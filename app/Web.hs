{-# LANGUAGE OverloadedStrings #-}

module Main where

-- App modules
import ProofToLaTeX (proofTableLaTeX, defaultRenderOpts)
import qualified LemmonChecker                   as LC
import           ProofTypes
import           PipeParse                       (parsePipeProof)
import           PrettyPrint                     (renderFormula)
import           FormulaParser                   (parseFormula)
import           ModelSemantics                  (Model, evalClosed)
import           Normalize                       (normalizeSyntax)
import           TruthTable                      (truthTable, buildTruthTableData)
import           TruthTable.LaTeX   (renderTruthTableLaTeX)
import           PropDNF                         (toDNF)
import OcrLatexToPipe (latexTableToPipe)
import qualified OcrLatexToPipe as OCR
import qualified Data.Text as TS


-- Web stack
import           Web.Scotty
import           Network.Wai                     (Request(..), RequestBodyLength(..))
import           Network.Wai.Middleware.Static   (staticPolicy, addBase)
import           Network.Wai.Middleware.RequestLogger (logStdoutDev)
import Network.HTTP.Types.Status (status200, status400, status401, status413, status429, status500, status502)
import           Network.HTTP.Simple         -- from http-conduit
import Text.Blaze.Html.Renderer.Utf8 (renderHtml)
import TruthTable.Html (truthTableHtml, truthTableHtmlMainOnly)
import TruthTable.Text (renderTruthTableText)
import TruthTable
  ( truthTable
  , buildTruthTableData
  , TruthTableData(..)
  , TTToken(..)
  )

-- Utils & JSON
import Control.Concurrent                  (threadDelay)
import Control.Concurrent.MVar             (MVar, newMVar, modifyMVar)
import Control.Exception                   (try, SomeException, displayException)
import qualified Network.HTTP.Client       as HC
import qualified GHC.IO.Encoding           as Enc
import Data.Time.Clock                     (UTCTime, getCurrentTime, diffUTCTime)
import Control.Monad.IO.Class (liftIO)
import Control.Applicative ((<|>))
import           System.Environment              (lookupEnv)
import           Text.Read                       (readMaybe)
import           Data.Aeson                      (Value(..), object, (.=))
import qualified Data.Aeson                     as A
import qualified Data.Aeson.Types               as AT  -- for parseEither
import qualified Data.Set                       as Set
import qualified Data.Map.Strict                as M
import qualified Data.Text.Lazy                 as TL
import qualified Data.Text.Lazy.Encoding        as TLE
import qualified Data.ByteString.Lazy           as BL
import qualified Data.ByteString.Char8       as BS
import qualified Data.Text        as T
import qualified Data.HashMap.Strict      as HM
import qualified Data.Vector              as V
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString.Lazy.Char8 as L8

-- truth tables 
import TruthTable.Style (TruthStyle(..))

--------------------------------------------------------------------------------
-- Limits 
--------------------------------------------------------------------------------

maxBodyBytes  :: Int
maxBodyBytes  = 128 * 1024      -- 128 KiB

maxProofLines :: Int
maxProofLines = 400

-- Shared with tools/transcribe.py, so the browser route and the evaluation
-- harness read photographs with one prompt rather than two that drift apart.
promptFile :: FilePath
promptFile = "prompts/transcribe.txt"

--------------------------------------------------------------------------------
-- Limits on the transcription route
--------------------------------------------------------------------------------
--
-- /transcribe is the only route that spends money: each call goes to a paid
-- API on our key. Everything else here is pure computation and needs no such
-- guard.
--
-- Three limits, because they fail in different ways.
--
--   * A size cap, so a single request cannot carry an enormous payload. The
--     browser downscales to 1568px, which is a few hundred kilobytes; anything
--     far larger did not come from our own page.
--
--   * A per-address hourly cap. This catches ordinary accidents — a stuck
--     retry loop, an impatient student reloading — and nothing more, since an
--     attacker can change address at will.
--
--   * A global daily cap. This is the only limit that bounds the bill against
--     someone who rotates addresses, and it is deliberately blunt. It can deny
--     service to real students, which is the trade being made: an exhausted
--     daily quota is recoverable by waiting, an exhausted account is not.

maxImageBytes :: Int
maxImageBytes = 8 * 1024 * 1024        -- generous next to a 1568px JPEG

perAddressPerHour :: Int
perAddressPerHour = 40                 -- a full problem set, comfortably

globalPerDay :: Int
globalPerDay = 500                     -- a class of thirty, several attempts each

data LimitState = LimitState
  { lsRecent :: M.Map String [UTCTime]  -- ^ recent calls, by client address
  , lsCount  :: Int                     -- ^ calls in the current day
  , lsStart  :: UTCTime                 -- ^ when the current day began
  }

newtype Limits = Limits (MVar LimitState)

newLimits :: IO Limits
newLimits = do
  now <- getCurrentTime
  Limits <$> newMVar (LimitState M.empty 0 now)

-- | Record a call and say whether it is allowed. Nothing means go ahead;
-- Just holds the message to show the caller.
--
-- The whole decision happens under one MVar so that concurrent requests cannot
-- both read a count below the limit and then both proceed.
admit :: Limits -> String -> IO (Maybe String)
admit (Limits var) addr = do
  now <- getCurrentTime
  modifyMVar var $ \st -> do
    -- Roll the daily window over if a day has passed.
    let (count, start)
          | diffUTCTime now (lsStart st) > 86400 = (0, now)
          | otherwise                            = (lsCount st, lsStart st)

        -- Drop calls older than an hour, for this address and for everyone,
        -- so the map cannot grow without bound.
        fresh ts  = [ t | t <- ts, diffUTCTime now t < 3600 ]
        pruned    = M.filter (not . null) (M.map fresh (lsRecent st))
        mine      = M.findWithDefault [] addr pruned

    if count >= globalPerDay
      then pure ( st { lsRecent = pruned, lsCount = count, lsStart = start }
                , Just "This service has reached its daily limit for reading \
                       \photographs. Please try again tomorrow, or type your \
                       \proof into the proof checker directly." )
      else if length mine >= perAddressPerHour
        then pure ( st { lsRecent = pruned, lsCount = count, lsStart = start }
                  , Just "Too many photographs from this connection in the last \
                         \hour. Please wait a little, or type your proof into \
                         \the proof checker directly." )
        else pure ( LimitState (M.insert addr (now : mine) pruned) (count + 1) start
                  , Nothing )

-- | Best guess at who is calling. Render sits behind a proxy, so the socket
-- address is the proxy's; X-Forwarded-For carries the original, with the
-- client first.
callerAddress :: ActionM String
callerAddress = do
  fwd <- header "x-forwarded-for"
  case fwd of
    Just t | not (TL.null t) -> pure (trimAddr (takeWhile (/= ',') (TL.unpack t)))
    _                        -> show . remoteHost <$> request
  where
    trimAddr = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- truth table auxiliaries

data TTMode = TTLaTeX | TTFull | TTMain | TTText
  deriving (Eq, Show)

parseMode :: String -> TTMode
parseMode m = case m of
  "latex" -> TTLaTeX
  "full"  -> TTFull
  "main"  -> TTMain
  "text"  -> TTText
  _       -> TTFull   -- default

parseTruthStyle :: String -> TruthStyle
parseTruthStyle s = case s of
  "tf"     -> StyleTF
  "bits"   -> StyleBits
  "topbot" -> StyleTopBot
  _        -> StyleTF   -- default

data PropTableReq = PropTableReq
  { ptrSentenceText :: String
  , ptrMode         :: TTMode
  , ptrTruthStyle   :: TruthStyle
  } deriving (Eq, Show)

instance A.FromJSON PropTableReq where
  parseJSON = A.withObject "PropTableReq" $ \o -> do
    s  <- o A..:  "sentenceText"
    m  <- parseMode <$> (o A..:? "mode" AT..!= "full")
    ts <- parseTruthStyle <$> (o A..:? "truthStyle" AT..!= "tf")
    pure (PropTableReq s m ts)


--------------------------------------------------------------------------------
-- JSON helpers for the line-by-line report
--------------------------------------------------------------------------------

lineReportToJSON :: LC.LineReport -> Value
lineReportToJSON r =
  let l        = LC.lrLine r
      depsList = Set.toList (references l)
      ok       = either (const False) (const True) (LC.lrNote r)
      msg      = either id (const "") (LC.lrNote r)
  in object
       [ "line"           .= lineNumber l
       , "deps"           .= depsList
       , "formulaPretty"  .= renderFormula (formula l)
       , "justification"  .= show (justification l)
       , "ok"             .= ok
       , "message"        .= msg
       ]

reportToJSON :: [LC.LineReport] -> Value
reportToJSON reps =
  object
    [ "valid" .= LC.proofValid reps
    , "lines" .= map lineReportToJSON reps
    ]

--------------------------------------------------------------------------------
-- Transcribing a photograph of a proof
--------------------------------------------------------------------------------

-- | Split "data:image/jpeg;base64,AAAA" into ("image/jpeg", "AAAA").
--
-- Text rather than String throughout. The payload is several hundred
-- kilobytes of base64; as a String that is a linked list of Char at roughly
-- twenty bytes each, traversed once per transformation. On a small instance
-- the cost is enough to stall the request while it is being written.
splitDataUrl :: T.Text -> Maybe (T.Text, T.Text)
splitDataUrl t = do
  rest <- T.stripPrefix "data:" t
  let (meta, enc) = T.breakOn "," rest
  payload <- if T.null enc then Nothing else Just (T.drop 1 enc)
  media   <- T.stripSuffix ";base64" meta
  pure (media, payload)

-- | Concatenate the text blocks of a Messages API response, ignoring any
-- thinking blocks.
responseText :: A.Value -> String
responseText v =
  case v of
    A.Object o ->
      case KM.lookup "content" o of
        Just (A.Array blocks) ->
          concat [ T.unpack t
                 | A.Object b <- V.toList blocks
                 , Just (A.String "text") <- [KM.lookup "type" b]
                 , Just (A.String t)      <- [KM.lookup "text" b]
                 ]
        _ -> ""
    _ -> ""

-- | Keep the pipe rows out of a model reply, discarding fences, commentary,
-- a header row, and the blank rows of the printed template. Mirrors
-- extract_pipe in tools/transcribe.py.
pipeRowsOf :: String -> String
pipeRowsOf reply = unlines (filter keep (map trimS (lines (dropFence reply))))
  where
    trimS = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse
    dropFence t = unlines [ l | l <- lines t, take 3 l /= "```" ]
    keep l =
      let cols = splitPipe l
      in length cols == 4
         && not (null (trimS (cols !! 2)))            -- blank template row
         && not (isHeaderRow cols)
    isHeaderRow cols =
      let low = map toLowerC (concat cols)
      in substr "depends" low && substr "justif" low
    toLowerC c = if c >= 'A' && c <= 'Z' then toEnum (fromEnum c + 32) else c
    substr needle hay = any (\i -> take (length needle) (drop i hay) == needle)
                            [0 .. length hay]

splitPipe :: String -> [String]
splitPipe s = case break (== '|') s of
  (a, [])     -> [a]
  (a, _:rest) -> a : splitPipe rest

-- | Things worth a second look before the student presses Check.
--
-- The heavy lifting is done by the parser itself, which already rejects
-- unknown rules and wrong reference counts, so this adds only the one check
-- the parser cannot make: an assumption whose Depends cell is empty. Every
-- dropped row in the evaluation corpus showed up that way. It is reported,
-- never repaired — if the cell really is blank the student has made a mistake
-- and the checker must be allowed to say so.
transcriptionNotices :: String -> [String]
transcriptionNotices pipe =
  [ "Line " ++ trimS (cols !! 1) ++ " is an assumption, but its dependency "
    ++ "cell came out empty. An assumption depends on its own line, so check "
    ++ "that against your photo."
  | l <- lines pipe
  , let cols = splitPipe l
  , length cols == 4
  , trimS (cols !! 3) == "A"
  , null (trimS (cols !! 0))
  ]
  where trimS = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse

-- | One call to the Messages API, returning the raw decoded response.
-- | Strip whitespace from a credential read out of the environment.
--
-- A key pasted into a dashboard field very easily carries a trailing newline
-- or space. HTTP header values may not contain a newline, so http-client
-- refuses to send the request at all, and the failure looks like a network
-- fault rather than a mistyped secret.
trimKey :: String -> String
trimKey = f . f where f = reverse . dropWhile (`elem` (" \t\r\n" :: String))

-- | Put a multi-line message on one line, so a truncated view of it still
-- carries the informative part.
flatten :: String -> String
flatten = take 400 . unwords . words

-- | Remove anything that looks like a credential.
--
-- http-client renders a failed request with every header included, so the
-- API key lands in the log verbatim unless it is stripped here. Logs are
-- readable by anyone with dashboard access and are retained; a key that
-- reaches them has to be treated as compromised.
redact :: String -> String
redact = go
  where
    go [] = []
    go xs@(c:rest)
      | take 7 xs == "sk-ant-" = "sk-ant-***REDACTED***" ++ go (dropWhile keyChar xs)
      | otherwise              = c : go rest
    keyChar ch = ch `elem` ("-_" :: String)
              || (ch >= 'a' && ch <= 'z')
              || (ch >= 'A' && ch <= 'Z')
              || (ch >= '0' && ch <= '9')

-- | The smallest possible real request to the Messages API: no image, a
-- handful of tokens. Returns the HTTP status, or the failure.
tinyAnthropicCall :: String -> IO (Either String Int)
tinyAnthropicCall rawKey = do
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (4 :: Int)
        , "messages"   .= [ A.object [ "role" .= ("user" :: String)
                                     , "content" .= ("hi" :: String) ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (60 * 1000000) }
  outcome <- try (httpLBS req)
  pure $ case outcome of
    Left e     -> Left (flatten (redact (displayException (e :: SomeException))))
    Right resp -> Right (getResponseStatusCode resp)

-- | Post a request of roughly the given size and report what came back.
--
-- The model name is deliberately invalid, so the API rejects the request
-- before it charges for anything -- but it can only reject what it has
-- received, so any HTTP status at all proves the bytes arrived. A connection
-- exception means they did not. That is the distinction we need, and this way
-- the sweep is free.
sizeProbe :: String -> Int -> IO (Int, String)
sizeProbe rawKey kb = do
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let filler  = T.replicate (kb * 1024) "x"
      payload = A.object
        [ "model"      .= ("probe-not-a-real-model" :: String)
        , "max_tokens" .= (1 :: Int)
        , "messages"   .= [ A.object [ "role" .= ("user" :: String)
                                     , "content" .= filler ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (60 * 1000000) }
  outcome <- try (httpLBS req)
  pure $ case outcome of
    Left e     -> (kb, "FAILED: " ++ take 90 (flatten (redact (displayException (e :: SomeException)))))
    Right resp -> (kb, "reached the API, HTTP " ++ show (getResponseStatusCode resp))

-- | A valid request that deliberately takes a while to answer.
--
-- The size probes use an invalid model, so the API rejects them at once and
-- the connection is never idle. A real transcription is silent for ten to
-- thirty seconds while the model reads the page. If a slow request fails
-- where a fast one of the same size succeeds, the problem is the idle period,
-- not the payload -- and the remedy is streaming, which keeps bytes moving.
slowProbe :: String -> IO String
slowProbe rawKey = do
  t0 <- getCurrentTime
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (2000 :: Int)
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .= ("Write out the numbers from 1 to 400, separated by \
                            \commas. Output nothing else." :: String) ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (180 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> "FAILED after " ++ secs ++ ": "
                  ++ take 90 (flatten (redact (displayException (e :: SomeException))))
    Right resp -> "succeeded after " ++ secs ++ ", HTTP "
                  ++ show (getResponseStatusCode resp)

-- | Large upload followed by a long wait: the one combination the other
-- probes leave untested, and the only one that matches the real request.
--
-- The size probes are rejected instantly, so their connections never go
-- quiet. The slow probe is tiny. A middlebox that drops a connection which
-- falls silent after a substantial transfer would pass both and fail this.
combinedProbe :: String -> Int -> IO String
combinedProbe rawKey kb = do
  t0 <- getCurrentTime
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let filler  = T.replicate (kb * 1024) "x"
      payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (1500 :: Int)
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .= (T.concat
                [ "Ignore the following padding entirely: ", filler
                , "\n\nNow write out the numbers from 1 to 900, separated by \
                  \commas. Output nothing else." ]) ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (180 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> show kb ++ " KB, FAILED after " ++ secs ++ ": "
                  ++ take 80 (flatten (redact (displayException (e :: SomeException))))
    Right resp -> show kb ++ " KB, succeeded after " ++ secs ++ ", HTTP "
                  ++ show (getResponseStatusCode resp)

-- | An 8x8 white JPEG. Small enough to embed, real enough for the API to
-- accept as an image.
tinyJpegB64 :: T.Text
tinyJpegB64 = "/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAA0JCgsKCA0LCgsODg0PEyAVExISEyccHhcgLikxMC4pLSwzOko+MzZGNywtQFdBRkxOUlNSMj5aYVpQYEpRUk//2wBDAQ4ODhMREyYVFSZPNS01T09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT09PT0//wAARCAAIAAgDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwD06iiigD//2Q=="

-- | The last untested difference: an image content block.
--
-- Every probe that succeeds sends plain text. The request that fails sends a
-- content array with an image in it. This sends a real image plus padding, in
-- exactly the shape /transcribe uses, so the only thing varying from a passing
-- probe is the presence of the image block.
imageProbe :: String -> Int -> IO String
imageProbe rawKey kb = do
  t0 <- getCurrentTime
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let padding = T.replicate (kb * 1024) "x"
      payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (600 :: Int)
        , "stream"     .= True
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .=
                [ A.object
                    [ "type"   .= ("image" :: String)
                    , "source" .= A.object
                        [ "type"       .= ("base64" :: String)
                        , "media_type" .= ("image/jpeg" :: String)
                        , "data"       .= tinyJpegB64
                        ]
                    ]
                , A.object
                    [ "type" .= ("text" :: String)
                    , "text" .= T.concat
                        [ "Ignore this padding: ", padding
                        , "\n\nWrite the numbers 1 to 300, comma separated." ]
                    ]
                ] ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (180 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> "image + " ++ show kb ++ " KB, FAILED after " ++ secs ++ ": "
                  ++ take 70 (flatten (redact (displayException (e :: SomeException))))
    Right resp -> "image + " ++ show kb ++ " KB, succeeded after " ++ secs
                  ++ ", HTTP " ++ show (getResponseStatusCode resp)

-- | How long the connection may stay silent before the first byte arrives.
--
-- This is the only variable that separates every passing probe from every
-- failing request. The real transcription posts 211 KB -- less than probes
-- that pass -- so size is not the cause. What it does instead is go quiet for
-- fifteen to thirty seconds while the model reads a dense page. The longest
-- silence this host has been shown to survive is seventeen seconds
-- (combinedProbe at 400 KB), and the failures begin right about there.
--
-- It also explains why streaming did not help. Streaming keeps bytes moving
-- only once the first token exists; with a real photograph the silence falls
-- before that, while the image is being read.
--
-- Non-streaming on purpose: the point is to hold the connection quiet for a
-- known length of time. Roughly fifty numbers a second, measured from the
-- probes above, so the count sets the duration.
silenceProbe :: String -> Int -> IO String
silenceProbe rawKey n = do
  t0 <- getCurrentTime
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
          -- 8000 to match the real request, which is also untested at this size
        , "max_tokens" .= (8000 :: Int)
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .= ("Write out the numbers from 1 to " ++ show n
                            ++ ", separated by commas. Output nothing else.") ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (300 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> "asked for " ++ show n ++ ", FAILED after " ++ secs ++ " -- "
                  ++ take 70 (flatten (redact (displayException (e :: SomeException))))
    Right resp -> "asked for " ++ show n ++ ", survived " ++ secs ++ " of silence, HTTP "
                  ++ show (getResponseStatusCode resp)

-- | The reproduction as a standalone route, in both streaming modes.
runRealProbe :: Bool -> String -> ActionM ()
runRealProbe doStream size = do
  mKey <- liftAndCatchIO $ lookupEnv "ANTHROPIC_API_KEY"
  case mKey of
    Nothing -> json $ object
      [ "status" .= ("no_key" :: String)
      , "error"  .= ("ANTHROPIC_API_KEY is not set." :: String) ]
    Just k -> do
      r <- liftAndCatchIO $ realImageProbe k doStream size
      json $ object [ "status" .= ("done" :: String), "result" .= r ]

-- | The two-by-two the evidence actually points at.
--
-- Every probe that passes uses a short hardcoded ASCII prompt. Every probe
-- that fails reads prompts/transcribe.txt, which is UTF-8 and carries the
-- logical symbols. That correlation is exact across everything measured so
-- far, and it has never been varied deliberately -- the image was varied
-- instead, four times, and made no difference at all (41 KB fails exactly as
-- 244 KB does, both at fifteen seconds).
--
-- The ASCII arm keeps the prompt's length and structure and replaces only the
-- characters above 127, so the sole difference between the two arms is whether
-- non-ASCII text goes out in the body.
matrixProbe :: String -> Bool -> Bool -> IO String
matrixProbe rawKey bigImage rawPrompt = do
  t0      <- getCurrentTime
  prompt0 <- readFile promptFile
  b64     <- if bigImage
               then T.pack . filter (\c -> c /= '\n' && c /= '\r')
                      <$> readFile "static/probe-md.b64"
               else pure tinyJpegB64
  let prompt = if rawPrompt
                 then prompt0
                 else map (\c -> if c > '\DEL' then '?' else c) prompt0
      label  = (if bigImage then "125 KB image" else "8x8 image")
               ++ " + " ++ (if rawPrompt then "prompt as-is" else "prompt ASCII-only")
               ++ ": "
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (8000 :: Int)
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .=
                [ A.object
                    [ "type"   .= ("image" :: String)
                    , "source" .= A.object
                        [ "type"       .= ("base64" :: String)
                        , "media_type" .= ("image/jpeg" :: String)
                        , "data"       .= b64 ] ]
                , A.object [ "type" .= ("text" :: String), "text" .= prompt ]
                ] ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (90 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> label ++ "FAILED after " ++ secs ++ " -- "
                  ++ briefly (flatten (redact (displayException (e :: SomeException))))
    Right resp -> label ++ "succeeded after " ++ secs ++ ", HTTP "
                  ++ show (getResponseStatusCode resp)

-- | A faithful reproduction of the request that fails.
--
-- Every passing probe so far sits in one of two boxes: long but with no real
-- image (bySilence, 47 seconds), or a real image but answered quickly
-- (imageProbe, 12 seconds, an 8x8 JPEG). The failing request is the cell
-- neither covers -- a genuine photograph and a long wait together.
--
-- static/probe-{xs,sm,md,lg}.b64 are one real page from the evaluation corpus
-- at four resolutions -- 41, 68, 125 and 244 KB of base64 -- stored already
-- encoded so this needs no encoder dependency. lg matches what the browser
-- currently produces. The prompt is the real one, so the model does
-- the real work and takes the real amount of time.
--
-- The streaming flag matters because that combination is untested too: the
-- long probes that pass are all non-streaming, and the streaming probes that
-- pass are all short.
realImageProbe :: String -> Bool -> String -> IO String
realImageProbe rawKey doStream size = do
  t0 <- getCurrentTime
  rawB64 <- readFile ("static/probe-" ++ size ++ ".b64")
  prompt <- readFile promptFile
  let b64 = T.pack (filter (\c -> c /= '\n' && c /= '\r') rawB64)
      label = (if doStream then "streaming" else "non-streaming")
              ++ ", " ++ show (T.length b64 `div` 1024) ++ " KB b64: "
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (8000 :: Int)
        , "stream"     .= doStream
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .=
                [ A.object
                    [ "type"   .= ("image" :: String)
                    , "source" .= A.object
                        [ "type"       .= ("base64" :: String)
                        , "media_type" .= ("image/jpeg" :: String)
                        , "data"       .= b64
                        ]
                    ]
                , A.object [ "type" .= ("text" :: String), "text" .= prompt ]
                ] ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          -- 90 rather than the 180 the real call uses. A success takes about
          -- twenty-five seconds and the observed failure about ten, so nothing
          -- useful happens after ninety, and waiting three minutes per probe
          -- makes this too slow to iterate on.
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (90 * 1000000) }
  stage ("realprobe: " ++ label ++ "posting")
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  stage ("realprobe: finished in " ++ secs)
  pure $ case outcome of
    Left e     -> label ++ "FAILED after " ++ secs ++ " -- "
                  ++ briefly (flatten (redact (displayException (e :: SomeException))))
    Right resp -> label ++ "succeeded after " ++ secs ++ ", HTTP "
                  ++ show (getResponseStatusCode resp) ++ ", "
                  ++ show (BL.length (getResponseBody resp) `div` 1024) ++ " KB back"

-- | Kept for completeness, though 211 KB in the real request rules size out.
--
-- imageProbe pads the *text* block and leaves an 8x8 JPEG in the image, so the
-- largest image this host has been shown to send is about five hundred bytes.
-- A real photograph is one to three megabytes of base64 sitting in that field.
--
-- The padding is valid base64 but not a valid JPEG, so the API answers HTTP
-- 400. That is a pass, not a failure: it can only reject the image after it
-- has received the whole body, so a 400 proves the bytes arrived. The result
-- worth having here is a transport exception.
bigImageProbe :: String -> Int -> IO String
bigImageProbe rawKey kb = do
  t0 <- getCurrentTime
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let fat = T.append tinyJpegB64 (T.replicate (kb * 1024) "A")
      payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (16 :: Int)
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .=
                [ A.object
                    [ "type"   .= ("image" :: String)
                    , "source" .= A.object
                        [ "type"       .= ("base64" :: String)
                        , "media_type" .= ("image/jpeg" :: String)
                        , "data"       .= fat
                        ]
                    ]
                , A.object
                    [ "type" .= ("text" :: String)
                    , "text" .= ("Describe this image." :: String) ]
                ] ] ]
        ]
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack (trimKey rawKey)]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ initReq { HC.responseTimeout = HC.responseTimeoutMicro (180 * 1000000) }
  outcome <- try (httpLBS req)
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int) ++ "s"
  pure $ case outcome of
    Left e     -> show kb ++ " KB image: TRANSPORT FAILURE after " ++ secs ++ ": "
                  ++ take 70 (flatten (redact (displayException (e :: SomeException))))
    Right resp -> show kb ++ " KB image: body delivered in " ++ secs
                  ++ ", HTTP " ++ show (getResponseStatusCode resp)
                  ++ " (400 expected -- the padding is not a JPEG)"

-- | Run an action, retrying a failure a few times with a short pause.
retrying :: Int -> IO (Either SomeException a) -> IO (Either SomeException a)
retrying n act = do
  -- Time each attempt separately. The handler reports only the last failure,
  -- so a 31 second total could be one slow attempt or three quick ones, and
  -- those point at quite different causes.
  t0 <- getCurrentTime
  r  <- act
  t1 <- getCurrentTime
  let secs = show (round (realToFrac (diffUTCTime t1 t0) :: Double) :: Int)
  case r of
    Right _              -> pure r
    Left _ | n <= 1      -> stage ("attempt failed after " ++ secs ++ "s, giving up")
                            >> pure r
           | otherwise   -> stage ("attempt failed after " ++ secs ++ "s, retrying")
                            >> threadDelay 1000000 >> retrying (n - 1) act

-- | Assemble the reply from a stream of server-sent events.
--
-- Streaming is not for progressive display here -- we still wait for the whole
-- reply. It is to keep bytes moving. A non-streamed request sits silent for
-- twenty-odd seconds while the model reads the page, and something between
-- this host and the API closes connections that go quiet for that long. With
-- streaming, deltas arrive continuously and the connection is never idle.
assembleSSE :: L8.ByteString -> String
assembleSSE body =
  concat [ T.unpack t
         | line <- L8.lines body
         , L8.isPrefixOf "data: " line
         , Just v <- [A.decode (L8.drop 6 line) :: Maybe A.Value]
         , Just t <- [deltaText v]
         ]
  where
    deltaText (A.Object o)
      | Just (A.String "content_block_delta") <- KM.lookup "type" o
      , Just (A.Object d) <- KM.lookup "delta" o
      , Just (A.String t) <- KM.lookup "text" d
      = Just t
    deltaText _ = Nothing

-- | A timestamped progress line.
--
-- Every probe on the outbound leg now passes, so the fault is either in the
-- inbound POST or in this handler after the API answers -- and there is no way
-- to tell which from the outside. This makes the log say where it stopped
-- rather than leaving it to be inferred.
-- | The informative end of an http-client exception.
--
-- displayException on an HttpExceptionRequest renders the whole Request record
-- first and names the actual fault last, so taking a prefix -- which is what
-- these probes were doing -- keeps the boilerplate and discards the answer.
-- ResponseTimeout and NoResponseDataReceived are quite different failures and
-- the distinction was being truncated away.
briefly :: String -> String
briefly e
  | length e <= 220 = e
  | otherwise       = take 70 e ++ " ... " ++ reverse (take 140 (reverse e))

-- | What the container thinks the prompt file says.
--
-- readFile decodes using the locale encoding. macOS sets a UTF-8 locale;
-- debian:bullseye-slim sets none, so GHC falls back to ASCII -- and
-- prompts/transcribe.txt is UTF-8 containing the logical symbols. If the
-- decode is wrong the character count rises (each three-byte symbol becoming
-- three characters) and the highest code point drops to 255. Comparing this
-- line against the same route run locally settles it without argument.
promptDiag :: IO String
promptDiag = do
  enc <- try Enc.getLocaleEncoding
  r   <- try (do p <- readFile promptFile
                 -- force it: readFile is lazy, so a decode error surfaces here
                 -- rather than later inside the request body
                 let n  = length p
                     hi = maximum (0 : map fromEnum p)
                     na = length (filter (> '\DEL') p)
                 n `seq` hi `seq` pure (n, hi, na))
  let encS = case enc of
               Left e        -> "locale ?? (" ++ take 40 (show (e :: SomeException)) ++ ")"
               Right x       -> "locale " ++ show x
  pure $ encS ++ ", " ++ case r of
    Left e            -> "readFile FAILED: "
                         ++ take 120 (flatten (show (e :: SomeException)))
    Right (n, hi, na) -> show n ++ " chars, " ++ show na
                         ++ " non-ASCII, max code point " ++ show hi
                         ++ (if hi > 255 then " (decoded as UTF-8, correct)"
                                         else " (NOT UTF-8 -- symbols are mangled)")

stage :: String -> IO ()
stage msg = do
  t <- getCurrentTime
  putStrLn ("[transcribe] " ++ takeWhile (/= '.') (drop 11 (show t)) ++ " " ++ msg)

callAnthropic :: String -> T.Text -> T.Text -> String -> IO (Either String String)
callAnthropic rawKey media b64 promptText = do
  let apiKey = trimKey rawKey
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (8000 :: Int)
        , "stream"     .= True
          -- Transcription is perception, not reasoning. Left enabled, thinking
          -- can consume the whole budget on a dense page and emit no text.
        , "thinking"   .= A.object [ "type" .= ("disabled" :: String) ]
        , "messages"   .= [ A.object
            [ "role"    .= ("user" :: String)
            , "content" .=
                [ A.object
                    [ "type"   .= ("image" :: String)
                    , "source" .= A.object
                        [ "type"       .= ("base64" :: String)
                        , "media_type" .= media
                        , "data"       .= b64
                        ]
                    ]
                , A.object [ "type" .= ("text" :: String), "text" .= promptText ]
                ]
            ] ]
        ]
      -- http-client defaults to a 30 second response timeout. Reading a dense
      -- page takes longer than that often enough to matter, and the failure
      -- looks like a server fault rather than a slow one, so allow plenty.
      timedOut = initReq { HC.responseTimeout = HC.responseTimeoutMicro (180 * 1000000) }
      req = setRequestBodyLBS (A.encode payload)
          $ setRequestHeader "content-type"      ["application/json"]
          $ setRequestHeader "x-api-key"         [BS.pack apiKey]
          $ setRequestHeader "anthropic-version" ["2023-06-01"]
          $ timedOut
  -- Catch rather than let the exception escape as an unhandled 500: a network
  -- failure reaching the API is not an internal error, and the caller needs to
  -- be told which it was.
  -- NoResponseDataReceived and friends are transient: a pooled connection the
  -- far end had already closed, or a connection dropped in flight. One retry
  -- on a fresh connection clears the common case, and costs a second when it
  -- does not.
  putStrLn ("[transcribe] posting " ++ show (T.length b64 * 3 `div` 4 `div` 1024)
            ++ " KB image to api.anthropic.com")
  outcome <- retrying 2 (try (httpLBS req))
  case outcome of
    Left e -> do
      let msg = redact (displayException (e :: SomeException))
      putStrLn ("[transcribe] request to api.anthropic.com failed: " ++ msg)
      -- The exception renders over several lines; collapse them rather than
      -- truncating at the first newline, which leaves only "Request {".
      pure (Left ("Could not reach the transcription service. " ++ flatten msg))
    Right resp -> do
      let code = getResponseStatusCode resp
          bodyL = getResponseBody resp
      if code < 200 || code >= 300
        then do
          putStrLn ("[transcribe] api.anthropic.com returned " ++ show code
                    ++ ": " ++ take 400 (L8.unpack bodyL))
          pure (Left ("The transcription service returned HTTP " ++ show code
                      ++ ". " ++ take 200 (L8.unpack bodyL)))
        else pure (Right (assembleSSE bodyL))

collectTexts :: A.Value -> [T.Text]
collectTexts (A.Object o) =
  let direct = case KM.lookup "text" o of
                 Just (A.String s) -> [s]
                 _                 -> []
  in direct ++ concatMap collectTexts (KM.elems o)
collectTexts (A.Array arr)  = concatMap collectTexts (V.toList arr)
collectTexts (A.String s)   = [s]
collectTexts _              = []

--------------------------------------------------------------------------------
-- Model checker request type (JSON)
--------------------------------------------------------------------------------

-- We accept: { "model": { ..Model.. }, "sentenceText": "∀x(…)" }
data ModelCheckReq = ModelCheckReq
  { mcModel       :: Model
  , mcSentenceTxt :: String
  }

instance A.FromJSON ModelCheckReq where
  parseJSON = A.withObject "ModelCheckReq" $ \o ->
    ModelCheckReq <$> o A..: "model"
                  <*> o A..: "sentenceText"

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  -- Do not inherit the locale. readFile and putStrLn decode and encode with
  -- whatever the environment says, and the deployment container sets nothing,
  -- so GHC falls back to ASCII -- while a Mac supplies UTF-8. The prompt file
  -- is UTF-8 and carries the logical symbols, so the same code reads a
  -- different prompt in the two places. Fixing it here rather than only in the
  -- Dockerfile means it holds wherever this runs.
  inherited <- Enc.getLocaleEncoding
  Enc.setLocaleEncoding Enc.utf8
  Enc.setFileSystemEncoding Enc.utf8
  Enc.setForeignEncoding Enc.utf8
  putStrLn ("[startup] inherited locale encoding: " ++ show inherited
            ++ " (now forced to UTF-8)")
  before <- promptDiag
  putStrLn ("[startup] prompt file: " ++ before)

  -- Respect $PORT in prod (platform sets it). Default to 8080 locally.
  mPort   <- lookupEnv "PORT"
  let port = maybe 8080 id (mPort >>= readMaybe)

  -- One limiter for the whole process, shared by every request.
  limits <- newLimits

  scotty port $ do
    -- Simple request logging
    middleware logStdoutDev

    -- Serve /static/* from ./static and allow root to read from it too
    middleware $ staticPolicy (addBase "static")

    -- Liveness probe
    get "/health" $ status status200 >> text "ok"

    -- Landing page (proof checker)
    get "/" $ file "static/index.html"

    get "/proof" $ file "static/proof.html"

    -- Instructions page
    get "/instructions" $ file "static/instructions.html"

    -- Model builder page
    get "/model" $ file "static/model.html"

    get "/graph" $ file "static/graph.html"

    -- Truth table page
    get "/prop" $ file "static/prop.html"

    -- Proof checking endpoint
    post "/check" $ do
      req <- request
      case requestBodyLength req of
        KnownLength n | n > fromIntegral maxBodyBytes -> do
          status status413
          json $ object
            [ "status" .= ("too_large" :: String)
            , "error"  .= ("Request body exceeds limit (" ++ show maxBodyBytes ++ " bytes)" :: String)
            ]
          finish
        _ -> pure ()

  -- accept form field or raw body
      mProof <- rescue (Just <$> param "proof") (const (pure Nothing))
      raw    <- body
      let inputTxt =
            case mProof of
              Just t | not (TL.null t) -> TL.unpack t
              _                        -> TL.unpack (TLE.decodeUtf8 (raw :: BL.ByteString))

      let lsCount = length (lines inputTxt)
      if lsCount > maxProofLines
        then do
          status status400
          json $ object
            [ "status" .= ("too_many_lines" :: String)
            , "error"  .= ("Proof has " ++ show lsCount ++
                           " lines; limit is " ++ show maxProofLines :: String)
            ]
        else
          case parsePipeProof inputTxt of
            Left perr -> do
              status status400
              json $ object
                [ "status" .= ("parse_error" :: String)
                , "error"  .= perr
                ]
            Right proof -> do
              let reps  = LC.checkProof proof
                  ok    = LC.proofValid reps
                  
                  latex = if ok then Just (proofTableLaTeX defaultRenderOpts proof) else (Nothing :: Maybe String)
              json $ object
                [ "status" .= ("ok" :: String)
                , "report" .= reportToJSON reps
                , "valid"  .= ok
                , "latex"  .= latex   -- present only when valid
                ]


    -- Model checking endpoint (JSON)
    post "/model/check" $ do
      raw <- body
      case A.eitherDecode' raw of
        Left e -> do
          status status400
          json $ object
            [ "status" .= ("bad_json" :: String)
            , "error"  .= e
            ]
        Right (ModelCheckReq m sTxt) ->
          -- normalize ASCII shorthands before parsing
          let sNorm = normalizeSyntax sTxt in
          case parseFormula sNorm of
            Left perr -> do
              status status400
              json $ object
                [ "status" .= ("parse_error" :: String)
                , "error"  .= perr
                ]
            Right phi ->
              case evalClosed m phi of
                Left evalErr ->
                  json $ object
                    [ "status" .= ("eval_error" :: String)
                    , "error"  .= evalErr
                    ]
                Right truth ->
                  json $ object
                    [ "status" .= ("ok" :: String)
                    , "value"  .= truth
                    ]

    -- Propositional truth table endpoint (JSON)
    post "/prop/table" $ do
      raw <- body
      case A.eitherDecode' raw of
        Left e -> do
          status status400
          json $ object
            [ "status" .= ("bad_json" :: String)
            , "error"  .= e
            ]

        Right (PropTableReq sTxt mode tstyle) -> do
          let sNorm = normalizeSyntax sTxt
          liftIO $ putStrLn $
            "/prop/table mode=" ++ show mode
            ++ " truthStyle=" ++ show tstyle
            ++ " sentenceText=" ++ take 80 sTxt

          case parseFormula sNorm of
            Left perr -> do
              status status400
              json $ object
                [ "status" .= ("parse_error" :: String)
                , "error"  .= perr
                ]

            Right phi -> do
              -- keep your propositional check (as before)
              case truthTable phi of
                Left err -> do
                  status status400
                  json $ object
                    [ "status" .= ("non_propositional" :: String)
                    , "error"  .= err
                    ]

                Right _rows -> do
                  let phiStr = renderFormula phi

                  -- build TruthTableData once
                  case buildTruthTableData phi of
                    Left err -> do
                      status status400
                      json $ object
                        [ "status" .= ("non_propositional" :: String)
                        , "error"  .= err
                        ]

                    Right tt -> do
                      case mode of
                        TTLaTeX -> do
                          let latex = renderTruthTableLaTeX tstyle tt
                          json $ object
                            [ "status" .= ("ok" :: String)
                            , "format" .= ("latex" :: String)
                            , "mode"   .= ("latex" :: String)
                            , "truthStyle" .= show tstyle
                            , "header" .= phiStr
                            , "latex"  .= latex
                            ]

                        TTFull -> do
                          let htmlText = TLE.decodeUtf8 (renderHtml (truthTableHtml tstyle tt))
                          json $ object
                            [ "status" .= ("ok" :: String)
                            , "format" .= ("html" :: String)
                            , "mode"   .= ("full" :: String)
                            , "truthStyle" .= show tstyle
                            , "header" .= phiStr
                            , "html"   .= htmlText
                            ]

                        TTMain -> do
                          let htmlTable = TLE.decodeUtf8 (renderHtml (truthTableHtmlMainOnly tstyle tt))
                          json $ object
                            [ "status" .= ("ok" :: String)
                            , "format" .= ("html" :: String)
                            , "mode"   .= ("main" :: String)
                            , "truthStyle" .= show tstyle
                            , "header" .= phiStr
                            , "html"   .= htmlTable
                            ]

                        TTText -> do
                          let txt = renderTruthTableText tstyle tt
                          json $ object
                            [ "status" .= ("ok" :: String)
                            , "format" .= ("text" :: String)
                            , "mode"   .= ("text" :: String)
                            , "truthStyle" .= show tstyle
                            , "header" .= phiStr
                            , "text"   .= txt
                            ]
  


      -- DNF page
    get "/prop/dnf" $ file "static/prop-dnf.html"

    --   DNF conversion endpoint
    post "/prop/dnf" $ do
      raw <- body
      case A.eitherDecode' raw of
        Left e -> do
          status status400
          json $ object
            [ "status" .= ("bad_json" :: String)
            , "error"  .= e
            ]
        Right (Object v) ->
          case AT.parseEither (\obj -> obj A..: "sentenceText") v of
            Left perr -> do
              status status400
              json $ object
                [ "status" .= ("parse_error" :: String)
                , "error"  .= perr
                ]
            Right sTxt ->
              let sNorm = normalizeSyntax sTxt in
                case parseFormula sNorm of
                  Left perr -> do
                    status status400
                    json $ object
                      [ "status" .= ("parse_error" :: String)
                      , "error"  .= perr
                      ]
                  Right phi ->
                    case toDNF phi of       
                      Left err -> do
                        status status400
                        json $ object
                          [ "status" .= ("dnf_error" :: String)
                          , "error"  .= err
                          ]
                      Right dnf ->
                        json $ object
                          [ "status" .= ("ok" :: String)
                          , "dnf"    .= renderFormula dnf ]
        _ -> do
          status status400
          json $ object
            [ "status" .= ("bad_request" :: String)
            , "error"  .= ("Expected {sentenceText: ...}" :: String)
            ]

    -- The blank proof template, for printing. Served explicitly rather than
    -- left to the static middleware so that the URL is memorable and the
    -- headers are right: browsers need the content type to preview a PDF
    -- rather than download it as an unknown blob.
    get "/template" $ do
      setHeader "Content-Type" "application/pdf"
      setHeader "Content-Disposition" "inline; filename=\"proof-template.pdf\""
      file "static/template.pdf"

    -- Does this server reach the Anthropic API at all?
    --
    -- The transcription request carries several hundred kilobytes of image.
    -- If a tiny request to the same endpoint succeeds while the real one
    -- fails, the connection is fine and the payload size is the problem --
    -- a path-MTU or egress limit rather than anything in this code. If both
    -- fail, the host cannot reach the API and the size is irrelevant. There
    -- is no way to tell those apart from the outside, hence this route.
    get "/transcribe/selftest" $ do
      mKey <- liftAndCatchIO $ lookupEnv "ANTHROPIC_API_KEY"
      case mKey of
        Nothing -> json $ object
          [ "status" .= ("no_key" :: String)
          , "error"  .= ("ANTHROPIC_API_KEY is not set." :: String) ]
        Just k -> do
          r      <- liftAndCatchIO $ tinyAnthropicCall k
          probes <- liftAndCatchIO $ mapM (sizeProbe k) [16, 64, 128, 256, 512]
          slow   <- liftAndCatchIO $ slowProbe k
          comb   <- liftAndCatchIO $ mapM (combinedProbe k) [128, 400]
          imgs   <- liftAndCatchIO $ mapM (imageProbe k) [0, 400, 600]
          big    <- liftAndCatchIO $ mapM (bigImageProbe k) [1024, 4096]
          quiet  <- liftAndCatchIO $ mapM (silenceProbe k) [900, 1500, 2200, 3000]
          real   <- liftAndCatchIO $
                      mapM (realImageProbe k False) ["xs", "sm", "md", "lg"]
          json $ object
            [ "status"  .= (either (const "failed") (const "ok") r :: String)
            , "tiny"    .= either id (\c -> "HTTP " ++ show c) r
            , "bySize"  .= [ object [ "kb" .= kb, "result" .= res ]
                           | (kb, res) <- probes ]
            , "slowRequest"     .= slow
            , "largeAndSlow"    .= comb
            , "withImageBlock"  .= imgs
            , "byImageSize"     .= big
            , "bySilence"       .= quiet
            , "realRequest"     .= real
            , "note2"   .= ("realRequest is now the one that matters: a real \
                            \photograph from the corpus, the real prompt, \
                            \max_tokens 8000, run both non-streaming and \
                            \streaming. It is the request that fails, minus the \
                            \browser. If it fails here the reproduction is in \
                            \hand and can go to Render support as a GET anyone \
                            \can run. If it succeeds, the fault is not in the \
                            \call at all but in the inbound POST or in this \
                            \handler, and /transcribe/echo separates those." :: String)
            , "note"    .= ("bySilence is the one that matters. The real \
                            \request posts 211 KB -- smaller than probes that \
                            \pass -- so size is not the cause. What it does is \
                            \go quiet for fifteen to thirty seconds while the \
                            \model reads the page. The longest silence proven \
                            \here is seventeen seconds. These four hold the \
                            \connection quiet for roughly 17, 30, 45 and 60 \
                            \seconds. If the failures start partway down that \
                            \ladder, the ceiling is an idle timeout on the way \
                            \out of this host, and no amount of streaming will \
                            \help because the silence falls before the first \
                            \token exists." :: String)
            ]

    -- The reproduction on its own, so it can be run in thirty seconds rather
    -- than behind two and a half minutes of probes that have already told us
    -- what they have to tell.
    --
    --   /transcribe/realprobe         non-streaming, as the code was originally
    --   /transcribe/realprobe/stream  streaming, as the code is now
    get "/transcribe/realprobe"        $ runRealProbe False "lg"
    get "/transcribe/realprobe/stream" $ runRealProbe True  "lg"
    -- The ladder, one rung at a time: 41, 68, 125 and 244 KB of base64, the
    -- same page photographed at four resolutions. If the small ones survive
    -- and the large ones do not, downscaling harder in photo.html is a fix we
    -- can ship today rather than waiting on Render.
    -- The 2x2: image big/small crossed with prompt raw/ASCII-only, plus what
    -- the container thinks the prompt file says.
    get "/transcribe/matrix" $ do
      diag <- liftAndCatchIO promptDiag
      mKey <- liftAndCatchIO $ lookupEnv "ANTHROPIC_API_KEY"
      case mKey of
        Nothing -> json $ object [ "prompt" .= diag, "error" .= ("no key" :: String) ]
        Just k  -> do
          rs <- liftAndCatchIO $ sequence
                  [ matrixProbe k big raw | big <- [False, True], raw <- [False, True] ]
          json $ object [ "prompt" .= diag, "matrix" .= rs ]

    get "/transcribe/realprobe/xs" $ runRealProbe False "xs"
    get "/transcribe/realprobe/sm" $ runRealProbe False "sm"
    get "/transcribe/realprobe/md" $ runRealProbe False "md"

    -- The selftest is a GET, so it exercises none of the inbound path: no
    -- large POST body, no proxy buffering it, no JSON decode of a quarter
    -- megabyte. This does exactly that much and nothing else, so a failure
    -- here locates the fault before the API is ever involved.
    --
    --   curl -s -X POST --data-binary @big.json <host>/transcribe/echo
    post "/transcribe/echo" $ do
      raw <- body
      liftAndCatchIO $ stage ("echo: " ++ show (BL.length raw) ++ " bytes")
      json $ object
        [ "status" .= ("ok" :: String)
        , "bytes"  .= BL.length raw
        , "parses" .= (case A.eitherDecode' raw :: Either String A.Value of
                         Left e  -> "no: " ++ take 120 e
                         Right _ -> "yes") ]

    -- Photograph a proof, confirm the transcription, then check it
    get "/photo" $ file "static/photo.html"

    post "/transcribe" $ do
      -- Refuse an oversized body before reading it. The browser sends a
      -- downscaled image; anything much larger did not come from our page.
      req0 <- request
      case requestBodyLength req0 of
        KnownLength n | n > fromIntegral maxImageBytes -> do
          status status413
          json $ object
            [ "status" .= ("too_large" :: String)
            , "error"  .= ("That image is too large. Photograph the page \
                           \rather than scanning it at high resolution." :: String) ]
          finish
        _ -> pure ()

      addr    <- callerAddress
      refused <- liftAndCatchIO (admit limits addr)
      case refused of
        Just msg -> do
          status status429
          json $ object [ "status" .= ("rate_limited" :: String), "error" .= msg ]
          finish
        Nothing -> pure ()

      raw <- body
      liftAndCatchIO $ stage ("inbound body read, "
                              ++ show (BL.length raw `div` 1024) ++ " KB")
      if BL.length raw > fromIntegral maxImageBytes
        then do
          status status413
          json $ object
            [ "status" .= ("too_large" :: String)
            , "error"  .= ("That image is too large." :: String) ]
        else case A.eitherDecode' raw of
        Left e -> do
          status status400
          json $ object [ "status" .= ("bad_json" :: String), "error" .= e ]
        Right (A.Object o) ->
          case AT.parseEither (AT..: "dataUrl") o of
            Left perr -> do
              status status400
              json $ object [ "status" .= ("bad_json" :: String), "error" .= perr ]
            Right dataUrl ->
              case splitDataUrl (dataUrl :: T.Text) of
                Nothing -> do
                  status status400
                  json $ object
                    [ "status" .= ("bad_image" :: String)
                    , "error"  .= ("Expected a base64 data URL for the photo." :: String) ]
                Just (media, b64) -> do
                  mKey <- liftAndCatchIO $ lookupEnv "ANTHROPIC_API_KEY"
                  case mKey of
                    Nothing -> do
                      status status500
                      json $ object
                        [ "status" .= ("server_not_configured" :: String)
                        , "error"  .= ("Set ANTHROPIC_API_KEY on the server." :: String) ]
                    Just apiKey | null (trimKey apiKey) -> do
                      status status500
                      json $ object
                        [ "status" .= ("server_not_configured" :: String)
                        , "error"  .= ("ANTHROPIC_API_KEY is set but empty." :: String) ]
                    Just apiKey -> do
                      promptText <- liftAndCatchIO $ readFile promptFile
                      liftAndCatchIO $ stage ("prompt read, " ++ show (length promptText)
                                              ++ " chars; image b64 "
                                              ++ show (T.length b64 `div` 1024) ++ " KB")
                      first <- liftAndCatchIO $ callAnthropic apiKey media b64 promptText
                      liftAndCatchIO $ stage $ case first of
                        Left e  -> "API call FAILED: "
                                   ++ take 200 (flatten (redact e))
                        Right s -> "API returned " ++ show (length s) ++ " chars"
                      case first of
                        Left decErr -> do
                          status status500
                          json $ object
                            [ "status" .= ("upstream_error" :: String)
                            , "error"  .= decErr ]
                        Right v -> do
                          let pipe0 = pipeRowsOf v
                          -- The parser is the validator. If the transcription
                          -- will not parse, show the model its own error and
                          -- let it look at the photograph once more.
                          pipe <- case parsePipeProof pipe0 of
                            Right _ -> pure pipe0
                            Left perr -> do
                              liftAndCatchIO $ stage
                                ("first attempt did not parse; second call. "
                                 ++ take 120 (flatten perr))
                              let note = promptText
                                       ++ "\n\nYour previous attempt could not be "
                                       ++ "read by the proof checker:\n\n" ++ perr
                                       ++ "\n\nLook at the image again and correct "
                                       ++ "it. Do not invent content: if a cell "
                                       ++ "really is blank, leave it blank."
                              again <- liftAndCatchIO $
                                         callAnthropic apiKey media b64 note
                              pure $ case again of
                                Right v2 ->
                                  let p2 = pipeRowsOf v2
                                  in if null p2 then pipe0 else p2
                                Left _ -> pipe0
                          if null pipe
                            then do
                              status status502
                              json $ object
                                [ "status" .= ("no_transcription" :: String)
                                , "error"  .= ("Nothing legible was found in that \
                                               \photo. Try again with more light, \
                                               \or type the proof in directly." :: String) ]
                            else
                              json $ object
                                [ "status"  .= ("ok" :: String)
                                , "pipe"    .= pipe
                                , "notices" .= transcriptionNotices pipe
                                ]
        _ -> do
          status status400
          json $ object
            [ "status" .= ("bad_json" :: String)
            , "error"  .= ("Expected an object with a dataUrl field." :: String) ]

    -- OCR page
    get "/ocr" $ file "static/ocr.html"

    post "/ocr" $ do
      raw <- body
      case A.eitherDecode' raw of
        Left e -> do
          status status400
          json $ object [ "status" .= ("bad_json" :: String), "error" .= e ]
        Right (A.Object o) ->
          case AT.parseEither (AT..: "dataUrl") o of
            Left perr -> do
              status status400
              json $ object [ "status" .= ("bad_json" :: String), "error" .= perr ]
            Right dataUrl -> do
              -- read Mathpix credentials from env
              mAppId  <- liftAndCatchIO $ lookupEnv "MATHPIX_APP_ID"
              mAppKey <- liftAndCatchIO $ lookupEnv "MATHPIX_APP_KEY"
              case (mAppId, mAppKey) of
                (Just appId, Just appKey) -> do
                  let payload = A.object
                        [ "src"         .= (dataUrl :: String)
                        , "formats"     .= (["text"] :: [String])
                        , "rm_spaces"   .= True
                        , "enable_tables" .= True
                        , "data_options" .= A.object
                          [ "include_asciimath" .= False
                          , "include_latex"     .= False
                          ]
                        ]
                  initReq <- liftAndCatchIO $ parseRequest "POST https://api.mathpix.com/v3/text"
                  let req = setRequestBodyLBS (A.encode payload)
                          $ setRequestHeader "Content-Type" ["application/json"]
                          $ setRequestHeader "app_id"  [BS.pack appId]
                          $ setRequestHeader "app_key" [BS.pack appKey]
                          $ initReq
                  resp <- liftAndCatchIO $ httpLBS req
                  let bodyL = getResponseBody resp
                  liftIO $ L8.putStrLn bodyL
                  case A.eitherDecode' bodyL :: Either String A.Value of
                    Left decErr -> do
                      status status500
                      json $ object [ "status" .= ("mathpix_decode_error" :: String), "error" .= decErr ]
                    Right (A.Object r) -> do
                      let rawTxt =
                            (AT.parseMaybe (AT..: "markdown") r)
                            <|> (AT.parseMaybe (AT..: "text") r)

                      case rawTxt of
                        Just t -> do
                          let converted =
                                case OCR.latexTableToPipe t of
                                  Right pipe -> pipe   -- pipe :: String
                                  Left  _    -> t      -- fall back to original
                          json $ object [ "status" .= ("ok" :: String)
                                        , "text"   .= converted
                                        ]
                        Nothing -> do
                          status status500
                          json $ object [ "status" .= ("mathpix_no_text" :: String)
                                        , "error"  .= ("No usable text returned" :: String)
                                        ]                        
                    Right _ -> do
                      status status500
                      json $ object [ "status" .= ("mathpix_bad_response" :: String), "error" .= ("Unexpected JSON shape" :: String) ]
                _ -> do
                  status status500
                  json $ object [ "status" .= ("server_not_configured" :: String)
                                , "error"  .= ("Set MATHPIX_APP_ID and MATHPIX_APP_KEY" :: String) ]
        _ -> do
          status status400
          json $ object [ "status" .= ("bad_json" :: String), "error" .= ("Expected object with dataUrl" :: String) ]
