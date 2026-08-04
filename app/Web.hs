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
import Control.Concurrent.MVar             (MVar, newMVar, modifyMVar)
import Control.Exception                   (try, SomeException, displayException)
import qualified Network.HTTP.Client       as HC
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
splitDataUrl :: String -> Maybe (String, String)
splitDataUrl s = do
  rest          <- stripPrefix' "data:" s
  let (meta, enc) = break (== ',') rest
  payload       <- case enc of
                     (_:p) -> Just p
                     []    -> Nothing
  media         <- case break (== ';') meta of
                     (m, ";base64") -> Just m
                     _              -> Nothing
  pure (media, payload)
  where
    stripPrefix' p xs
      | take (length p) xs == p = Just (drop (length p) xs)
      | otherwise               = Nothing

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

callAnthropic :: String -> String -> String -> String -> IO (Either String A.Value)
callAnthropic rawKey media b64 promptText = do
  let apiKey = trimKey rawKey
  initReq <- parseRequest "POST https://api.anthropic.com/v1/messages"
  let payload = A.object
        [ "model"      .= ("claude-sonnet-5" :: String)
        , "max_tokens" .= (8000 :: Int)
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
  outcome <- try (httpLBS req)
  case outcome of
    Left e -> do
      let msg = displayException (e :: SomeException)
      putStrLn ("[transcribe] request to api.anthropic.com failed: " ++ msg)
      pure (Left ("Could not reach the transcription service. " ++ takeWhile (/= '\n') msg))
    Right resp -> do
      let code = getResponseStatusCode resp
          bodyL = getResponseBody resp
      if code < 200 || code >= 300
        then do
          putStrLn ("[transcribe] api.anthropic.com returned " ++ show code
                    ++ ": " ++ take 400 (L8.unpack bodyL))
          pure (Left ("The transcription service returned HTTP " ++ show code
                      ++ ". " ++ take 200 (L8.unpack bodyL)))
        else pure (A.eitherDecode' bodyL)

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
              case splitDataUrl (dataUrl :: String) of
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
                      first <- liftAndCatchIO $ callAnthropic apiKey media b64 promptText
                      case first of
                        Left decErr -> do
                          status status500
                          json $ object
                            [ "status" .= ("upstream_error" :: String)
                            , "error"  .= decErr ]
                        Right v -> do
                          let pipe0 = pipeRowsOf (responseText v)
                          -- The parser is the validator. If the transcription
                          -- will not parse, show the model its own error and
                          -- let it look at the photograph once more.
                          pipe <- case parsePipeProof pipe0 of
                            Right _ -> pure pipe0
                            Left perr -> do
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
                                  let p2 = pipeRowsOf (responseText v2)
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
