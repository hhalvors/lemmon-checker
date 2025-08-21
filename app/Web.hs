{-# LANGUAGE OverloadedStrings #-}

module Main where

-- App modules
import qualified LemmonChecker                   as LC
import           ProofTypes
import           PipeParse                       (parsePipeProof)
import           PrettyPrint                     (renderFormula)
import           FormulaParser                   (parseFormula)
import           ModelSemantics                  (Model, evalClosed)
import           Normalize                       (normalizeSyntax)
import           TruthTable                      (truthTable)
import           PropDNF                         (toDNF)

-- Web stack
import           Web.Scotty
import           Network.Wai                     (Request(..), RequestBodyLength(..))
import           Network.Wai.Middleware.Static   (staticPolicy, addBase)
import           Network.Wai.Middleware.RequestLogger (logStdoutDev)
import           Network.HTTP.Types.Status       (status200, status400, status401, status413)

-- Utils & JSON
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

--------------------------------------------------------------------------------
-- Limits (tweak to taste)
--------------------------------------------------------------------------------

maxBodyBytes  :: Int
maxBodyBytes  = 128 * 1024      -- 128 KiB

maxProofLines :: Int
maxProofLines = 400

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
          case parsePipeProof (normalizeSyntax inputTxt) of
            Left perr -> do
              status status400
              json $ object
                [ "status" .= ("parse_error" :: String)
                , "error"  .= perr
                ]
            Right proof -> do
              let reps = LC.checkProof proof
              json $ object
                [ "status" .= ("ok" :: String)
                , "report" .= reportToJSON reps
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

        Right (A.Object o) -> do
          -- pull "sentenceText" out of the JSON object
          case AT.parseEither (\obj -> obj A..: "sentenceText") o of
            Left e -> do
              status status400
              json $ object
                [ "status" .= ("bad_json" :: String)
                , "error"  .= e
                ]
            Right sTxt -> do
              let sNorm = normalizeSyntax sTxt
              case parseFormula sNorm of
                Left perr -> do
                  status status400
                  json $ object
                    [ "status" .= ("parse_error" :: String)
                    , "error"  .= perr
                    ]
                Right phi ->
                  case truthTable phi of
                    Left err -> do
                      status status400
                      json $ object
                        [ "status" .= ("non_propositional" :: String)
                        , "error"  .= err
                        ]
                    Right rows -> do
                      let phiStr = renderFormula phi
                          enc (valMap, b) = object
                            [ "valuation" .= M.fromList (M.toList valMap)
                            , "value"     .= b
                            ]
                      json $ object
                        [ "status" .= ("ok" :: String)
                        , "header" .= phiStr
                        , "rows"   .= map enc rows
                        ]

        Right _ -> do
          status status400
          json $ object
            [ "status" .= ("bad_json" :: String)
            , "error"  .= ("Expected JSON object with key \"sentenceText\"" :: String)
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
