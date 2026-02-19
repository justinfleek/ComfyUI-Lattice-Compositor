{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

{- | jaylene-slide: Console cowboy for the sprawl

Jacks into OpenAI-compatible inference endpoints (Baseten, Together, etc.),
parses their SSE/JSON garbage, and emits clean SIGIL binary frames over ZMQ.
-}
module Main (main) where

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // imports
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Control.Concurrent.Async (async)
import Control.Exception (bracket, throwIO)
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (object, (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T

import Data.Text.Encoding qualified as TE
import Data.Text.IO qualified as TIO
import Data.Vector.Unboxed qualified as VU
import Data.Word (Word32, Word64)
import Dhall qualified
import Katip
import Network.HTTP.Types (status200)
import Network.Wai qualified as Wai
import Network.Wai.Handler.Warp (run)
import Numeric (showHex)
import Options.Applicative (
    Parser,
    ParserInfo,
    ReadM,
    argument,
    auto,
    command,
    eitherReader,
    execParser,
    fullDesc,
    header,
    help,
    helper,
    hsubparser,
    info,
    long,
    metavar,
    maybeReader,
    option,
    optional,
    progDesc,
    short,
    str,
    strOption,
    switch,
    value,
    (<**>),
 )
import Prometheus qualified as P
import Prometheus.Metric.GHC qualified as P
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.IO (hFlush, hPutStrLn, isEOF, stderr, stdout)
import System.Random (randomIO)
import System.ZMQ4 (Pub (..), Socket, Sub (..), bind, close, connect, context, receiveMulti, sendMulti, socket, subscribe, term)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Time.Clock.POSIX (POSIXTime, getPOSIXTime, posixSecondsToUTCTime)
import Data.Time.Format.ISO8601 (iso8601Show)

import Slide.Chunk (
    ChunkState,
    ProcessResult (..),
    finalizeChunk,
    initChunkState,
    processToken,
    flushTextChunk,
 )
import Slide.Configuration qualified as Config
import Slide.Configuration (JackConfig (..), verifyHash)
import Slide.HotTable (HotTable, defaultHotTable, loadHotTable)
import Slide.Parse (ToolCallDelta (..))
import Slide.Provider (defaultStreamConfig, StreamEvent(..), AuthScheme(..))
import Slide.Provider.OpenAI (OpenAIConfig(..), OpenAIConnection, withOpenAIConnection, streamCompletion)
import Slide.Provider.OpenRouter qualified as OpenRouter
import Slide.Provider.Vertex.Anthropic qualified as VertexAnthropic
import Slide.Tokenizer (HFTokenizer, decode, encode, loadTokenizerJSON, loadIdentityTokenizer, tokenToId)
import Slide.Wire.Decode (Chunk (..), ChunkContent (..), decodeFrameIncremental, initDecodeState)
import Slide.Wire.Frame (Frame (..), FrameOp, newFrameBuilder, writeControl, writeExtendedToken, builderLength, finishFrame)
import Slide.Wire.Types (
    pattern OP_TOOL_CALL_START,
    pattern OP_TOOL_CALL_END
 )

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // stream metadata
-- ════════════════════════════════════════════════════════════════════════════

-- | Metadata attached to each ZMQ message for multi-stream support
data StreamMetadata = StreamMetadata
    { metaStreamId :: !Text
    -- ^ Unique stream identifier
    , metaModel :: !Text
    -- ^ Model name (e.g., "anthropic/claude-sonnet-4")
    , metaTimestamp :: !Double
    -- ^ Unix timestamp
    }
    deriving (Show, Eq)

instance Aeson.ToJSON StreamMetadata where
    toJSON meta = object
        [ "stream_id" .= metaStreamId meta
        , "model" .= metaModel meta
        , "timestamp" .= metaTimestamp meta
        ]

instance Aeson.FromJSON StreamMetadata where
    parseJSON = Aeson.withObject "StreamMetadata" $ \v ->
        StreamMetadata
            <$> v Aeson..: "stream_id"
            <*> v Aeson..: "model"
            <*> v Aeson..: "timestamp"

-- | Create ZMQ topic from model name
modelToTopic :: Text -> BS.ByteString
modelToTopic model = TE.encodeUtf8 $ "model/" <> model

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // jsonl accumulator
-- ════════════════════════════════════════════════════════════════════════════

-- | Accumulated response for JSONL logging
data AccumulatedResponse = AccumulatedResponse
    { accStreamId :: !Text
    , accModel :: !Text
    , accStartTime :: !POSIXTime
    , accTextTokens :: ![Word32]
    , accThinkTokens :: ![Word32]
    , accToolCalls :: ![AccumulatedToolCall]
    }

data AccumulatedToolCall = AccumulatedToolCall
    { toolTokens :: ![Word32]
    }

emptyAccumulator :: Text -> Text -> POSIXTime -> AccumulatedResponse
emptyAccumulator streamId model startTime = AccumulatedResponse
    { accStreamId = streamId
    , accModel = model
    , accStartTime = startTime
    , accTextTokens = []
    , accThinkTokens = []
    , accToolCalls = []
    }

-- | Write accumulated response to JSONL file
writeJsonlEntry :: FilePath -> HFTokenizer -> AccumulatedResponse -> IO ()
writeJsonlEntry logPath tokenizer acc = do
    endTime <- getPOSIXTime
    
    -- Decode accumulated tokens to text
    responseText <- decode tokenizer (accTextTokens acc)
    thinkText <- if null (accThinkTokens acc)
        then pure Nothing
        else Just <$> decode tokenizer (accThinkTokens acc)
    
    -- Decode tool calls
    toolCallTexts <- mapM (decode tokenizer . toolTokens) (accToolCalls acc)
    
    let entry = object
            [ "stream_id" .= accStreamId acc
            , "model" .= accModel acc
            , "start_time" .= iso8601Show (posixSecondsToUTCTime $ accStartTime acc)
            , "end_time" .= iso8601Show (posixSecondsToUTCTime endTime)
            , "duration_ms" .= (round ((endTime - accStartTime acc) * 1000) :: Int)
            , "response" .= responseText
            , "thinking" .= thinkText
            , "tool_calls" .= toolCallTexts
            , "token_count" .= length (accTextTokens acc)
            ]
    
    -- Append to file
    LBS.appendFile logPath (Aeson.encode entry <> "\n")

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // cli // configuration
-- ════════════════════════════════════════════════════════════════════════════

data Command
    = CommandJack !JackOptions
    | CommandListen !ListenOptions

data JackOptions = JackOptions
    { jackEndpoint :: !(Maybe Text)
    , jackEndpointFlag :: !(Maybe Text)
    , jackApiKey :: !(Maybe Text)
    , jackModel :: !(Maybe Text)
    , jackZmqBind :: !Text
    , jackHotTable :: !(Maybe FilePath)
    , jackTokenizer :: !(Maybe FilePath)
    , jackVerbose :: !Bool
    , jackJsonLogs :: !Bool
    , jackMetricsPort :: !Int
    , jackFlushThreshold :: !Int
    , jackProvider :: !ProviderType
    , jackConfigPath :: !(Maybe FilePath)
    , jackStreamId :: !(Maybe Text)
    -- ^ Unique stream identifier (defaults to random)
    }

data ProviderType
    = ProviderBaseten
    | ProviderOpenAI
    | ProviderOpenRouter
    | ProviderVertex
    deriving (Show, Eq)

data OutputFormat
    = FormatText
    | FormatOpenAI
    deriving (Show, Eq)

data ListenOptions = ListenOptions
    { listenZmqConnect :: !Text
    , listenTokenizer :: !FilePath
    , listenVerbose :: !Bool
    , listenShowThink :: !Bool
    , listenDumpFrames :: !Bool
    , listenFormat :: !OutputFormat
    , listenTopic :: !(Maybe Text)
    -- ^ ZMQ topic filter (e.g., "model/anthropic/*")
    , listenLogJsonl :: !(Maybe FilePath)
    -- ^ Log training data to JSONL file
    }

parseCommand :: Parser Command
parseCommand =
    hsubparser
        ( command "jack" (info (CommandJack <$> parseJackOptions) (progDesc "Jack into provider and emit frames"))
            <> command "listen" (info (CommandListen <$> parseListenOptions) (progDesc "Listen to frames and print text"))
        )

parseJackOptions :: Parser JackOptions
parseJackOptions =
    JackOptions
        <$> optional
            ( argument
                str
                ( metavar "ENDPOINT"
                    <> help "Provider endpoint URL"
                )
            )
        <*> optional
            ( strOption
                ( long "endpoint"
                    <> short 'e'
                    <> metavar "URL"
                    <> help "Provider endpoint URL (flag form)"
                )
            )
        <*> optional
            ( strOption
                ( long "api-key"
                    <> short 'k'
                    <> metavar "KEY"
                    <> help "API key (default: $JAYLENE_API_KEY)"
                )
            )
        <*> optional
            ( strOption
                ( long "model"
                    <> short 'm'
                    <> metavar "MODEL"
                    <> help "Model override"
                )
            )
        <*> strOption
            ( long "zmq"
                <> short 'z'
                <> metavar "BIND"
                <> value "tcp://*:5555"
                <> help "ZMQ PUB bind address"
            )
        <*> optional
            ( strOption
                ( long "hot-table"
                    <> metavar "PATH"
                    <> help "Hot token table path"
                )
            )
        <*> optional
            ( strOption
                ( long "tokenizer"
                    <> short 't'
                    <> metavar "PATH"
                    <> help "Tokenizer JSON path"
                )
            )
        <*> switch
            ( long "verbose"
                <> short 'v'
                <> help "Verbose logging"
            )
        <*> switch
            ( long "json-logs"
                <> help "Emit structured JSON logs (good for Datadog/CloudWatch)"
            )
        <*> option
            auto
            ( long "metrics-port"
                <> value 9090
                <> metavar "PORT"
                <> help "Prometheus metrics port (default: 9090)"
            )
        <*> option
            auto
            ( long "flush-every"
                <> value 8
                <> metavar "N"
                <> help "Flush chunk every N tokens (default: 8)"
            )
        <*> option
            (maybeReader parseProvider)
            ( long "provider"
                <> value ProviderBaseten
                <> metavar "PROVIDER"
                <> help "Provider type (baseten, openai, vertex)"
            )
        <*> optional
            ( strOption
                ( long "config"
                    <> short 'c'
                    <> metavar "DHALL"
                    <> help "Load configuration from Dhall file"
                )
            )
        <*> optional
            ( strOption
                ( long "stream-id"
                    <> metavar "ID"
                    <> help "Unique stream identifier (defaults to random UUID)"
                )
            )

parseProvider :: String -> Maybe ProviderType
parseProvider "baseten" = Just ProviderBaseten
parseProvider "openai" = Just ProviderOpenAI
parseProvider "openrouter" = Just ProviderOpenRouter
parseProvider "vertex" = Just ProviderVertex
parseProvider _ = Nothing

parseListenOptions :: Parser ListenOptions
parseListenOptions =
    ListenOptions
        <$> strOption
            ( long "zmq"
                <> short 'z'
                <> metavar "CONNECT"
                <> value "tcp://localhost:5555"
                <> help "ZMQ SUB connect address"
            )
        <*> strOption
            ( long "tokenizer"
                <> short 't'
                <> metavar "PATH"
                <> help "Tokenizer JSON path"
            )
        <*> switch
            ( long "verbose"
                <> short 'v'
                <> help "Show debug info"
            )
        <*> switch
            ( long "show-think"
                <> help "Display <think> blocks in output"
            )
        <*> switch
            ( long "dump-frames"
                <> help "Dump raw frame bytes and structure"
            )
        <*> option parseOutputFormat
            ( long "format"
                <> short 'f'
                <> metavar "FORMAT"
                <> value FormatText
                <> help "Output format: text (default), openai"
            )
        <*> optional
            ( strOption
                ( long "topic"
                    <> metavar "PATTERN"
                    <> help "ZMQ topic filter (e.g., 'model/anthropic/*')"
                )
            )
        <*> optional
            ( strOption
                ( long "log-jsonl"
                    <> metavar "FILE"
                    <> help "Log training data to JSONL file"
                )
            )

parseOutputFormat :: ReadM OutputFormat
parseOutputFormat = eitherReader $ \case
    "text" -> Right FormatText
    "openai" -> Right FormatOpenAI
    other -> Left $ "Unknown format: " <> other <> ". Use 'text' or 'openai'"

commandLineParserInfo :: ParserInfo Command
commandLineParserInfo =
    info
        (parseCommand <**> helper)
        ( fullDesc
            <> progDesc "jaylene-slide ingress adapter"
            <> header "jaylene-slide — console cowboy for the sprawl"
        )

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // logging // setup
-- ════════════════════════════════════════════════════════════════════════════

initLogging :: Bool -> Bool -> Namespace -> (LogEnv -> IO a) -> IO a
initLogging verbose _useJson _namespace action = do
    handleScribe <- mkHandleScribe ColorIfTerminal stderr (permitItem logLevel) V2
    let mkLogEnv = initLogEnv "slide" "production"
    bracket mkLogEnv closeScribes $ \logEnv -> do
        let scribeName = "stderr"
        logEnvWithScribe <- registerScribe scribeName handleScribe defaultScribeSettings logEnv
        action logEnvWithScribe
  where
    logLevel = if verbose then DebugS else InfoS

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // main // entry point
-- ════════════════════════════════════════════════════════════════════════════

main :: IO ()
main = do
    cmd <- execParser commandLineParserInfo
    case cmd of
        CommandJack options ->
            initLogging (jackVerbose options) (jackJsonLogs options) (Namespace ["jack"]) $ \le ->
                runKatipContextT le () (Namespace ["jack"]) (runJack options)
        CommandListen options ->
            initLogging (listenVerbose options) False (Namespace ["listen"]) $ \le ->
                runKatipContextT le () (Namespace ["listen"]) (runListen options)

-- ════════════════════════════════════════════════════════════════════════════════
-- Metrics
-- ════════════════════════════════════════════════════════════════════════════════

data Metrics = Metrics
    { metricsFramesEmitted :: !P.Counter
    , metricsBytesEmitted :: !P.Counter
    , metricsTokensProcessed :: !P.Counter
    }

setupMetrics :: Int -> IO Metrics
setupMetrics port = do
    -- Register GHC metrics
    _ <- P.register P.ghcMetrics

    -- Register App metrics
    frames <- P.register $ P.counter (P.Info "slide_frames_emitted_total" "Total frames emitted via ZMQ")
    bytes <- P.register $ P.counter (P.Info "slide_bytes_emitted_total" "Total bytes emitted via ZMQ")
    tokens <- P.register $ P.counter (P.Info "slide_tokens_processed_total" "Total tokens processed from provider")

    -- Start metrics server in background
    let metricsApp :: Wai.Application
        metricsApp _req respond = do
            metrics <- P.exportMetricsAsText
            respond $ Wai.responseLBS status200 [("Content-Type", "text/plain")] metrics

    _ <- async $ run port metricsApp

    pure $ Metrics
        { metricsFramesEmitted = frames
        , metricsBytesEmitted = bytes
        , metricsTokensProcessed = tokens
        }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // jack mode
-- ════════════════════════════════════════════════════════════════════════════

runJack :: (KatipContext m) => JackOptions -> m ()
runJack options = do
    printBanner options

    -- Resolve configuration sources
    (resolvedEndpoint, resolvedTokenizerPath, resolvedModel, resolvedHotTablePath, resolvedAuth, resolvedDelimiters, resolvedProviderType) <- liftIO $ resolveConfig options

    -- Determine provider priority: Config > CLI > Default
    let selectedProvider = case resolvedProviderType of
            Just providerType -> providerType
            Nothing -> jackProvider options

    apiKey <- liftIO $ resolveApiKey options resolvedAuth

    -- Log authentication status (masked)
    case apiKey of
        Just key -> do
            let masked = if T.length key > 8 then T.take 4 key <> "..." <> T.takeEnd 4 key else "***"
            logFM InfoS $ ls $ "authentication: key loaded (" <> masked <> ")"
        Nothing ->
            logFM WarningS "authentication: no api key found (checked CLI, Config, Env)"

    hotTable <- liftIO $ resolveHotTable options resolvedHotTablePath

    logFM InfoS $ ls $ "loading tokenizer: " <> resolvedTokenizerPath
    
    -- Tokenizer hash verification already done in resolveConfig (fail-fast)
    tokenizer <- liftIO $ if resolvedTokenizerPath == "identity"
        then loadIdentityTokenizer
        else loadTokenizerJSON resolvedTokenizerPath

    _boundaryTokens <- liftIO $ createBoundaryTokenSet tokenizer
    specialTokens <- liftIO $ createSpecialTokenConfig tokenizer resolvedDelimiters

    -- Setup metrics
    metrics <- liftIO $ setupMetrics (jackMetricsPort options)

    logFM InfoS "jacking in..."

    -- Capture logging context to restore it inside IO callbacks
    logEnv <- getLogEnv
    katipContext <- getKatipContext
    katipNamespace <- getKatipNamespace

    -- Initialize ZMQ context and socket
    liftIO $ bracket context term $ \zmqContext ->
        bracket (socket zmqContext Pub) close $ \publisherSocket -> do
            bind publisherSocket (T.unpack $ jackZmqBind options)

            let authScheme = case apiKey of
                    Just key -> case resolvedAuth of
                        Just Config.ApiKey -> AuthApiKey key
                        Just Config.Bearer -> AuthBearer key
                        Just (Config.ApiKeyFile _) -> AuthApiKey key -- Resolved content is the key
                        Just Config.None -> AuthNone
                        Nothing -> case selectedProvider of
                            ProviderBaseten -> AuthApiKey key
                            ProviderOpenAI -> AuthBearer key
                            ProviderOpenRouter -> AuthBearer key
                            ProviderVertex -> AuthBearer key
                    Nothing -> case resolvedAuth of
                        Just Config.None -> AuthNone
                        _ -> AuthNone -- Default if no key found

            -- Determine provider and dispatch connection logic
            case selectedProvider of
                ProviderOpenAI -> do
                    let modelName = fromMaybe "unknown" resolvedModel
                        config = OpenAIConfig
                            { openaiEndpoint = resolvedEndpoint
                            , openaiAuth = authScheme
                            , openaiModel = resolvedModel
                            }
                    withOpenAIConnection config $ \connection -> do
                        let activeConnection = ConnOpenAI connection
                        runKatipContextT logEnv katipContext katipNamespace $ do
                            logFM InfoS "connected (OpenAI). prompts on stdin, frames on zmq."
                            runPromptLoop options activeConnection modelName tokenizer hotTable _boundaryTokens specialTokens publisherSocket metrics

                ProviderBaseten -> do
                    -- Baseten uses OpenAI protocol
                    let modelName = fromMaybe "unknown" resolvedModel
                        config = OpenAIConfig
                            { openaiEndpoint = resolvedEndpoint
                            , openaiAuth = authScheme
                            , openaiModel = resolvedModel
                            }
                    withOpenAIConnection config $ \connection -> do
                        let activeConnection = ConnOpenAI connection
                        runKatipContextT logEnv katipContext katipNamespace $ do
                            logFM InfoS "connected (Baseten/OpenAI). prompts on stdin, frames on zmq."
                            runPromptLoop options activeConnection modelName tokenizer hotTable _boundaryTokens specialTokens publisherSocket metrics

                ProviderOpenRouter -> do
                    -- OpenRouter unified API
                    case (apiKey, resolvedModel) of
                        (Just key, Just model) -> do
                            let openRouterConfig = OpenRouter.defaultOpenRouterConfig key model
                            OpenRouter.withOpenRouterConnection openRouterConfig $ \connection -> do
                                let activeConnection = ConnOpenRouter connection
                                runKatipContextT logEnv katipContext katipNamespace $ do
                                    logFM InfoS $ ls $ "connected (OpenRouter). model: " <> model
                                    runPromptLoop options activeConnection model tokenizer hotTable _boundaryTokens specialTokens publisherSocket metrics
                        (Nothing, _) -> do
                            runKatipContextT logEnv katipContext katipNamespace $
                                logFM ErrorS "OpenRouter requires an API key (--api-key or OPENROUTER_API_KEY)"
                            exitFailure
                        (_, Nothing) -> do
                            runKatipContextT logEnv katipContext katipNamespace $
                                logFM ErrorS "OpenRouter requires a model (--model, e.g., anthropic/claude-sonnet-4)"
                            exitFailure

                ProviderVertex -> do
                    -- Vertex AI with Anthropic models
                    let vertexModel = fromMaybe "claude-3-5-sonnet@20240620" resolvedModel
                        vertexConfig = VertexAnthropic.VertexAnthropicConfig
                            { VertexAnthropic.vertexEndpoint = resolvedEndpoint
                            , VertexAnthropic.vertexAuth = authScheme
                            , VertexAnthropic.vertexModel = vertexModel
                            , VertexAnthropic.vertexRegion = "" -- Parsed from endpoint
                            , VertexAnthropic.vertexProject = "" -- Parsed from endpoint
                            }
                    VertexAnthropic.withVertexAnthropicConnection vertexConfig $ \connection -> do
                        let activeConnection = ConnVertexAnthropic connection
                        runKatipContextT logEnv katipContext katipNamespace $ do
                            logFM InfoS "connected (Vertex/Anthropic). prompts on stdin, frames on zmq."
                            runPromptLoop options activeConnection vertexModel tokenizer hotTable _boundaryTokens specialTokens publisherSocket metrics

resolveConfig :: JackOptions -> IO (Text, FilePath, Maybe Text, Maybe FilePath, Maybe Config.AuthScheme, Config.Delimiters, Maybe ProviderType)
resolveConfig options = do
    case jackConfigPath options of
        Just path -> do
            config <- Dhall.inputFile Dhall.auto path :: IO JackConfig
            
            -- Verify tokenizer
            let tPath = T.unpack $ Config.tokenizer_path config
            -- Skip verification for identity
            unless (tPath == "identity") $ do
                tContent <- BS.readFile tPath
                let tSpecHash = Config.tokenizer $ Config.model config
                unless (verifyHash tContent tSpecHash) $ do
                    throwIO $ userError $ "Tokenizer hash verification failed for " <> tPath
            
            let providerSpec = Config.provider config
            
            -- Determine provider type from config
            let pType = case Config.providerType providerSpec of
                    Config.OpenAI -> ProviderOpenAI
                    Config.Baseten -> ProviderBaseten
                    Config.Vertex -> ProviderVertex

            pure ( Config.endpoint providerSpec
                 , tPath
                 , Config.model_override providerSpec
                 , fmap T.unpack (Config.hot_table_path config)
                 , Just (Config.auth providerSpec)
                 , Config.delimiters (Config.model config)
                 , Just pType
                 )
        Nothing -> do
            -- Fallback to CLI
            -- OpenRouter doesn't require an endpoint (it's fixed)
            let providerType = jackProvider options
            endpoint <- case jackEndpointFlag options of
                Just endpointUrl -> pure endpointUrl
                Nothing -> case jackEndpoint options of
                    Just endpointUrl -> pure endpointUrl
                    Nothing -> case providerType of
                        ProviderOpenRouter -> pure ""  -- OpenRouter has a fixed endpoint
                        _ -> throwIO $ userError "No endpoint specified (use argument, --endpoint, or --config)"

            tokenizerPath <- case jackTokenizer options of
                Just path -> pure path
                Nothing -> throwIO $ userError "No tokenizer specified (use --tokenizer or --config)"
            
            -- Default delimiters for CLI mode
            let defaults = Config.Delimiters 
                    { Config.think_start = Just "<think>"
                    , Config.think_end = Just "</think>"
                    , Config.tool_start = Just "<tool_call>"
                    , Config.tool_end = Just "</tool_call>"
                    , Config.code_fence = "```"
                    }

            pure (endpoint, tokenizerPath, jackModel options, jackHotTable options, Nothing, defaults, Nothing)

resolveApiKey :: JackOptions -> Maybe Config.AuthScheme -> IO (Maybe Text)
resolveApiKey options maybeAuth = do
    -- 1. CLI Override
    case jackApiKey options of
        Just providedKey -> pure (Just providedKey)
        Nothing -> do
            -- 2. Config File Strategy
            case maybeAuth of
                Just (Config.ApiKeyFile path) -> do
                    -- Read key from file (trimming whitespace)
                    content <- TIO.readFile (T.unpack path)
                    pure $ Just (T.strip content)
                _ -> do
                    -- 3. Provider-specific environment variable
                    providerKey <- case jackProvider options of
                        ProviderOpenRouter -> lookupEnv "OPENROUTER_API_KEY"
                        ProviderOpenAI -> lookupEnv "OPENAI_API_KEY"
                        ProviderVertex -> lookupEnv "VERTEX_API_KEY"
                        ProviderBaseten -> lookupEnv "BASETEN_API_KEY"
                    case providerKey of
                        Just keyFromEnv -> pure (Just $ T.pack keyFromEnv)
                        Nothing -> do
                            -- 4. Generic environment variable (Legacy/Dev)
                            environmentKey <- lookupEnv "JAYLENE_API_KEY"
                            case environmentKey of
                                Just keyFromEnv -> pure (Just $ T.pack keyFromEnv)
                                Nothing -> pure Nothing

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // listen mode
-- ════════════════════════════════════════════════════════════════════════════

runListen :: (KatipContext m) => ListenOptions -> m ()
runListen options = do
    logFM InfoS $ ls $ "loading tokenizer: " <> listenTokenizer options
    tokenizer <- liftIO $ if listenTokenizer options == "identity"
        then loadIdentityTokenizer
        else loadTokenizerJSON (listenTokenizer options)

    logFM InfoS $ ls $ "connecting to: " <> listenZmqConnect options
    logFM InfoS $ ls $ "output format: " <> T.pack (show (listenFormat options))
    case listenTopic options of
        Just topic -> logFM InfoS $ ls $ "topic filter: " <> topic
        Nothing -> logFM InfoS "topic filter: (none, accepting all)"

    liftIO $ bracket context term $ \zmqContext ->
        bracket (socket zmqContext Sub) close $ \subscriberSocket -> do
            connect subscriberSocket (T.unpack $ listenZmqConnect options)
            -- Subscribe to topic prefix or empty for all
            let subscribePrefix = case listenTopic options of
                    Just topic -> TE.encodeUtf8 $ "model/" <> topic
                    Nothing -> ""
            subscribe subscriberSocket subscribePrefix

            hPutStrLn stderr "[slide] [listen] waiting for frames..."
            
            -- Initialize accumulator ref for JSONL logging
            accumulatorRef <- newIORef Nothing :: IO (IORef (Maybe AccumulatedResponse))
            
            -- Run stateful decoding loop
            -- For OpenAI format, we buffer incomplete chunks and coalesce
            -- State: (decoderState, streamId, pendingTokens)
            let loop !decoderState !streamId !pendingTokens = do
                    parts <- receiveMulti subscriberSocket
                    
                    -- Parse multipart message: [topic, metadata, frame] or legacy [frame]
                    let (maybeMeta, frameData) = case parts of
                            [_topic, metaJson, frame] -> 
                                (Aeson.decodeStrict metaJson, frame)
                            [frame] -> 
                                -- Legacy single-part message
                                (Nothing, frame)
                            _ -> 
                                -- Unexpected format, treat as empty
                                (Nothing, "")

                    when (listenDumpFrames options) $ do
                        TIO.putStrLn ""
                        TIO.putStrLn $ "── // frame // " <> T.pack (show (BS.length frameData)) <> " bytes ──────────────────────────────────────────"
                        case maybeMeta of
                            Just meta -> TIO.putStrLn $ "   [meta] stream=" <> metaStreamId meta <> " model=" <> metaModel meta
                            Nothing -> TIO.putStrLn "   [meta] (none)"
                        TIO.putStrLn $ "   " <> T.pack (foldMap (`showHex` "") (BS.unpack frameData))

                    -- Initialize accumulator on first message with metadata (for JSONL logging)
                    case (listenLogJsonl options, maybeMeta) of
                        (Just _, Just meta) -> do
                            currentAcc <- readIORef accumulatorRef
                            case currentAcc of
                                Nothing -> do
                                    -- Start new accumulator
                                    now <- getPOSIXTime
                                    writeIORef accumulatorRef $ Just $
                                        emptyAccumulator (metaStreamId meta) (metaModel meta) now
                                Just _ -> pure ()  -- Already accumulating
                        _ -> pure ()

                    -- Use decodeFrameIncremental to maintain state across frames
                    let (nextState, chunks) = decodeFrameIncremental decoderState frameData
                    
                    -- Accumulate tokens for JSONL logging
                    case listenLogJsonl options of
                        Just logPath -> 
                            accumulateAndMaybeWrite logPath tokenizer accumulatorRef chunks
                        Nothing -> pure ()
                    
                    -- Output chunks in appropriate format
                    (newStreamId, newPending) <- case listenFormat options of
                        FormatText -> do
                            mapM_ (printChunkText tokenizer (listenShowThink options) (listenDumpFrames options)) chunks
                            pure (streamId, [])
                        FormatOpenAI -> 
                            processChunksOpenAI tokenizer streamId pendingTokens chunks
                    
                    hFlush stdout
                    loop nextState newStreamId newPending

            -- Generate initial stream ID
            initialStreamId <- randomIO :: IO Word64
            loop initDecodeState initialStreamId []

-- | Accumulate chunks and write JSONL on StreamEnd
accumulateAndMaybeWrite :: FilePath -> HFTokenizer -> IORef (Maybe AccumulatedResponse) -> [Chunk] -> IO ()
accumulateAndMaybeWrite logPath tokenizer accRef chunks = mapM_ processChunk chunks
  where
    processChunk (Chunk content _isComplete) = case content of
        TextContent tokens -> 
            modifyIORef' accRef $ fmap $ \acc -> 
                acc { accTextTokens = accTextTokens acc ++ tokens }
        
        ThinkContent tokens ->
            modifyIORef' accRef $ fmap $ \acc ->
                acc { accThinkTokens = accThinkTokens acc ++ tokens }
        
        ToolCallContent tokens ->
            modifyIORef' accRef $ fmap $ \acc ->
                acc { accToolCalls = accToolCalls acc ++ [AccumulatedToolCall tokens] }
        
        CodeBlockContent tokens ->
            -- Treat code blocks as text content
            modifyIORef' accRef $ fmap $ \acc ->
                acc { accTextTokens = accTextTokens acc ++ tokens }
        
        StreamEnd -> do
            -- Write accumulated response and reset
            maybeAcc <- readIORef accRef
            case maybeAcc of
                Just acc -> do
                    writeJsonlEntry logPath tokenizer acc
                    writeIORef accRef Nothing
                Nothing -> pure ()
        
        DecodeError _ -> pure ()
        AmbiguityReset _ -> pure ()  -- Reset handled at wire level

-- | Print chunk in plain text format
printChunkText :: HFTokenizer -> Bool -> Bool -> Chunk -> IO ()
printChunkText tokenizer showThink dumpFrames (Chunk content isComplete) = do
    when dumpFrames $ do
        TIO.putStrLn $ "   [chunk] complete: " <> T.pack (show isComplete)
        TIO.putStrLn $ "   [content] " <> T.pack (show content)
        TIO.putStrLn "────────────────────────────────────────────────────────────────────────────────"

    case content of
        TextContent tokens -> do
            text <- decode tokenizer tokens
            TIO.putStr text
        ThinkContent tokens -> do
            when showThink $ do
                text <- decode tokenizer tokens
                TIO.putStr $ "\n<think>\n" <> text <> "\n</think>\n"
        ToolCallContent tokens -> do
            text <- decode tokenizer tokens
            TIO.putStr $ "\n[TOOL] " <> text <> "\n"
        CodeBlockContent tokens -> do
            text <- decode tokenizer tokens
            TIO.putStr text
        StreamEnd -> do
            TIO.putStrLn "\n[EOS]"
        DecodeError err -> do
            TIO.putStrLn $ "\n[ERROR] " <> err
        AmbiguityReset reason -> do
            TIO.putStrLn $ "\n[AMBIGUITY RESET] " <> T.pack (show reason)

-- | Process chunks for OpenAI SSE format with coalescing
-- Buffers incomplete chunks, emits only on complete boundaries
-- Returns (newStreamId, pendingTokens)
processChunksOpenAI :: HFTokenizer -> Word64 -> [Word32] -> [Chunk] -> IO (Word64, [Word32])
processChunksOpenAI tokenizer streamId initialPending chunks = go streamId initialPending chunks
  where
    go currentId pending [] = pure (currentId, pending)
    go currentId pending (Chunk content isComplete : rest) = case content of
        TextContent tokens -> do
            let allTokens = pending ++ tokens
            if isComplete
                then do
                    -- Emit coalesced content
                    text <- decode tokenizer allTokens
                    unless (T.null text) $ emitOpenAIDelta currentId text
                    go currentId [] rest
                else
                    -- Buffer incomplete chunk
                    go currentId allTokens rest
                    
        ThinkContent tokens -> do
            -- Flush pending first
            unless (null pending) $ do
                text <- decode tokenizer pending
                unless (T.null text) $ emitOpenAIDelta currentId text
            -- Emit thinking content
            text <- decode tokenizer tokens
            unless (T.null text) $ emitOpenAIDelta currentId text
            go currentId [] rest
            
        ToolCallContent tokens -> do
            -- Flush pending text first
            unless (null pending) $ do
                text <- decode tokenizer pending
                unless (T.null text) $ emitOpenAIDelta currentId text
            -- Emit as tool_calls delta
            text <- decode tokenizer tokens
            unless (T.null text) $ emitOpenAIToolCallDelta currentId 0 text
            go currentId [] rest
            
        CodeBlockContent tokens -> do
            let allTokens = pending ++ tokens
            if isComplete
                then do
                    text <- decode tokenizer allTokens
                    unless (T.null text) $ emitOpenAIDelta currentId text
                    go currentId [] rest
                else
                    go currentId allTokens rest
                    
        StreamEnd -> do
            -- Flush any remaining pending
            unless (null pending) $ do
                text <- decode tokenizer pending
                unless (T.null text) $ emitOpenAIDelta currentId text
            emitOpenAIDone currentId
            -- Reset connection on ambiguity: generate new stream ID
            newStreamId <- randomIO :: IO Word64
            pure (newStreamId, [])
            
        DecodeError err -> do
            emitOpenAIError currentId err
            go currentId pending rest
            
        AmbiguityReset reason -> do
            -- Reset on ambiguity: flush pending, emit error, get new stream ID
            unless (null pending) $ do
                text <- decode tokenizer pending
                unless (T.null text) $ emitOpenAIDelta currentId text
            emitOpenAIError currentId (T.pack $ "Ambiguity reset: " ++ show reason)
            -- Generate new stream ID to re-establish clean state
            newStreamId <- randomIO :: IO Word64
            go newStreamId [] rest

-- | Emit a single OpenAI SSE delta event
emitOpenAIDelta :: Word64 -> Text -> IO ()
emitOpenAIDelta streamId content = do
    let streamIdHex = "chatcmpl-" <> T.pack (showHex streamId "")
        payload = object
            [ "id" .= streamIdHex
            , "object" .= ("chat.completion.chunk" :: Text)
            , "choices" .= 
                [ object
                    [ "index" .= (0 :: Int)
                    , "delta" .= object ["content" .= content]
                    , "finish_reason" .= Aeson.Null
                    ]
                ]
            ]
    BS.putStr "data: "
    LBS.putStr (Aeson.encode payload)
    BS.putStr "\n\n"

-- | Emit OpenAI SSE tool_calls delta event
emitOpenAIToolCallDelta :: Word64 -> Int -> Text -> IO ()
emitOpenAIToolCallDelta streamId toolIndex arguments = do
    let streamIdHex = "chatcmpl-" <> T.pack (showHex streamId "")
        payload = object
            [ "id" .= streamIdHex
            , "object" .= ("chat.completion.chunk" :: Text)
            , "choices" .= 
                [ object
                    [ "index" .= (0 :: Int)
                    , "delta" .= object 
                        [ "tool_calls" .= 
                            [ object
                                [ "index" .= toolIndex
                                , "function" .= object
                                    [ "arguments" .= arguments
                                    ]
                                ]
                            ]
                        ]
                    , "finish_reason" .= Aeson.Null
                    ]
                ]
            ]
    BS.putStr "data: "
    LBS.putStr (Aeson.encode payload)
    BS.putStr "\n\n"

-- | Emit OpenAI SSE done event
emitOpenAIDone :: Word64 -> IO ()
emitOpenAIDone streamId = do
    let streamIdHex = "chatcmpl-" <> T.pack (showHex streamId "")
        payload = object
            [ "id" .= streamIdHex
            , "object" .= ("chat.completion.chunk" :: Text)
            , "choices" .= 
                [ object
                    [ "index" .= (0 :: Int)
                    , "delta" .= object []
                    , "finish_reason" .= ("stop" :: Text)
                    ]
                ]
            ]
    BS.putStr "data: "
    LBS.putStr (Aeson.encode payload)
    BS.putStr "\n\ndata: [DONE]\n\n"

-- | Emit OpenAI SSE error event
emitOpenAIError :: Word64 -> Text -> IO ()
emitOpenAIError _streamId err = do
    let payload = object
            [ "error" .= object
                [ "message" .= err
                , "type" .= ("server_error" :: Text)
                ]
            ]
    BS.putStr "data: "
    LBS.putStr (Aeson.encode payload)
    BS.putStr "\n\n"

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // initialization helpers
-- ════════════════════════════════════════════════════════════════════════════

printBanner :: (KatipContext m) => JackOptions -> m ()
printBanner _ = do
    logFM InfoS "  ╷┌─┐┐ ┬┬  ┌─┐┌┐┐┌─┐  ┐─┐┬  o┬─┐┌─┐"
    logFM InfoS "  ││─┤└┬┘│  ├─ │││├─   └─┐│  ││ │├─ "
    logFM InfoS "╶─┘┘ ┴ ┴ ┘─┘┴─┘┘└┘┴─┘  ──┘┘─┘┘┘─┘┴─┘"
    logFM InfoS ""

    logFM InfoS "    \"I'm Slide,” the figure said, hands on its hips, “Jaylene. You don't fuck"
    logFM InfoS "     with me. Nobody in L.A.” she gestured, a window suddenly snapping into"
    logFM InfoS "     existence behind her “fucks with me. You got that?\""
    logFM InfoS ""
    logFM InfoS "                                                           — Neuromancer"
    logFM InfoS ""

    -- We print resolved endpoint later

resolveHotTable :: JackOptions -> Maybe FilePath -> IO HotTable
resolveHotTable options resolvedPath = case resolvedPath of
    Just tablePath -> loadHotTable tablePath
    Nothing -> case jackHotTable options of
        Just cliPath -> loadHotTable cliPath
        Nothing -> pure defaultHotTable

-- | Create boundary token set for semantic chunking
createBoundaryTokenSet :: HFTokenizer -> IO (VU.Vector Bool)
createBoundaryTokenSet tokenizer = do
    -- Common boundary characters
    let boundaries = ["\n", ";", "}", ")", "]"]

    -- Resolve IDs for these tokens
    boundaryIds <- mapM (tokenToId tokenizer) boundaries

    let maxTokenId = 256 * 1024

    pure $ VU.generate maxTokenId $ \index ->
        let tokenId = fromIntegral index
         in Just tokenId `elem` boundaryIds

-- | Special token configuration
data SpecialTokenConfig = SpecialTokenConfig
    { specialThinkStart :: !Word32
    , specialThinkEnd :: !Word32
    , specialToolStart :: !Word32
    , specialToolEnd :: !Word32
    , specialCodeFence :: !Word32
    }

createSpecialTokenConfig :: HFTokenizer -> Config.Delimiters -> IO SpecialTokenConfig
createSpecialTokenConfig tokenizer delimiters = do
    -- Helper to resolve token or return 0 (unk) if missing
    let resolveTokenId maybeText = case maybeText of
            Just text -> do
                maybeId <- tokenToId tokenizer text
                case maybeId of
                    Just tokenId -> pure tokenId
                    Nothing -> pure 0 -- Fallback to 0 if token not in vocab
            Nothing -> pure 0
            
    thinkStart <- resolveTokenId (Config.think_start delimiters)
    thinkEnd <- resolveTokenId (Config.think_end delimiters)
    toolStart <- resolveTokenId (Config.tool_start delimiters)
    toolEnd <- resolveTokenId (Config.tool_end delimiters)

    -- Code fence is mandatory Text in config
    maybeFenceId <- tokenToId tokenizer (Config.code_fence delimiters)
    let codeFence = fromMaybe 0 maybeFenceId

    pure $
        SpecialTokenConfig
            { specialThinkStart = thinkStart
            , specialThinkEnd = thinkEnd
            , specialToolStart = toolStart
            , specialToolEnd = toolEnd
            , specialCodeFence = codeFence
            }

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // main processing loop
-- ════════════════════════════════════════════════════════════════════════════

data ActiveConnection
    = ConnOpenAI OpenAIConnection
    | ConnOpenRouter OpenRouter.OpenRouterConnection
    | ConnVertexAnthropic VertexAnthropic.VertexAnthropicConnection

runPromptLoop ::
    (KatipContext m) =>
    JackOptions ->
    ActiveConnection ->
    Text ->
    -- ^ Model name for stream metadata
    HFTokenizer ->
    HotTable ->
    VU.Vector Bool ->
    SpecialTokenConfig ->
    Socket Pub ->
    Metrics ->
    m ()
runPromptLoop options connection modelName tokenizer hotTable boundaryTokens specialTokens publisherSocket metrics = loop
  where
    loop = do
        end <- liftIO isEOF
        if end
            then logFM InfoS "EOF received, exiting."
            else do
                userPrompt <- liftIO TIO.getLine
                unless (T.null userPrompt) $ do
                    when (jackVerbose options) $
                        logFM InfoS $
                            ls $
                                ">> " <> T.unpack userPrompt

                    processPrompt options connection modelName tokenizer hotTable boundaryTokens specialTokens publisherSocket metrics userPrompt
                loop

processPrompt ::
    (KatipContext m) =>
    JackOptions ->
    ActiveConnection ->
    Text ->
    -- ^ Model name for metadata
    HFTokenizer ->
    HotTable ->
    VU.Vector Bool ->
    SpecialTokenConfig ->
    Socket Pub ->
    Metrics ->
    Text ->
    m ()
processPrompt options activeConnection modelName tokenizer hotTable boundaryTokens specialTokens publisherSocket metrics userPrompt = do
    frameBuilder <- liftIO $ newFrameBuilder (64 * 1024)

    let initialChunkState =
            initChunkState
                frameBuilder
                hotTable
                boundaryTokens
                (specialThinkStart specialTokens, specialThinkEnd specialTokens)
                (specialToolStart specialTokens, specialToolEnd specialTokens)
                (specialCodeFence specialTokens)
                (jackFlushThreshold options)

    chunkStateRef <- liftIO $ newIORef initialChunkState

    -- Generate session identifiers (random 64-bit hex strings)
    randomSlideId <- liftIO (randomIO :: IO Word64)
    randomHttpId <- liftIO (randomIO :: IO Word64)
    let toHexText word = T.pack $ showHex word ""
        slideId = toHexText randomSlideId
        httpId = toHexText randomHttpId

    -- Create stream metadata for ZMQ messages
    timestamp <- liftIO getPOSIXTime
    let streamId = fromMaybe slideId (jackStreamId options)
        meta = StreamMetadata
            { metaStreamId = streamId
            , metaModel = modelName
            , metaTimestamp = realToFrac timestamp
            }

    -- Add IDs to logging context
    katipAddContext (sl "slide_id" slideId <> sl "http_id" httpId) $ do
        currentLogEnv <- getLogEnv
        currentKatipContext <- getKatipContext
        currentNamespace <- getKatipNamespace

        let logAction :: Severity -> Text -> IO ()
            logAction severity message = runKatipContextT currentLogEnv currentKatipContext currentNamespace $ logFM severity (ls message)

        -- Track tool call state
        activeToolCall <- liftIO $ newIORef Nothing

        case activeConnection of
            ConnOpenAI openAIConn -> liftIO $
                streamCompletion
                    openAIConn
                    userPrompt
                    defaultStreamConfig
                    (handleStreamEvent options meta tokenizer chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (handleStreamFinish options meta chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (logAction DebugS)
            ConnOpenRouter openRouterConn -> liftIO $
                OpenRouter.streamCompletion
                    openRouterConn
                    userPrompt
                    defaultStreamConfig
                    (handleStreamEvent options meta tokenizer chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (handleStreamFinish options meta chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (logAction DebugS)
            ConnVertexAnthropic vertexConn -> liftIO $
                VertexAnthropic.streamCompletion
                    vertexConn
                    userPrompt
                    defaultStreamConfig
                    (handleStreamEvent options meta tokenizer chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (handleStreamFinish options meta chunkStateRef activeToolCall publisherSocket metrics logAction)
                    (logAction DebugS)

handleStreamEvent ::
    JackOptions ->
    StreamMetadata ->
    HFTokenizer ->
    IORef ChunkState ->
    IORef (Maybe Int) -> -- Active tool call index
    Socket Pub ->
    Metrics ->
    (Severity -> Text -> IO ()) ->
    StreamEvent ->
    IO ()
handleStreamEvent options meta tokenizer chunkStateRef activeToolCallRef publisherSocket metrics logger event = case event of
    EventContent contentDelta -> do
        -- If we were in a tool call, close it
        maybeActive <- readIORef activeToolCallRef
        case maybeActive of
            Just _ -> do
                -- Close tool call
                emitControlFrame publisherSocket meta metrics logger OP_TOOL_CALL_END
                writeIORef activeToolCallRef Nothing
            Nothing -> pure ()

        -- Handle content normally
        handleContentDelta options meta tokenizer chunkStateRef publisherSocket metrics logger contentDelta

    EventToolCall delta -> do
        -- Flush any pending text chunk first
        state <- readIORef chunkStateRef
        maybeFrame <- flushTextChunk state
        case maybeFrame of
            Just frame -> emitFrame publisherSocket meta metrics logger frame
            Nothing -> pure ()
        
        -- Check if we need to start a new tool call
        maybeActive <- readIORef activeToolCallRef
        let toolCallIndex = tcIndex delta

        case maybeActive of
            Just activeIndex | activeIndex == toolCallIndex -> pure () -- Continue
            Just _ -> do
                -- Close previous tool call, start new one
                emitControlFrame publisherSocket meta metrics logger OP_TOOL_CALL_END
                emitControlFrame publisherSocket meta metrics logger OP_TOOL_CALL_START
                writeIORef activeToolCallRef (Just toolCallIndex)
            Nothing -> do
                -- Start new tool call
                emitControlFrame publisherSocket meta metrics logger OP_TOOL_CALL_START
                writeIORef activeToolCallRef (Just toolCallIndex)

        -- Emit content
        -- We construct a JSON fragment for the token stream
        -- Ideally this would be robust JSON construction
        let content = buildToolCallContent delta
        unless (T.null content) $ do
             handleRawTokens options meta tokenizer publisherSocket metrics logger content

buildToolCallContent :: ToolCallDelta -> Text
buildToolCallContent delta =
    let namePart = case tcName delta of
            Just name -> "{\"name\": \"" <> name <> "\", \"arguments\": \""
            Nothing -> ""
        argumentsPart = fromMaybe "" (tcArgs delta)
        -- human: hacky JSON reconstruction, but matches streaming reality
    in namePart <> argumentsPart

handleContentDelta ::
    JackOptions ->
    StreamMetadata ->
    HFTokenizer ->
    IORef ChunkState ->
    Socket Pub ->
    Metrics ->
    (Severity -> Text -> IO ()) ->
    Text ->
    IO ()
handleContentDelta options meta tokenizer chunkStateRef publisherSocket metrics logger contentDelta = do
    -- Log the raw delta
    when (jackVerbose options) $
        logger DebugS $
            "delta: " <> T.replace "\n" "\\n" contentDelta

    tokenIds <- encode tokenizer contentDelta
    _ <- P.addCounter (metricsTokensProcessed metrics) (fromIntegral $ length tokenIds)

    mapM_ (processAndEmitToken options meta chunkStateRef publisherSocket metrics logger) tokenIds

handleRawTokens ::
    JackOptions ->
    StreamMetadata ->
    HFTokenizer ->
    Socket Pub ->
    Metrics ->
    (Severity -> Text -> IO ()) ->
    Text ->
    IO ()
handleRawTokens _options meta tokenizer publisherSocket metrics logger content = do
    -- Bypass chunk state, just emit tokens
    tokenIds <- encode tokenizer content
    _ <- P.addCounter (metricsTokensProcessed metrics) (fromIntegral $ length tokenIds)
    
    -- We need a temporary builder to pack these tokens into frames
    -- Since we're inside a tool call block (delimited by control frames), 
    -- we can just emit extended/hot tokens directly.
    --                                                                       // but
    
    -- Use a fresh builder for this batch
    builder <- newFrameBuilder (64 * 1024)
    -- We assume the hot table is the same... strictly we should use the one in ChunkState
    -- but for now let's just use extended tokens to be safe/simple, or pass HotTable.
    -- Actually, let's just write extended tokens for now.
    
    mapM_ (writeExtendedToken builder) tokenIds
    
    -- Finish and send
    frameLength <- builderLength builder
    when (frameLength > 0) $ do
        frame <- finishFrame builder
        emitFrame publisherSocket meta metrics logger frame

-- | Emit frame with metadata using ZMQ multipart message
-- Format: [topic] [metadata_json] [frame_bytes]
emitFrame :: Socket Pub -> StreamMetadata -> Metrics -> (Severity -> Text -> IO ()) -> Frame -> IO ()
emitFrame publisherSocket meta metrics logger frame = do
    let bytes = frameBytes frame
        byteCount = BS.length bytes
        topic = modelToTopic (metaModel meta)
        metaJson = BS.toStrict $ Aeson.encode meta

    logger DebugS $ "-> frame (" <> T.pack (show byteCount) <> " bytes)"

    -- Send multipart: [topic, metadata, frame]
    sendMulti publisherSocket (topic :| [metaJson, bytes])
    P.incCounter (metricsFramesEmitted metrics)
    _ <- P.addCounter (metricsBytesEmitted metrics) (fromIntegral byteCount)
    pure ()

emitControlFrame :: Socket Pub -> StreamMetadata -> Metrics -> (Severity -> Text -> IO ()) -> Slide.Wire.Frame.FrameOp -> IO ()
emitControlFrame publisherSocket meta metrics logger frameOp = do
    builder <- newFrameBuilder 128
    writeControl builder frameOp
    frame <- finishFrame builder
    emitFrame publisherSocket meta metrics logger frame

processAndEmitToken ::
    JackOptions ->
    StreamMetadata ->
    IORef ChunkState ->
    Socket Pub ->
    Metrics ->
    (Severity -> Text -> IO ()) ->
    Word32 ->
    IO ()
processAndEmitToken options meta chunkStateRef publisherSocket metrics logger tokenId = do
    currentState <- readIORef chunkStateRef
    (updatedState, processingResult) <- processToken currentState tokenId
    writeIORef chunkStateRef updatedState

    case processingResult of
        ResultEmitChunk completedFrame -> do
            emitFrame publisherSocket meta metrics logger completedFrame
            when (jackVerbose options) $
                logger InfoS "<- chunk frame"
        ResultStateChange _controlOp -> pure ()
        ResultContinue -> pure ()

handleStreamFinish ::
    JackOptions ->
    StreamMetadata ->
    IORef ChunkState ->
    IORef (Maybe Int) ->
    Socket Pub ->
    Metrics ->
    (Severity -> Text -> IO ()) ->
    IO ()
handleStreamFinish options meta chunkStateRef activeToolCallRef publisherSocket metrics logger = do
    -- Close active tool call if any
    maybeActive <- readIORef activeToolCallRef
    case maybeActive of
        Just _ -> emitControlFrame publisherSocket meta metrics logger OP_TOOL_CALL_END
        Nothing -> pure ()

    finalState <- readIORef chunkStateRef
    finalFrame <- finalizeChunk finalState

    emitFrame publisherSocket meta metrics logger finalFrame

    when (jackVerbose options) $
        logger InfoS "<- stream end"
