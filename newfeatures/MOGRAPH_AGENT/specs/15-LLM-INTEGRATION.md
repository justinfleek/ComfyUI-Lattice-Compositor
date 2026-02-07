# Specification 15: LLM Integration
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-15  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines the integration layer between Large Language Models and the Lottie generation engine. It covers:

1. **Prompt engineering** (system prompts, few-shot examples)
2. **Response parsing** (SAM extraction, validation)
3. **Error recovery** (retry logic, fallbacks)
4. **Multi-provider support** (OpenAI, Anthropic, local models)
5. **Determinism guarantees** (seeded sampling, caching)

---

## 2. Architecture

### 2.1 System Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                        User Interface                            │
│                    "A red ball bouncing"                         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Prompt Processor                             │
│  • Normalize input                                               │
│  • Extract context                                               │
│  • Build system prompt                                           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      LLM Gateway                                 │
│  • Provider abstraction                                          │
│  • Rate limiting                                                 │
│  • Retry logic                                                   │
│  • Response caching                                              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Response Parser                               │
│  • JSON extraction                                               │
│  • SAM validation                                                │
│  • Error detection                                               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     SAM Compiler                                 │
│  • Lottie generation                                             │
│  • Keyframe optimization                                         │
│  • Output validation                                             │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 Data Flow

```haskell
-- | Complete pipeline type
type AnimationPipeline = 
  UserPrompt -> IO (Either PipelineError LottieAnimation)

-- | Pipeline stages
data PipelineStage
  = StagePromptProcessing
  | StageLLMRequest
  | StageResponseParsing
  | StageSAMValidation
  | StageLottieCompilation
  deriving (Eq, Show, Enum, Bounded)

-- | Pipeline error with stage information
data PipelineError = PipelineError
  { peStage   :: !PipelineStage
  , peMessage :: !Text
  , peContext :: !(Maybe Value)  -- Additional context
  , peRetryable :: !Bool
  } deriving (Eq, Show)
```

---

## 3. Prompt Engineering

### 3.1 System Prompt Template

```haskell
-- | System prompt components
data SystemPromptConfig = SystemPromptConfig
  { spcRole        :: !Text          -- AI role description
  , spcTask        :: !Text          -- Task description
  , spcConstraints :: ![Text]        -- Output constraints
  , spcSchema      :: !Text          -- SAM JSON schema
  , spcExamples    :: ![PromptExample]  -- Few-shot examples
  , spcOutputFormat :: !Text         -- Expected output format
  } deriving (Eq, Show)

-- | Build complete system prompt
buildSystemPrompt :: SystemPromptConfig -> Text
buildSystemPrompt cfg = T.unlines
  [ "# Role"
  , spcRole cfg
  , ""
  , "# Task"
  , spcTask cfg
  , ""
  , "# Constraints"
  , T.unlines $ map ("- " <>) (spcConstraints cfg)
  , ""
  , "# Output Schema"
  , "```json"
  , spcSchema cfg
  , "```"
  , ""
  , "# Examples"
  , T.unlines $ map formatExample (spcExamples cfg)
  , ""
  , "# Output Format"
  , spcOutputFormat cfg
  ]

-- | Default system prompt for animation generation
defaultSystemPrompt :: Text
defaultSystemPrompt = buildSystemPrompt SystemPromptConfig
  { spcRole = T.unlines
      [ "You are an expert animation designer that converts natural language"
      , "descriptions into structured animation specifications."
      , "You have deep knowledge of motion graphics, animation principles,"
      , "and the Lottie animation format."
      ]
  
  , spcTask = T.unlines
      [ "Convert the user's animation description into a Semantic Animation Model (SAM)"
      , "JSON document. The SAM will be compiled into a Lottie animation."
      , ""
      , "Your job is to:"
      , "1. Identify all visual subjects (shapes, text, images)"
      , "2. Determine their properties (color, size, position)"
      , "3. Define the animations/actions to apply"
      , "4. Specify timing and easing"
      ]
  
  , spcConstraints = 
      [ "ALL numeric values MUST be within specified bounds"
      , "ALL IDs must be unique strings"
      , "ALL action targets must reference existing subject IDs"
      , "Duration must be positive (minimum 0.001 seconds)"
      , "Colors can be named (red, blue) or hex (#ff0000)"
      , "Easing can be preset names or custom cubic-bezier"
      , "Output ONLY valid JSON, no explanations"
      ]
  
  , spcSchema = samJsonSchemaCompact
  
  , spcExamples = defaultExamples
  
  , spcOutputFormat = T.unlines
      [ "Respond with ONLY the SAM JSON document."
      , "Do not include any text before or after the JSON."
      , "Do not use markdown code blocks."
      , "The response must be valid, parseable JSON."
      ]
  }
```

### 3.2 Few-Shot Examples

```haskell
-- | Prompt example (input/output pair)
data PromptExample = PromptExample
  { peInput  :: !Text  -- User prompt
  , peOutput :: !Text  -- Expected SAM JSON
  , peNote   :: !(Maybe Text)  -- Explanation (not sent to LLM)
  } deriving (Eq, Show)

-- | Format example for prompt
formatExample :: PromptExample -> Text
formatExample ex = T.unlines
  [ "Input: " <> peInput ex
  , "Output:"
  , peOutput ex
  , ""
  ]

-- | Default few-shot examples
defaultExamples :: [PromptExample]
defaultExamples = 
  [ bounceExample
  , fadeExample
  , multipleShapesExample
  , logoRevealExample
  , textAnimationExample
  ]

bounceExample :: PromptExample
bounceExample = PromptExample
  { peInput = "A red ball bouncing three times"
  , peOutput = T.unlines
      [ "{"
      , "  \"canvas\": {\"width\": 1920, \"height\": 1080, \"fps\": 60, \"duration\": 3},"
      , "  \"subjects\": ["
      , "    {"
      , "      \"id\": \"ball\","
      , "      \"type\": \"ellipse\","
      , "      \"geometry\": {\"width\": 100, \"height\": 100},"
      , "      \"fill\": {\"color\": \"red\", \"opacity\": 100},"
      , "      \"transform\": {\"position\": [960, 200]}"
      , "    }"
      , "  ],"
      , "  \"actions\": ["
      , "    {"
      , "      \"id\": \"bounce\","
      , "      \"type\": \"bounce\","
      , "      \"target\": \"ball\","
      , "      \"startTime\": 0,"
      , "      \"duration\": 3,"
      , "      \"params\": {\"bounces\": 3, \"decay\": 0.6},"
      , "      \"easing\": \"easeOutBounce\""
      , "    }"
      , "  ],"
      , "  \"timing\": {\"mode\": \"sequential\"}"
      , "}"
      ]
  , peNote = Just "Simple single-subject bounce animation"
  }

fadeExample :: PromptExample
fadeExample = PromptExample
  { peInput = "A blue square fading in"
  , peOutput = T.unlines
      [ "{"
      , "  \"canvas\": {\"width\": 1920, \"height\": 1080, \"fps\": 60, \"duration\": 1},"
      , "  \"subjects\": ["
      , "    {"
      , "      \"id\": \"square\","
      , "      \"type\": \"rectangle\","
      , "      \"geometry\": {\"width\": 200, \"height\": 200, \"cornerRadius\": 0},"
      , "      \"fill\": {\"color\": \"blue\", \"opacity\": 100},"
      , "      \"transform\": {\"position\": [960, 540], \"opacity\": 0}"
      , "    }"
      , "  ],"
      , "  \"actions\": ["
      , "    {"
      , "      \"id\": \"fade\","
      , "      \"type\": \"fadeIn\","
      , "      \"target\": \"square\","
      , "      \"startTime\": 0,"
      , "      \"duration\": 1,"
      , "      \"easing\": \"easeOutCubic\""
      , "    }"
      , "  ],"
      , "  \"timing\": {\"mode\": \"sequential\"}"
      , "}"
      ]
  , peNote = Just "Simple fade animation"
  }

multipleShapesExample :: PromptExample
multipleShapesExample = PromptExample
  { peInput = "Three circles appearing one after another from left to right"
  , peOutput = T.unlines
      [ "{"
      , "  \"canvas\": {\"width\": 1920, \"height\": 1080, \"fps\": 60, \"duration\": 2},"
      , "  \"subjects\": ["
      , "    {\"id\": \"c1\", \"type\": \"ellipse\", \"geometry\": {\"width\": 80, \"height\": 80},"
      , "     \"fill\": {\"color\": \"#3498db\"}, \"transform\": {\"position\": [480, 540], \"scale\": [0, 0]}},"
      , "    {\"id\": \"c2\", \"type\": \"ellipse\", \"geometry\": {\"width\": 80, \"height\": 80},"
      , "     \"fill\": {\"color\": \"#e74c3c\"}, \"transform\": {\"position\": [960, 540], \"scale\": [0, 0]}},"
      , "    {\"id\": \"c3\", \"type\": \"ellipse\", \"geometry\": {\"width\": 80, \"height\": 80},"
      , "     \"fill\": {\"color\": \"#2ecc71\"}, \"transform\": {\"position\": [1440, 540], \"scale\": [0, 0]}}"
      , "  ],"
      , "  \"actions\": ["
      , "    {\"id\": \"a1\", \"type\": \"scaleTo\", \"target\": \"c1\", \"startTime\": 0, \"duration\": 0.4,"
      , "     \"params\": {\"scaleX\": 100, \"scaleY\": 100}, \"easing\": \"easeOutBack\"},"
      , "    {\"id\": \"a2\", \"type\": \"scaleTo\", \"target\": \"c2\", \"startTime\": 0.3, \"duration\": 0.4,"
      , "     \"params\": {\"scaleX\": 100, \"scaleY\": 100}, \"easing\": \"easeOutBack\"},"
      , "    {\"id\": \"a3\", \"type\": \"scaleTo\", \"target\": \"c3\", \"startTime\": 0.6, \"duration\": 0.4,"
      , "     \"params\": {\"scaleX\": 100, \"scaleY\": 100}, \"easing\": \"easeOutBack\"}"
      , "  ],"
      , "  \"timing\": {\"mode\": \"stagger\", \"stagger\": 0.3}"
      , "}"
      ]
  , peNote = Just "Multiple subjects with staggered timing"
  }
```

---

## 4. LLM Provider Abstraction

### 4.1 Provider Interface

```haskell
-- | LLM provider abstraction
class LLMProvider p where
  -- | Send completion request
  complete :: p -> CompletionRequest -> IO (Either LLMError CompletionResponse)
  
  -- | Provider name for logging
  providerName :: p -> Text
  
  -- | Check if provider is available
  isAvailable :: p -> IO Bool
  
  -- | Get rate limit status
  rateLimitStatus :: p -> IO RateLimitStatus

-- | Completion request
data CompletionRequest = CompletionRequest
  { crSystemPrompt :: !Text
  , crUserPrompt   :: !Text
  , crMaxTokens    :: !Int
  , crTemperature  :: !Double
  , crSeed         :: !(Maybe Int)  -- For determinism
  , crStopSequences :: ![Text]
  } deriving (Eq, Show)

-- | Completion response
data CompletionResponse = CompletionResponse
  { crContent      :: !Text
  , crFinishReason :: !FinishReason
  , crUsage        :: !TokenUsage
  , crModelId      :: !Text
  } deriving (Eq, Show)

data FinishReason = FinishStop | FinishLength | FinishError Text
  deriving (Eq, Show)

data TokenUsage = TokenUsage
  { tuPromptTokens     :: !Int
  , tuCompletionTokens :: !Int
  , tuTotalTokens      :: !Int
  } deriving (Eq, Show)

-- | LLM errors
data LLMError
  = LLMErrRateLimit !Int  -- Retry after seconds
  | LLMErrTimeout
  | LLMErrInvalidResponse !Text
  | LLMErrProviderDown
  | LLMErrQuotaExceeded
  | LLMErrInvalidRequest !Text
  deriving (Eq, Show)

-- | Rate limit status
data RateLimitStatus = RateLimitStatus
  { rlsRequestsRemaining :: !Int
  , rlsTokensRemaining   :: !Int
  , rlsResetTime         :: !(Maybe UTCTime)
  } deriving (Eq, Show)
```

### 4.2 Provider Implementations

```haskell
-- | OpenAI provider
data OpenAIProvider = OpenAIProvider
  { oaiApiKey    :: !Text
  , oaiModel     :: !Text
  , oaiBaseUrl   :: !Text
  , oaiOrgId     :: !(Maybe Text)
  } deriving (Eq, Show)

instance LLMProvider OpenAIProvider where
  complete p req = do
    let body = object
          [ "model" .= oaiModel p
          , "messages" .= 
              [ object ["role" .= ("system" :: Text), "content" .= crSystemPrompt req]
              , object ["role" .= ("user" :: Text), "content" .= crUserPrompt req]
              ]
          , "max_tokens" .= crMaxTokens req
          , "temperature" .= crTemperature req
          , "seed" .= crSeed req
          ]
    
    response <- httpJSON $ setRequestBodyJSON body
                         $ setRequestHeader "Authorization" ["Bearer " <> encodeUtf8 (oaiApiKey p)]
                         $ parseRequest_ (T.unpack $ oaiBaseUrl p <> "/chat/completions")
    
    parseOpenAIResponse response
  
  providerName _ = "OpenAI"
  
  isAvailable p = do
    result <- try $ complete p testRequest
    pure $ isRight result
    where
      testRequest = CompletionRequest "test" "test" 1 0 Nothing []

-- | Anthropic provider
data AnthropicProvider = AnthropicProvider
  { antApiKey  :: !Text
  , antModel   :: !Text
  , antBaseUrl :: !Text
  } deriving (Eq, Show)

instance LLMProvider AnthropicProvider where
  complete p req = do
    let body = object
          [ "model" .= antModel p
          , "system" .= crSystemPrompt req
          , "messages" .= 
              [ object ["role" .= ("user" :: Text), "content" .= crUserPrompt req]
              ]
          , "max_tokens" .= crMaxTokens req
          , "temperature" .= crTemperature req
          ]
    
    response <- httpJSON $ setRequestBodyJSON body
                         $ setRequestHeader "x-api-key" [encodeUtf8 (antApiKey p)]
                         $ setRequestHeader "anthropic-version" ["2024-01-01"]
                         $ parseRequest_ (T.unpack $ antBaseUrl p <> "/messages")
    
    parseAnthropicResponse response
  
  providerName _ = "Anthropic"

-- | Local model provider (e.g., Ollama)
data LocalProvider = LocalProvider
  { locModel   :: !Text
  , locBaseUrl :: !Text
  } deriving (Eq, Show)

instance LLMProvider LocalProvider where
  complete p req = do
    let body = object
          [ "model" .= locModel p
          , "prompt" .= (crSystemPrompt req <> "\n\nUser: " <> crUserPrompt req)
          , "stream" .= False
          , "options" .= object
              [ "temperature" .= crTemperature req
              , "num_predict" .= crMaxTokens req
              , "seed" .= crSeed req
              ]
          ]
    
    response <- httpJSON $ setRequestBodyJSON body
                         $ parseRequest_ (T.unpack $ locBaseUrl p <> "/api/generate")
    
    parseOllamaResponse response
  
  providerName _ = "Local"
```

---

## 5. Response Parsing

### 5.1 JSON Extraction

```haskell
-- | Extract JSON from LLM response
extractJSON :: Text -> Either ParseError Value
extractJSON response = 
  -- Try direct parse first
  case eitherDecodeStrict (encodeUtf8 response) of
    Right json -> Right json
    Left _ -> 
      -- Try to find JSON in the response
      case findJSONInText response of
        Just jsonText -> 
          case eitherDecodeStrict (encodeUtf8 jsonText) of
            Right json -> Right json
            Left err -> Left $ ParseError err
        Nothing -> Left $ ParseError "No valid JSON found in response"

-- | Find JSON object in text (handles markdown code blocks, etc.)
findJSONInText :: Text -> Maybe Text
findJSONInText txt = 
  -- Try various extraction strategies
  asum
    [ extractFromCodeBlock txt
    , extractBracketedJSON txt
    , extractRawJSON txt
    ]

-- | Extract from ```json ... ``` blocks
extractFromCodeBlock :: Text -> Maybe Text
extractFromCodeBlock txt =
  let patterns = ["```json\n", "```\n{"]
  in asum $ map (\p -> extractBetween p "```" txt) patterns

-- | Extract from first { to last }
extractBracketedJSON :: Text -> Maybe Text
extractBracketedJSON txt = do
  let start = T.findIndex (== '{') txt
      end = T.findLastIndex (== '}') txt
  case (start, end) of
    (Just s, Just e) | s < e -> Just $ T.drop s $ T.take (e + 1) txt
    _ -> Nothing

-- | Validate extracted JSON is a SAM document
validateSAMJSON :: Value -> Either SAMError SAMDocument
validateSAMJSON json = do
  -- Parse to SAMDocument
  doc <- case fromJSON json of
    Success d -> Right d
    Error err -> Left $ SAMErrInvalidJSON err
  
  -- Validate the document
  case validateSAM doc of
    Right valid -> Right valid
    Left errors -> Left $ SAMErrValidation errors
```

### 5.2 Error Recovery

```haskell
-- | Retry configuration
data RetryConfig = RetryConfig
  { rcMaxRetries     :: !Int
  , rcInitialDelay   :: !Int  -- Milliseconds
  , rcMaxDelay       :: !Int  -- Milliseconds
  , rcBackoffFactor  :: !Double
  , rcRetryOn        :: !(LLMError -> Bool)
  } deriving (Eq, Show)

defaultRetryConfig :: RetryConfig
defaultRetryConfig = RetryConfig
  { rcMaxRetries = 3
  , rcInitialDelay = 1000
  , rcMaxDelay = 30000
  , rcBackoffFactor = 2.0
  , rcRetryOn = \case
      LLMErrRateLimit _ -> True
      LLMErrTimeout -> True
      LLMErrProviderDown -> True
      _ -> False
  }

-- | Execute with retries
withRetries :: RetryConfig -> IO (Either LLMError a) -> IO (Either LLMError a)
withRetries cfg action = go 0 (rcInitialDelay cfg)
  where
    go attempt delay
      | attempt >= rcMaxRetries cfg = action
      | otherwise = do
          result <- action
          case result of
            Right _ -> pure result
            Left err | rcRetryOn cfg err -> do
              threadDelay (delay * 1000)
              go (attempt + 1) (min (rcMaxDelay cfg) (round $ fromIntegral delay * rcBackoffFactor cfg))
            Left err -> pure $ Left err

-- | Error recovery strategies
data RecoveryStrategy
  = RSRetry                    -- Retry with same prompt
  | RSSimplifyPrompt           -- Try simplified prompt
  | RSFallbackProvider         -- Try different provider
  | RSReturnPartial            -- Return partial result
  | RSFail                     -- Give up
  deriving (Eq, Show)

-- | Determine recovery strategy for error
selectRecoveryStrategy :: LLMError -> Int -> RecoveryStrategy
selectRecoveryStrategy err attempts = case err of
  LLMErrRateLimit _ 
    | attempts < 3 -> RSRetry
    | otherwise -> RSFallbackProvider
  
  LLMErrTimeout
    | attempts < 2 -> RSRetry
    | otherwise -> RSSimplifyPrompt
  
  LLMErrInvalidResponse _
    | attempts < 2 -> RSRetry
    | otherwise -> RSSimplifyPrompt
  
  LLMErrProviderDown -> RSFallbackProvider
  
  LLMErrQuotaExceeded -> RSFallbackProvider
  
  LLMErrInvalidRequest _ -> RSFail

-- | Simplify prompt for retry
simplifyPrompt :: Text -> Text
simplifyPrompt prompt = 
  -- Remove complex details, keep core request
  let simplified = T.unwords $ take 20 $ T.words prompt
  in simplified <> " (keep it simple)"
```

---

## 6. Determinism Guarantees

### 6.1 Seeded Generation

```haskell
-- | Deterministic generation config
data DeterministicConfig = DeterministicConfig
  { dcSeed        :: !Int           -- RNG seed
  , dcTemperature :: !Double        -- Should be 0 for determinism
  , dcCacheKey    :: !(Maybe Text)  -- For response caching
  } deriving (Eq, Show)

-- | Generate with determinism guarantees
generateDeterministic :: 
  LLMProvider p => 
  p -> 
  DeterministicConfig -> 
  Text -> 
  IO (Either PipelineError SAMDocument)
generateDeterministic provider cfg prompt = do
  -- Check cache first
  cached <- case dcCacheKey cfg of
    Just key -> lookupCache key
    Nothing -> pure Nothing
  
  case cached of
    Just doc -> pure $ Right doc
    Nothing -> do
      -- Make deterministic request
      let req = CompletionRequest
            { crSystemPrompt = defaultSystemPrompt
            , crUserPrompt = prompt
            , crMaxTokens = 4096
            , crTemperature = dcTemperature cfg  -- 0 for determinism
            , crSeed = Just (dcSeed cfg)
            , crStopSequences = []
            }
      
      result <- complete provider req
      
      case result of
        Left err -> pure $ Left $ PipelineError StageLLMRequest (show err) Nothing True
        Right response -> do
          -- Parse and validate
          case extractJSON (crContent response) >>= validateSAMJSON of
            Left err -> pure $ Left $ PipelineError StageResponseParsing (show err) Nothing True
            Right doc -> do
              -- Cache result
              case dcCacheKey cfg of
                Just key -> cacheResult key doc
                Nothing -> pure ()
              pure $ Right doc

-- | Cache implementation
type ResponseCache = MVar (Map Text (SAMDocument, UTCTime))

lookupCache :: Text -> IO (Maybe SAMDocument)
lookupCache key = do
  cache <- readMVar globalCache
  case Map.lookup key cache of
    Just (doc, time) -> do
      now <- getCurrentTime
      if diffUTCTime now time < cacheExpiry
        then pure $ Just doc
        else pure Nothing
    Nothing -> pure Nothing

cacheResult :: Text -> SAMDocument -> IO ()
cacheResult key doc = do
  now <- getCurrentTime
  modifyMVar_ globalCache $ \cache ->
    pure $ Map.insert key (doc, now) cache

cacheExpiry :: NominalDiffTime
cacheExpiry = 3600  -- 1 hour
```

### 6.2 Hash-Based Caching

```haskell
-- | Generate cache key from prompt and config
generateCacheKey :: Text -> DeterministicConfig -> Text
generateCacheKey prompt cfg = 
  let input = T.concat
        [ prompt
        , T.pack $ show (dcSeed cfg)
        , T.pack $ show (dcTemperature cfg)
        ]
      hash = SHA256.hash $ encodeUtf8 input
  in decodeUtf8 $ Base16.encode hash

-- | Verify determinism (debug mode)
verifyDeterminism :: 
  LLMProvider p => 
  p -> 
  Text -> 
  Int ->  -- Number of runs
  IO Bool
verifyDeterminism provider prompt runs = do
  let cfg = DeterministicConfig 42 0 Nothing
  results <- replicateM runs $ generateDeterministic provider cfg prompt
  
  case sequence results of
    Left _ -> pure False
    Right docs -> pure $ allSame docs
  where
    allSame [] = True
    allSame (x:xs) = all (== x) xs
```

---

## 7. Complete Pipeline Implementation

### 7.1 Pipeline Monad

```haskell
-- | Pipeline monad with logging and metrics
newtype Pipeline a = Pipeline 
  { runPipeline :: ReaderT PipelineEnv (ExceptT PipelineError IO) a }
  deriving (Functor, Applicative, Monad, MonadIO, 
            MonadReader PipelineEnv, MonadError PipelineError)

data PipelineEnv = PipelineEnv
  { peProvider    :: !SomeLLMProvider
  , peRetryConfig :: !RetryConfig
  , peLogger      :: !Logger
  , peMetrics     :: !MetricsCollector
  , peCache       :: !ResponseCache
  }

-- | Existential wrapper for any provider
data SomeLLMProvider = forall p. LLMProvider p => SomeLLMProvider p

-- | Run the pipeline
executePipeline :: PipelineEnv -> Text -> IO (Either PipelineError LottieAnimation)
executePipeline env prompt = 
  runExceptT $ runReaderT (runPipeline $ fullPipeline prompt) env

-- | Full pipeline implementation
fullPipeline :: Text -> Pipeline LottieAnimation
fullPipeline prompt = do
  -- Stage 1: Process prompt
  logStage StagePromptProcessing
  processedPrompt <- processPrompt prompt
  
  -- Stage 2: Call LLM
  logStage StageLLMRequest
  response <- callLLMWithRetries processedPrompt
  
  -- Stage 3: Parse response
  logStage StageResponseParsing
  json <- parseResponse response
  
  -- Stage 4: Validate SAM
  logStage StageSAMValidation
  sam <- validateSAMDocument json
  
  -- Stage 5: Compile to Lottie
  logStage StageLottieCompilation
  compileSAMToLottie sam

-- | Process user prompt
processPrompt :: Text -> Pipeline Text
processPrompt prompt = do
  -- Normalize whitespace
  let normalized = T.strip $ T.unwords $ T.words prompt
  
  -- Validate minimum length
  when (T.length normalized < 3) $
    throwError $ PipelineError StagePromptProcessing "Prompt too short" Nothing False
  
  -- Validate maximum length
  when (T.length normalized > 10000) $
    throwError $ PipelineError StagePromptProcessing "Prompt too long" Nothing False
  
  pure normalized

-- | Call LLM with retry logic
callLLMWithRetries :: Text -> Pipeline Text
callLLMWithRetries prompt = do
  env <- ask
  let SomeLLMProvider provider = peProvider env
  
  result <- liftIO $ withRetries (peRetryConfig env) $ do
    let req = CompletionRequest
          { crSystemPrompt = defaultSystemPrompt
          , crUserPrompt = prompt
          , crMaxTokens = 4096
          , crTemperature = 0.1
          , crSeed = Just 42
          , crStopSequences = []
          }
    complete provider req
  
  case result of
    Left err -> throwError $ PipelineError StageLLMRequest (show err) Nothing True
    Right response -> pure $ crContent response

-- | Parse and extract JSON
parseResponse :: Text -> Pipeline Value
parseResponse response = 
  case extractJSON response of
    Left err -> throwError $ PipelineError StageResponseParsing (show err) Nothing True
    Right json -> pure json

-- | Validate SAM document
validateSAMDocument :: Value -> Pipeline SAMDocument
validateSAMDocument json = do
  case fromJSON json of
    Error err -> throwError $ PipelineError StageSAMValidation err Nothing False
    Success doc -> case validateSAM doc of
      Left errors -> throwError $ PipelineError StageSAMValidation (show errors) Nothing False
      Right valid -> pure valid

-- | Compile SAM to Lottie
compileSAMToLottie :: SAMDocument -> Pipeline LottieAnimation
compileSAMToLottie sam = 
  case compileSAM sam of
    Left err -> throwError $ PipelineError StageLottieCompilation err Nothing False
    Right lottie -> pure lottie

-- | Logging helper
logStage :: PipelineStage -> Pipeline ()
logStage stage = do
  logger <- asks peLogger
  liftIO $ logInfo logger $ "Entering stage: " <> show stage
```

---

## 8. Constraint Summary

| Parameter | Min | Max | Default | Description |
|-----------|-----|-----|---------|-------------|
| Prompt length | 3 | 10000 | - | Characters |
| Max tokens | 100 | 8192 | 4096 | Response tokens |
| Temperature | 0 | 2 | 0.1 | LLM creativity |
| Seed | 0 | 2^31-1 | 42 | Determinism seed |
| Max retries | 0 | 10 | 3 | Retry attempts |
| Initial delay | 100 | 60000 | 1000 | Ms before first retry |
| Max delay | 1000 | 300000 | 30000 | Max retry delay |
| Cache expiry | 60 | 86400 | 3600 | Seconds |

---

## 9. Test Specifications

### 9.1 Unit Tests

| Test | Input | Expected |
|------|-------|----------|
| Empty prompt | "" | Error: too short |
| Simple prompt | "red ball" | Valid SAM |
| Complex prompt | Long description | Valid SAM |
| Invalid JSON response | "not json" | Parse error |
| Missing required field | Partial SAM | Validation error |
| Circular parent | Self-reference | Validation error |

### 9.2 Integration Tests

```haskell
-- | Test determinism
test_determinism :: IO ()
test_determinism = do
  env <- createTestEnv
  let prompt = "A blue circle moving right"
  
  result1 <- executePipeline env prompt
  result2 <- executePipeline env prompt
  
  assertEqual "Deterministic output" result1 result2

-- | Test retry logic
test_retry :: IO ()
test_retry = do
  -- Mock provider that fails twice then succeeds
  let mockProvider = MockProvider [Left LLMErrTimeout, Left LLMErrTimeout, Right validResponse]
  env <- createEnvWith mockProvider
  
  result <- executePipeline env "test prompt"
  
  assertRight "Should succeed after retries" result

-- | Test fallback
test_fallback :: IO ()
test_fallback = do
  -- Primary provider always fails
  -- Fallback provider succeeds
  env <- createEnvWithFallback failingProvider workingProvider
  
  result <- executePipeline env "test prompt"
  
  assertRight "Should use fallback" result
```

---

## 10. SOC2 Compliance Notes

### 10.1 Data Handling

- User prompts may contain sensitive information
- Prompts are NOT logged in production
- LLM responses are cached with encryption
- Cache keys are hashed (not reversible)

### 10.2 Audit Trail

- All API calls are logged (without prompt content)
- Token usage is tracked per user
- Error events are recorded with sanitized context
- Rate limit events are logged

### 10.3 Security Controls

- API keys stored in secure vault
- TLS 1.3 for all provider communication
- Request signing where supported
- IP allowlisting for production

---

*End of Specification 15*
