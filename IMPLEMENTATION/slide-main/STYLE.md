# straylight // production // haskell

## Why We Do What We Do

Production Haskell exists at the intersection of mathematical beauty and economic reality. We write
in a language that could express category theory but choose to express business logic instead. Not
because we can't do the former, but because making money with functional programming is the ultimate
proof of concept.

If RWST was written today, it wouldn't be a monad transformer tutorial. It would be
`ReaderT Config (ExceptT AppError (StateT Metrics IO))`, it would have structured logging,
Prometheus metrics, and compile with `-O2 -Wall -Werror`. It would process millions of events per
second while three different teams extend it without coordination. That's the gulf between academic
Haskell and production Haskell—we're not writing papers, we're writing paychecks.

This guide is for practitioners who know that `Applicative` is powerful not because it's a
mathematical abstraction, but because it makes JSON parsing composable. Who understand that `STM`
isn't beautiful because it solves the dining philosophers problem, but because it means you can
write concurrent code at 3am without creating race conditions.

We are not the same as the Haskell you learned in university. We're what happens when you take those
ideas and make them work for money.

## Core Philosophy: Optimize for Disambiguation

In modern codebases where agents generate significant amounts of code, traditional economics invert:

- Code is written once by agents in seconds
- Code is read hundreds of times by humans and agents
- Code is debugged when you're under pressure by tired humans
- Code is modified by agents who lack the original context

**Every ambiguity compounds exponentially.**

```haskell
-- This costs an agent 0.1 seconds to write, a human 10 minutes to debug
process e = if p e > 0 then go e else stop

-- This costs an agent 0.2 seconds to write, saves hours of cumulative confusion
processIncomingRequest :: HttpRequest -> IO ResponseResult
processIncomingRequest httpRequest =
  if requestTimeout httpRequest > 0
    then processValidRequest httpRequest
    else returnTimeoutError
```

## Language Extensions: A Hierarchy of Trust

### Green Light - Use Freely

```haskell
{-# LANGUAGE BangPatterns #-}          -- Strictness is good
{-# LANGUAGE OverloadedStrings #-}     -- Text everywhere
{-# LANGUAGE RecordWildCards #-}       -- Tasteful destructuring
{-# LANGUAGE NamedFieldPuns #-}        -- Clear intent
{-# LANGUAGE DeriveGeneric #-}         -- Boring is good
{-# LANGUAGE DerivingStrategies #-}    -- Be explicit
{-# LANGUAGE StrictData #-}            -- Default strict
{-# LANGUAGE NumericUnderscores #-}    -- 1_000_000 is clearer
```

### Yellow Light - Use With Purpose

```haskell
{-# LANGUAGE TypeFamilies #-}          -- OK for libraries
{-# LANGUAGE GADTs #-}                 -- When the juice is worth the squeeze
{-# LANGUAGE RankNTypes #-}            -- Sometimes necessary
{-# LANGUAGE FlexibleContexts #-}      -- When the alternative is worse
{-# LANGUAGE TemplateHaskell #-}       -- For Aeson/Lens, but measure build impact
```

### Red Light - Justify Your Existence

```haskell
{-# LANGUAGE DataKinds #-}             -- Type-level programming rarely pays off in apps
{-# LANGUAGE TypeOperators #-}         -- Compile times and error messages suffer
{-# LANGUAGE UndecidableInstances #-}  -- Usually means you're solving the wrong problem
{-# LANGUAGE ImplicitParams #-}        -- Debugging nightmare
{-# LANGUAGE OverlappingInstances #-}  -- Semantic timebomb
```

## Control Flow: Pragmatism Over Purity

### The Indentation Reality Check

In production code, deep nesting isn't just ugly—it's a maintenance liability. Every level of
indentation is a place where:

- Merge conflicts multiply
- Off-by-one space errors break compilation
- Code reviews devolve into whitespace debates
- Even good IDEs struggle with Haskell's layout rules

```haskell
-- BAD: Philosophically pure but practically painful
processRequest request =
  case validateRequest request of
    Nothing -> handleInvalid
    Just validReq ->
      case findRoute routes validReq of
        Nothing -> handleNoRoute
        Just route ->
          case lookupHandler route of
            Nothing -> handleMissingHandler
            Just handler ->
              executeHandler handler validReq

-- GOOD: Flat is better than nested
processRequest request
  | Nothing <- validateRequest request = handleInvalid
  | Just validReq <- validateRequest request
  , Nothing <- findRoute routes validReq = handleNoRoute
  | Just validReq <- validateRequest request
  , Just route <- findRoute routes validReq
  , Nothing <- lookupHandler route = handleMissingHandler
  | Just validReq <- validateRequest request
  , Just route <- findRoute routes validReq
  , Just handler <- lookupHandler route = executeHandler handler validReq

-- BETTER: Extract to where clause with guards
processRequest request = processValidated
  where
    processValidated
      | Nothing <- validateRequest request = handleInvalid
      | Just validReq <- validateRequest request = routeRequest validReq

    routeRequest validReq
      | Nothing <- findRoute routes validReq = handleNoRoute
      | Just route <- findRoute routes validReq = handleRoute route validReq

    handleRoute route validReq
      | Nothing <- lookupHandler route = handleMissingHandler
      | Just handler <- lookupHandler route = executeHandler handler validReq
```

### The Production Pattern That Works

Small do-block for sequencing, where-clause with guards for logic:

```haskell
-- This pattern scales to real complexity without nesting hell
handleWebRequest :: Request -> AppM Response
handleWebRequest request = do
  startTime <- getCurrentTime
  validated <- validateOrReject request
  enriched <- enrichRequest validated

  result <- processRequest enriched
  recordMetrics startTime result
  return result
  where
    validateOrReject req
      | not (validMethod req) = throwError InvalidMethod
      | not (validHeaders req) = throwError InvalidHeaders
      | not (validBody req) = throwError InvalidBody
      | otherwise = pure req

    enrichRequest req = do
      sessionId <- extractSessionId req
      permissions <- loadPermissions sessionId
      return $ req { requestSession = sessionId, requestPerms = permissions }

    processRequest req
      | isHealthCheck req = return healthCheckResponse
      | needsAuth req && not (hasValidAuth req) = throwError Unauthorized
      | otherwise = routeToHandler req
```

## Naming: The Three-Character Rule

If an identifier is 3 characters or less, it's probably too short for production code:

```haskell
-- BAD: Abbreviated names multiply confusion
cfg <- loadCfg
conn <- mkConn cfg
res <- proc req

-- GOOD: Full words tell the story
configuration <- loadServerConfiguration
connection <- createDatabaseConnection configuration
response <- processClientRequest request
```

### Standard Exceptions (Use Sparingly)

Only in local scope where type makes it unambiguous:

- `xs, ys` - lists in pure functions
- `m, n` - indices in array algorithms
- `k, v` - key/value in map operations
- `f, g` - functions in higher-order contexts

But even here, consider being explicit:

```haskell
-- OK for simple pure functions
map f xs = ...

-- Better for production code where context matters
mapWithIndex :: (Int -> a -> b) -> [a] -> [b]
mapWithIndex indexedFunction inputList = ...
```

## Config Parsing: The Foundation That Can't Crack

Configuration parsing is critical because config errors multiply across every component. Parse as
much as possible upfront, but pragmatically handle large services that need staged loading:

```haskell
-- Parse and validate core config at startup
loadSystemConfiguration :: FilePath -> IO SystemConfiguration
loadSystemConfiguration configPath = do
  configText <- readFileText configPath
  parseAndValidate configText
  where
    parseAndValidate text = case parseConfigurationTOML text of
      Left parseError ->
        fatal $ "[config] [parse] [error] " <> formatParseError parseError
      Right rawConfig -> case validateConfiguration rawConfig of
        Left validationError ->
          fatal $ "[config] [validation] [error] " <> validationError
        Right validConfig -> do
          logInfo $ "[config] [loaded] [path :: " <> T.pack configPath <> "]"
          return validConfig

-- Make invalid configs unrepresentable
data ValidatedServerConfig = ValidatedServerConfig
  { validatedPort :: PortNumber      -- newtype with bounds checking
  , validatedHost :: HostName        -- newtype with validation
  , validatedMaxConnections :: PositiveInt
  }

newtype PortNumber = PortNumber Word16
mkPortNumber :: Int -> Either Text PortNumber
mkPortNumber portNumber
  | portNumber > 0 && portNumber <= 65535 = Right (PortNumber $ fromIntegral portNumber)
  | otherwise = Left $ "Invalid port: " <> T.pack (show portNumber)
```

## The Agent Collaboration Convention

This convention helps identify code provenance and reasoning:

```haskell
-- Standard implementation following established patterns
parseHttpRequest :: ByteString -> IO (Either ParseError HttpRequest)
parseHttpRequest requestBytes = do
  headersParsed <- parseHeaders requestBytes
  bodyParsed <- parseBody requestBytes

  -- human: http/1.0 clients send malformed content-length, handle gracefully
  let normalizedHeaders = normalizeContentLength headersParsed

  buildRequest normalizedHeaders bodyParsed
```

## Newtype Wrapping: Pragmatic Boundaries

### Always Wrap These

```haskell
-- Domain boundaries - prevents mixing up parameters
newtype SessionId = SessionId UUID
newtype RequestId = RequestId Int64
newtype RouteId = RouteId Text

-- Units and semantics - when the type carries meaning
newtype Milliseconds = Milliseconds Int64
newtype ByteCount = ByteCount Word64
newtype Percentage = Percentage { unPercentage :: Double }

-- Validation boundaries - when construction can fail
newtype Email = Email { unEmail :: Text }
mkEmail :: Text -> Either ValidationError Email

-- Compiler domain - prevents mixing AST node types
newtype NodeId = NodeId Int
newtype TypeId = TypeId Int
newtype ScopeLevel = ScopeLevel Int
```

### Don't Wrap These

```haskell
-- Internal module details
type LoopCounter = Int
type CacheSize = Int

-- Well-typed contexts where confusion is unlikely
data ThreadPool = ThreadPool
  { poolThreadCount :: !Int
  , poolQueueDepth :: !Int
  , poolMaxIdleTime :: !NominalDiffTime
  }
```

The rule: Start with type aliases, upgrade to newtypes when you find bugs mixing things up. With
`-O2`, GHC eliminates newtype overhead anyway.

## STM: Composable Concurrency

STM shines in production because transactions compose and retry elegantly:

```haskell
-- Composable operations for connection pools
allocateFromPool :: ConnectionPool -> Int -> STM (Maybe [Connection])
allocateFromPool pool requestedCount = do
  available <- readTVar (poolAvailable pool)
  if length available >= requestedCount
    then do
      let (allocated, remaining) = splitAt requestedCount available
      writeTVar (poolAvailable pool) remaining
      modifyTVar (poolInUse pool) (allocated ++)
      return (Just allocated)
    else return Nothing

-- Combine multiple operations atomically
transferConnections :: ConnectionPool -> ConnectionPool -> Int -> STM Bool
transferConnections fromPool toPool connectionCount = do
  maybeConnections <- allocateFromPool fromPool connectionCount
  case maybeConnections of
    Nothing -> return False
    Just connections -> do
      modifyTVar (poolAvailable toPool) (connections ++)
      return True
```

STM's limitations: no IO inside transactions, and very long transactions can starve. But for
managing shared state, it's unmatched.

## Compiler Warnings: Your Automated Colleague

Always use strict warnings—they catch more bugs than you lose time to refactoring:

```yaml
# In package.yaml or .cabal
ghc-options:
  - -Wall
  - -Werror
  - -Wincomplete-patterns
  - -Wincomplete-record-updates
  - -Wmissing-signatures
  - -Wname-shadowing
  - -Wunused-matches
  - -Wunused-imports
```

```haskell
-- -Wincomplete-patterns saves you from 3am crashes
processMessage :: Message -> IO ()
processMessage (TextMessage content) = sendText content
processMessage (BinaryMessage bytes) = sendBinary bytes
processMessage (DataMessage payload) = processData payload
-- Compiler ensures we handle all cases

-- -Wmissing-signatures prevents type confusion
processRequest :: UnvalidatedRequest -> IO (Either RequestError Response)
processRequest request = do
  validated <- validateRequest request
  handleRequest validated
```

## State Machines in Types

```haskell
-- BAD: State scattered across booleans
data Connection = Connection
  { isConnected :: Bool
  , isAuthenticated :: Bool
  , hasError :: Bool
  }

-- GOOD: State machine can't be in impossible states
data ConnectionState
  = Disconnected
  | Connecting ConnectingInfo
  | Connected ConnectionInfo
  | Authenticated AuthInfo
  | Errored ErrorInfo

data Connection = Connection
  { connectionId :: ConnectionId
  , connectionState :: TVar ConnectionState
  }

-- Compiler state machines for type checking
data TypeCheckState
  = Parsing SourceLocation
  | ResolvingNames SymbolTable
  | CheckingTypes TypeEnv
  | GeneratingCode CodeGenContext
  | CompilationComplete CompiledModule
  | CompilationFailed CompileError
```

## Metrics and Observability

Instrument what matters, with first-class metrics types:

```haskell
data ServerMetrics = ServerMetrics
  { metricsRequestsReceived :: !Counter
  , metricsRequestsCompleted :: !Counter
  , metricsRequestLatency :: !Histogram
  , metricsActiveConnections :: !Gauge
  }

handleRequest :: ServerState -> Request -> IO Response
handleRequest serverState request = do
  startTime <- getCurrentMonotonicTime
  incrementCounter (metricsRequestsReceived $ serverMetrics serverState)
  incrementGauge (metricsActiveConnections $ serverMetrics serverState)

  result <- processRequest serverState request

  endTime <- getCurrentMonotonicTime
  recordHistogram (metricsRequestLatency $ serverMetrics serverState)
    (timeDiffMicros endTime startTime)
  decrementGauge (metricsActiveConnections $ serverMetrics serverState)

  handleResult result
```

## Structured Logging

```haskell
-- Structured, parseable, grepable
handleHttpRequest :: Request -> IO Response
handleHttpRequest request = do
  logInfo $ "[http] [request] [received] [id :: " <> requestId request <>
            "] [method :: " <> requestMethod request <>
            "] [path :: " <> requestPath request <> "]"

  result <- routeAndHandle request

  logInfo $ "[http] [request] [complete] [id :: " <> requestId request <>
            "] [status :: " <> showStatus result <>
            "] [duration_ms :: " <> showDuration result <> "]"

  return result
```

## Testing Philosophy

### Property Tests for Invariants

```haskell
-- Unit tests: thorough but mechanical (agent-friendly)
describe "parseHttpHeaders" $ do
  it "parses valid headers" $ do
    let input = "Content-Type: application/json\r\nContent-Length: 42\r\n"
    parseHttpHeaders input `shouldBe` Right expectedHeaders

-- Property tests: invariants and edge cases (human insight)
prop_headerRoundTrip :: ValidHeaders -> Bool
prop_headerRoundTrip headers =
  parseHttpHeaders (renderHeaders headers) == Right headers

prop_connectionPoolInvariants :: PoolState -> Bool
prop_connectionPoolInvariants pool =
  let available = poolAvailableConnections pool
      leased = poolLeasedConnections pool
  in Set.null (available `Set.intersection` leased)

-- Compiler invariants
prop_typeCheckPreservesScopes :: TypedAst -> Bool
prop_typeCheckPreservesScopes ast =
  let scopes = extractScopes ast
  in all scopeIsWellFormed scopes
```

## Performance: Start Simple, Measure When It Matters

```haskell
-- GOOD: Write clear code first, compile with -O2
sumResponseSizes :: [HttpResponse] -> ByteCount
sumResponseSizes = sum . map responseSize

-- When profiling shows bottlenecks, then optimize
parseHttpRequestFast :: ByteString -> Either ParseError HttpRequest
parseHttpRequestFast input =
  let !method = parseMethod input
      !headers = parseHeaders input
      !body = parseBody input
  in HttpRequest <$> method <*> headers <*> body

-- Compiler optimization: use ByteString builders for code generation
generateJavaScript :: [Statement] -> ByteString
generateJavaScript statements =
  toLazyByteString $ foldMap statementBuilder statements
  where
    statementBuilder stmt =
      case stmt of
        Assignment var expr ->
          byteString "var " <> byteString var <> byteString " = " <>
          exprBuilder expr <> byteString ";\n"
        Return expr ->
          byteString "return " <> exprBuilder expr <> byteString ";\n"
```

## API Evolution

```haskell
-- Never break, only extend
-- Original (keep forever)
handleRequest :: Request -> IO Response

-- Add better version alongside
handleRequestWithContext :: ServerContext -> Request -> IO DetailedResponse

-- Delegate old to new for consistency
handleRequest :: Request -> IO Response
handleRequest = handleRequestWithContext defaultContext >=> convertResponse
```

## Web Server Patterns

### Middleware Composition

```haskell
type Middleware = Handler -> Handler
type Handler = Request -> IO Response

-- Composable middleware stack
applyMiddleware :: [Middleware] -> Handler -> Handler
applyMiddleware middleware handler =
  foldr ($) handler middleware

-- Common middleware
loggingMiddleware :: Middleware
loggingMiddleware nextHandler request = do
  logInfo $ "[middleware] [logging] [path :: " <> requestPath request <> "]"
  response <- nextHandler request
  logInfo $ "[middleware] [logging] [status :: " <> showStatus response <> "]"
  return response

authMiddleware :: AuthConfig -> Middleware
authMiddleware authConfig nextHandler request = do
  validated <- validateAuth authConfig request
  case validated of
    Left authError -> return $ unauthorizedResponse authError
    Right authenticatedRequest -> nextHandler authenticatedRequest

-- Build server with middleware stack
buildServer :: ServerConfig -> IO Server
buildServer config = do
  let baseHandler = routeRequest config
  let withMiddleware = applyMiddleware
        [ loggingMiddleware
        , authMiddleware (configAuth config)
        , metricsMiddleware (configMetrics config)
        ] baseHandler
  return $ Server config withMiddleware
```

### Routing with Type Safety

```haskell
data Route
  = HealthCheck
  | ApiV1 ApiRoute
  | Static FilePath

data ApiRoute
  = GetUser UserId
  | CreateUser
  | UpdateUser UserId
  | ListSessions
  | GetSession SessionId

parseRoute :: Request -> Either RouteError Route
parseRoute request =
  case requestPath request of
    "/health" -> Right HealthCheck
    path | "/api/v1/" `T.isPrefixOf` path ->
      parseApiRoute (T.drop 8 path)
    path | "/static/" `T.isPrefixOf` path ->
      Right $ Static (T.unpack $ T.drop 8 path)
    _ -> Left RouteNotFound

routeHandler :: Route -> Handler
routeHandler route request =
  case route of
    HealthCheck -> return healthCheckResponse
    ApiV1 apiRoute -> handleApiRoute apiRoute request
    Static filePath -> serveStaticFile filePath
```

## Compiler Construction Patterns

### AST Design

```haskell
-- Use pattern synonyms for common AST patterns
data Expr
  = Var Name
  | Lit Literal
  | App Expr Expr
  | Lam Name Expr
  | Let Name Expr Expr

pattern IntLit :: Int -> Expr
pattern IntLit n = Lit (LitInt n)

pattern BoolLit :: Bool -> Expr
pattern BoolLit b = Lit (LitBool b)

-- Type-safe AST traversal
class Traversable t => AstTraversable t where
  traverseAst :: Applicative f => (Expr -> f Expr) -> t -> f t

foldAst :: Monoid m => (Expr -> m) -> Expr -> m
foldAst f expr = case expr of
  Var name -> f expr
  Lit literal -> f expr
  App function argument ->
    f expr <> foldAst f function <> foldAst f argument
  Lam param body ->
    f expr <> foldAst f body
  Let name value body ->
    f expr <> foldAst f value <> foldAst f body
```

### Type Checking with State

```haskell
type TypeCheck a = StateT TypeEnv (ExceptT TypeError IO) a

data TypeEnv = TypeEnv
  { envBindings :: Map Name Type
  , envTypeVars :: Map TypeVar Type
  , envScopeLevel :: ScopeLevel
  }

checkExpr :: Expr -> TypeCheck Type
checkExpr expr = case expr of
  Var name -> do
    env <- get
    case Map.lookup name (envBindings env) of
      Nothing -> throwError $ UnboundVariable name
      Just varType -> return varType

  App function argument -> do
    functionType <- checkExpr function
    argumentType <- checkExpr argument
    case functionType of
      TyArrow paramType returnType | paramType == argumentType ->
        return returnType
      _ -> throwError $ TypeMismatch functionType argumentType

  Lam param body -> do
    -- Enter new scope for lambda parameter
    paramType <- freshTypeVar
    withBinding param paramType $ do
      bodyType <- checkExpr body
      return $ TyArrow paramType bodyType
```

### Parser Combinators for Speed

```haskell
-- Use attoparsec for performance
parseModule :: Parser Module
parseModule = do
  skipSpace
  imports <- many parseImport
  declarations <- many parseDeclaration
  return $ Module imports declarations

parseDeclaration :: Parser Declaration
parseDeclaration =
  parseFunctionDecl <|> parseTypeDecl <|> parseClassDecl

parseFunctionDecl :: Parser Declaration
parseFunctionDecl = do
  name <- parseIdentifier
  skipSpace
  symbol "::"
  typeSignature <- parseType
  skipSpace
  name' <- parseIdentifier
  when (name /= name') $ fail "function name mismatch"
  parameters <- many parsePattern
  symbol "="
  body <- parseExpr
  return $ FunctionDecl name typeSignature parameters body
```

## The Vibe Test

Good production Haskell passes these checks:

- Could you debug it during an incident without ghci?
- Could a colleague (human or AI) extend it without breaking invariants?
- Do the types prevent tomorrow's bug?
- Is every abbreviation worth the confusion it creates?
- Does it compile fast enough for flow state?
- Will it still make sense after multiple contributors have touched it?

## Required Reading

### The Foundations

- ["Making Ad-Hoc Polymorphism Less Ad Hoc"](https://people.csail.mit.edu/dnj/teaching/6898/papers/wadler88.pdf)
  \- Wadler & Blott (1989)
- ["Monads for Functional Programming"](https://homepages.inf.ed.ac.uk/wadler/papers/marktoberdorf/baastad.pdf)
  \- Wadler (1995)
- ["Software Transactional Memory"](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/2005-ppopp-composable.pdf)
  \- Harris et al. (2005)

### Production Excellence

- [warp](https://github.com/yesodweb/wai) - The fastest Haskell web server
- [aeson](https://github.com/haskell/aeson) - JSON parsing that doesn't compromise
- [servant](https://github.com/haskell-servant/servant) - Type-level web programming that works
- [async](https://github.com/simonmar/async) - Concurrency for mortals
- [megaparsec](https://github.com/mrkkrp/megaparsec) - Parser combinators done right

### Compiler Construction

- "Implementing Functional Languages: A Tutorial" - Simon Peyton Jones
- [GHC source code](https://gitlab.haskell.org/ghc/ghc) - Study the master
- [Ormolu](https://github.com/tweag/ormolu) - Code formatter implementation patterns

### Essential Resources

- "Real World Haskell" - Still relevant for the production mindset
- "Parallel and Concurrent Programming in Haskell" (Marlow) - Concurrency done right
- [What I Wish I Knew When Learning Haskell](http://dev.stephendiehl.com/hask/) - Practical guidance

## Summary: Production Haskell for the Modern Era

We write Haskell like we're building production systems, not proving theorems. In codebases where
agents contribute significantly:

1. **Optimize for disambiguation** - Every ambiguity compounds
1. **Make invalid states unrepresentable** - Use the type system
1. **Be explicit about effects** - IO vs STM vs pure must be obvious
1. **Parse config early and strictly** - Config errors multiply
1. **Use the compiler as your pair programmer** - -Wall -Werror always
1. **Instrument what matters** - First-class metrics and structured logs
1. **Keep it flat** - Deep nesting is a maintenance liability, not elegant code

The Haskell community optimized for elegance. We optimize for clarity at scale. Beauty in production
code comes from disambiguation, not cleverness.

Write code as if a hundred contributors will extend it tomorrow, and you'll debug it during an
incident next month. Because both will happen.

We are not the same as the Haskell you learned in school. We're what happens when you take those
ideas and make them work for money.
