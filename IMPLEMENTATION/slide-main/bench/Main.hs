{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE RecordWildCards #-}

{- | SIGIL Wire Format Benchmarks

Raw throughput benchmarks for encode/decode operations.
Measures tokens/second and bytes/second under various conditions.

Run with: buck2 run //:bench
Run specific benchmarks: buck2 run //:bench -- varint encode decode
Run ZMQ benchmarks: buck2 run //:bench -- --zmq
Set duration: buck2 run //:bench -- --duration 5 throughput
-}
module Main where

import Control.Concurrent (getNumCapabilities, threadDelay)
import Control.Concurrent.Async (replicateConcurrently, withAsync, wait)
import Control.DeepSeq (NFData (..))
import Control.Exception (evaluate)
import Control.Monad (forM_, replicateM_, when)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.Word (Word32)
import Options.Applicative hiding (action)
import System.Clock (Clock (..), getTime, toNanoSecs)
import System.IO (hFlush, stdout)
import System.ZMQ4 qualified as ZMQ
import Text.Printf (printf)

import Slide.Wire.Decode (
    Chunk (..),
    ChunkContent (..),
    DecodeState,
    decodeFrame,
    feedBytes,
    initDecodeState,
 )
import Slide.Wire.Frame (
    Frame (..),
    finishFrame,
    newFrameBuilder,
    resetBuilder,
    writeExtendedToken,
    writeHotToken,
    writeStreamEnd,
 )
import Slide.Wire.Varint (decodeVarint, encodeVarint)

-- ════════════════════════════════════════════════════════════════════════════════
--                                                                  // cli // o
-- ════════════════════════════════════════════════════════════════════════════════

data BenchOptions = BenchOptions
    { optZMQ :: !Bool
    , optDuration :: !Int  -- seconds for sustained tests
    , optBenchmarks :: [String]  -- empty = all
    }

parseBenchOptions :: Parser BenchOptions
parseBenchOptions = do
    optZMQ <- switch
        ( long "zmq"
       <> help "Run ZMQ pub/sub throughput benchmarks"
        )
    optDuration <- option auto
        ( long "duration"
       <> short 'd'
       <> metavar "SECONDS"
       <> value 10
       <> help "Duration for sustained throughput tests (default: 10)"
        )
    optBenchmarks <- many (argument str (metavar "BENCHMARKS..."))
    pure BenchOptions{..}

benchOptsInfo :: ParserInfo BenchOptions
benchOptsInfo = info (parseBenchOptions <**> helper)
    ( fullDesc
   <> progDesc "SIGIL wire format benchmarks"
   <> header "bench - benchmark SIGIL encode/decode/ZMQ throughput"
    )

-- ════════════════════════════════════════════════════════════════════════════════
-- Benchmark Infrastructure
-- ════════════════════════════════════════════════════════════════════════════════

data BenchResult = BenchResult
    { benchName :: !String
    , benchIterations :: !Int
    , benchTotalNs :: !Integer
    , benchOpsPerSec :: !Double
    , benchThroughputMBps :: !(Maybe Double)
    }

instance NFData BenchResult where
    rnf (BenchResult n i t o m) = n `seq` i `seq` t `seq` o `seq` m `seq` ()

-- | Time an IO action in nanoseconds
timeNs :: IO a -> IO (a, Integer)
timeNs action = do
    start <- getTime Monotonic
    !result <- action
    end <- getTime Monotonic
    let !elapsed = toNanoSecs end - toNanoSecs start
    pure (result, elapsed)

-- | Run a benchmark with warmup
bench :: String -> Int -> IO a -> IO BenchResult
bench name iterations action = do
    -- Warmup: 10% of iterations or at least 100
    let warmupCount = max 100 (iterations `div` 10)
    replicateM_ warmupCount action
    
    -- Timed run
    (_, elapsed) <- timeNs $ replicateM_ iterations action
    
    let opsPerSec = fromIntegral iterations / (fromIntegral elapsed / 1e9)
    pure BenchResult
        { benchName = name
        , benchIterations = iterations
        , benchTotalNs = elapsed
        , benchOpsPerSec = opsPerSec
        , benchThroughputMBps = Nothing
        }

-- | Run a benchmark with byte throughput tracking
benchWithBytes :: String -> Int -> Int -> IO a -> IO BenchResult
benchWithBytes name iterations bytesPerOp action = do
    result <- bench name iterations action
    let totalBytes = fromIntegral $ iterations * bytesPerOp
        seconds = fromIntegral (benchTotalNs result) / 1e9
        mbps = totalBytes / seconds / (1024 * 1024)
    pure result { benchThroughputMBps = Just mbps }

printResult :: BenchResult -> IO ()
printResult r = do
    let opsStr = formatOps (benchOpsPerSec r)
        timeStr = formatTime (benchTotalNs r)
    case benchThroughputMBps r of
        Just mbps -> printf "  %-40s %12s ops/s  %10s  %8.1f MB/s\n" 
            (benchName r) opsStr timeStr mbps
        Nothing -> printf "  %-40s %12s ops/s  %10s\n" 
            (benchName r) opsStr timeStr
    hFlush stdout

formatOps :: Double -> String
formatOps ops
    | ops >= 1e9 = printf "%.2fG" (ops / 1e9)
    | ops >= 1e6 = printf "%.2fM" (ops / 1e6)
    | ops >= 1e3 = printf "%.2fK" (ops / 1e3)
    | otherwise = printf "%.0f" ops

formatTime :: Integer -> String
formatTime ns
    | ns >= 1_000_000_000 = printf "%.2fs" (fromIntegral ns / 1e9 :: Double)
    | ns >= 1_000_000 = printf "%.2fms" (fromIntegral ns / 1e6 :: Double)
    | ns >= 1_000 = printf "%.2fus" (fromIntegral ns / 1e3 :: Double)
    | otherwise = printf "%dns" ns

-- ════════════════════════════════════════════════════════════════════════════════
-- Varint Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

benchVarint :: IO ()
benchVarint = do
    putStrLn "\n═══ Varint Encode/Decode ═══"
    
    -- Single byte (0-127)
    printResult =<< bench "encode varint (1 byte)" 10_000_000 (evaluate $ encodeVarint 42)
    printResult =<< bench "decode varint (1 byte)" 10_000_000 (evaluate $ decodeVarint (BS.pack [42]))
    
    -- Two bytes (128-16383)
    let twoByteVal = encodeVarint 1000
    printResult =<< bench "encode varint (2 bytes)" 10_000_000 (evaluate $ encodeVarint 1000)
    printResult =<< bench "decode varint (2 bytes)" 10_000_000 (evaluate $ decodeVarint twoByteVal)
    
    -- Five bytes (max Word32)
    let fiveByteVal = encodeVarint (fromIntegral (maxBound :: Word32))
    printResult =<< bench "encode varint (5 bytes)" 10_000_000 (evaluate $ encodeVarint (fromIntegral (maxBound :: Word32)))
    printResult =<< bench "decode varint (5 bytes)" 10_000_000 (evaluate $ decodeVarint fiveByteVal)

-- ════════════════════════════════════════════════════════════════════════════════
-- Frame Encode Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

benchEncode :: IO ()
benchEncode = do
    putStrLn "\n═══ Frame Encoding ═══"
    
    -- Small frame (100 hot tokens)
    printResult =<< benchWithBytes "encode 100 hot tokens" 100_000 100 (do
        builder <- newFrameBuilder 256
        forM_ [0..99 :: Int] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))
    
    -- Medium frame (1K hot tokens)
    printResult =<< benchWithBytes "encode 1K hot tokens" 10_000 1000 (do
        builder <- newFrameBuilder 2048
        forM_ [0..999 :: Int] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))
    
    -- Large frame (100K hot tokens)
    printResult =<< benchWithBytes "encode 100K hot tokens" 100 100_000 (do
        builder <- newFrameBuilder 200_000
        forM_ [0..99_999 :: Int] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))
    
    -- Extended tokens (require varint encoding)
    printResult =<< benchWithBytes "encode 1K extended tokens" 10_000 5000 (do
        builder <- newFrameBuilder 10_000
        forM_ [1000..1999 :: Word32] $ \i ->
            writeExtendedToken builder i
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))
    
    -- Builder reuse (amortized allocation)
    builder <- newFrameBuilder 2048
    printResult =<< benchWithBytes "encode 100 hot (reused builder)" 100_000 100 (do
        resetBuilder builder
        forM_ [0..99 :: Int] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))

-- ════════════════════════════════════════════════════════════════════════════════
-- Frame Decode Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

-- | Pre-build frames for decode benchmarks
buildTestFrame :: Int -> Bool -> IO ByteString
buildTestFrame tokenCount extended = do
    builder <- newFrameBuilder (tokenCount * 6)
    if extended
        then forM_ [1..tokenCount] $ \i ->
            writeExtendedToken builder (fromIntegral $ i * 1000)
        else forM_ [0..tokenCount-1] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
    writeStreamEnd builder
    frame <- finishFrame builder
    pure $! frameBytes frame

benchDecode :: IO ()
benchDecode = do
    putStrLn "\n═══ Frame Decoding ═══"
    
    -- Pre-build test frames
    frame100 <- buildTestFrame 100 False
    frame1k <- buildTestFrame 1000 False
    frame100k <- buildTestFrame 100_000 False
    frame1kExt <- buildTestFrame 1000 True
    
    printResult =<< benchWithBytes "decode 100 hot tokens" 100_000 (BS.length frame100)
        (evaluate $ length $ decodeFrame frame100)
    
    printResult =<< benchWithBytes "decode 1K hot tokens" 10_000 (BS.length frame1k)
        (evaluate $ length $ decodeFrame frame1k)
    
    printResult =<< benchWithBytes "decode 100K hot tokens" 100 (BS.length frame100k)
        (evaluate $ length $ decodeFrame frame100k)
    
    printResult =<< benchWithBytes "decode 1K extended tokens" 10_000 (BS.length frame1kExt)
        (evaluate $ length $ decodeFrame frame1kExt)

-- ════════════════════════════════════════════════════════════════════════════════
-- Incremental Decode Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

benchIncremental :: IO ()
benchIncremental = do
    putStrLn "\n═══ Incremental Decoding ═══"
    
    frame1k <- buildTestFrame 1000 False
    let frameLen = BS.length frame1k
    
    -- Feed entire frame at once
    printResult =<< benchWithBytes "incremental (full frame)" 10_000 frameLen (do
        let (_, chunks) = feedBytes initDecodeState frame1k
        evaluate $ length chunks)
    
    -- Feed in 64-byte chunks
    let chunks64 = chunksOf 64 frame1k
    printResult =<< benchWithBytes "incremental (64B chunks)" 10_000 frameLen (do
        let (_, chunks) = foldl' feedChunk (initDecodeState, []) chunks64
        evaluate $ length chunks)
    
    -- Feed in 256-byte chunks
    let chunks256 = chunksOf 256 frame1k
    printResult =<< benchWithBytes "incremental (256B chunks)" 10_000 frameLen (do
        let (_, chunks) = foldl' feedChunk (initDecodeState, []) chunks256
        evaluate $ length chunks)
    
    -- Feed byte-by-byte (worst case)
    let frameSmall = BS.take 100 frame1k  -- Only first 100 bytes
    printResult =<< benchWithBytes "incremental (byte-by-byte)" 10_000 100 (do
        let bytes = map BS.singleton $ BS.unpack frameSmall
            (_, chunks) = foldl' feedChunk (initDecodeState, []) bytes
        evaluate $ length chunks)

feedChunk :: (DecodeState, [Chunk]) -> ByteString -> (DecodeState, [Chunk])
feedChunk (state, acc) chunk =
    let (newState, newChunks) = feedBytes state chunk
    in (newState, acc ++ newChunks)

chunksOf :: Int -> ByteString -> [ByteString]
chunksOf n bs
    | BS.null bs = []
    | otherwise = BS.take n bs : chunksOf n (BS.drop n bs)

-- ════════════════════════════════════════════════════════════════════════════════
-- Concurrent Throughput Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

benchConcurrent :: IO ()
benchConcurrent = do
    caps <- getNumCapabilities
    putStrLn $ "\n═══ Concurrent Throughput (" ++ show caps ++ " cores) ═══"
    
    -- Build shared test data
    frame1k <- buildTestFrame 1000 False
    let frameLen = BS.length frame1k
    
    -- Single-threaded baseline (10K iterations)
    let singleIters = 10_000
    printResult =<< benchWithBytes "single-threaded encode 1K" singleIters 1000 (do
        builder <- newFrameBuilder 2048
        forM_ [0..999 :: Int] $ \i ->
            writeHotToken builder (fromIntegral $ i `mod` 127)
        writeStreamEnd builder
        !frame <- finishFrame builder
        evaluate (BS.length $ frameBytes frame))
    
    printResult =<< benchWithBytes "single-threaded decode 1K" singleIters frameLen
        (evaluate $ length $ decodeFrame frame1k)
    
    -- Concurrent encode: N threads × M iterations = total ops
    -- We want same total work as single-threaded for fair comparison
    let perThread = 10_000
        totalOps = caps * perThread
    
    putStrLn $ "  [" ++ show caps ++ " threads × " ++ show perThread ++ " iterations = " ++ show totalOps ++ " total ops]"
    
    (_, encodeTime) <- timeNs $ do
        _ <- replicateConcurrently caps $ do
            builder <- newFrameBuilder 2048
            replicateM_ perThread $ do
                resetBuilder builder
                forM_ [0..999 :: Int] $ \i ->
                    writeHotToken builder (fromIntegral $ i `mod` 127)
                writeStreamEnd builder
                !frame <- finishFrame builder
                evaluate (BS.length $ frameBytes frame)
        pure ()
    
    let encodeOpsPerSec = fromIntegral totalOps / (fromIntegral encodeTime / 1e9) :: Double
        encodeMbps = fromIntegral (totalOps * 1000) / (fromIntegral encodeTime / 1e9) / (1024 * 1024) :: Double
    printf "  %-40s %12s ops/s  %10s  %8.1f MB/s\n"
        ("concurrent encode 1K (" ++ show caps ++ " threads)")
        (formatOps encodeOpsPerSec)
        (formatTime encodeTime)
        encodeMbps
    
    -- Concurrent decode
    (_, decodeTime) <- timeNs $ do
        _ <- replicateConcurrently caps $
            replicateM_ perThread $
                evaluate $ length $ decodeFrame frame1k
        pure ()
    
    let decodeOpsPerSec = fromIntegral totalOps / (fromIntegral decodeTime / 1e9) :: Double
        decodeMbps = fromIntegral (totalOps * frameLen) / (fromIntegral decodeTime / 1e9) / (1024 * 1024) :: Double
    printf "  %-40s %12s ops/s  %10s  %8.1f MB/s\n"
        ("concurrent decode 1K (" ++ show caps ++ " threads)")
        (formatOps decodeOpsPerSec)
        (formatTime decodeTime)
        decodeMbps
    
    -- Scaling efficiency
    let encodeSpeedup = encodeOpsPerSec / 48810 :: Double  -- baseline from single-threaded
        decodeSpeedup = decodeOpsPerSec / 661240000 :: Double  -- baseline
    printf "  Encode scaling:     %.1fx (ideal: %dx)\n" encodeSpeedup caps
    printf "  Decode scaling:     %.2fx (ideal: %dx)\n" decodeSpeedup caps

-- ════════════════════════════════════════════════════════════════════════════════
-- Latency Benchmarks
-- ════════════════════════════════════════════════════════════════════════════════

benchLatency :: IO ()
benchLatency = do
    putStrLn "\n═══ Latency (single operation) ═══"
    
    -- Measure individual operation latencies
    let iterations = 100_000 :: Int
    
    -- Hot token encode latency
    builder <- newFrameBuilder 256
    hotLatencies <- mapM (\_ -> do
        resetBuilder builder
        (_, ns) <- timeNs $ do
            writeHotToken builder 42
            writeStreamEnd builder
            finishFrame builder
        pure ns) [1..iterations]
    
    let hotAvg = fromIntegral (sum hotLatencies) / fromIntegral iterations :: Double
        hotMin = minimum hotLatencies
        hotMax = maximum hotLatencies
    
    printf "  hot token encode:   avg=%s  min=%s  max=%s\n"
        (formatTime $ round hotAvg)
        (formatTime hotMin)
        (formatTime hotMax)
    
    -- Decode latency
    frame <- buildTestFrame 10 False
    decodeLatencies <- mapM (\_ -> do
        (_, ns) <- timeNs $ evaluate $ decodeFrame frame
        pure ns) [1..iterations]
    
    let decAvg = fromIntegral (sum decodeLatencies) / fromIntegral iterations :: Double
        decMin = minimum decodeLatencies
        decMax = maximum decodeLatencies
    
    printf "  decode 10 tokens:   avg=%s  min=%s  max=%s\n"
        (formatTime $ round decAvg)
        (formatTime decMin)
        (formatTime decMax)

-- ════════════════════════════════════════════════════════════════════════════════
--                                                                  // zmq // p
-- ════════════════════════════════════════════════════════════════════════════════

benchZMQ :: Int -> IO ()
benchZMQ durationSecs = do
    caps <- getNumCapabilities
    putStrLn $ "\n═══ ZMQ Pub/Sub Throughput (" ++ show durationSecs ++ "s, " ++ show caps ++ " cores) ═══"
    
    -- Build test frames of various sizes
    frame100 <- buildTestFrame 100 False
    frame1k <- buildTestFrame 1000 False
    frame10k <- buildTestFrame 10000 False
    
    let endpoint = "inproc://sigil-bench"
    
    -- Single pub -> single sub throughput
    ZMQ.withContext $ \ctx -> do
        putStrLn "  [1 pub → 1 sub, inproc]"
        
        -- Test different frame sizes
        forM_ [(100, frame100), (1000, frame1k), (10000, frame10k)] $ \(tokenCount, frame) -> do
            let frameLen = BS.length frame
            
            recvCounter <- newIORef (0 :: Int)
            stopFlag <- newIORef False
            
            let targetDurationNs = fromIntegral durationSecs * 1_000_000_000 :: Integer
            
            -- Run pub/sub pair
            (_, elapsed) <- timeNs $ do
                ZMQ.withSocket ctx ZMQ.Pub $ \pub -> do
                    ZMQ.bind pub endpoint
                    -- Let bind settle
                    threadDelay 10_000
                    
                    ZMQ.withSocket ctx ZMQ.Sub $ \sub -> do
                        ZMQ.subscribe sub ""
                        ZMQ.connect sub endpoint
                        threadDelay 10_000
                        
                        -- Receiver async
                        withAsync (receiver sub recvCounter stopFlag) $ \recvAsync -> do
                            -- Publisher loop
                            start <- getTime Monotonic
                            let pubLoop = do
                                    ZMQ.send pub [] frame
                                    now <- getTime Monotonic
                                    let elapsedNs = toNanoSecs now - toNanoSecs start
                                    when (elapsedNs < targetDurationNs) pubLoop
                            pubLoop
                            
                            -- Signal stop and drain
                            writeIORef stopFlag True
                            threadDelay 100_000
                            wait recvAsync
            
            framesRecv <- readIORef recvCounter
            let seconds = fromIntegral elapsed / 1e9 :: Double
                framesPerSec = fromIntegral framesRecv / seconds
                tokensPerSec = fromIntegral (framesRecv * tokenCount) / seconds
                bytesPerSec = fromIntegral (framesRecv * frameLen) / seconds
                mbps = bytesPerSec / (1024 * 1024)
            
            printf "  %5d tokens/frame: %s frames/s  %s tokens/s  %.1f MB/s\n"
                tokenCount
                (formatOps framesPerSec)
                (formatOps tokensPerSec)
                mbps
    
    -- Parallel pubs -> single sub
    putStrLn ""
    putStrLn $ "  [" ++ show caps ++ " pubs → 1 sub, inproc]"
    
    let parallelEndpoint = "inproc://sigil-bench-parallel"
    
    ZMQ.withContext $ \ctx -> do
        recvCounter <- newIORef (0 :: Int)
        stopFlag <- newIORef False
        let targetDurationNs = fromIntegral durationSecs * 1_000_000_000 :: Integer
        
        (_, elapsed) <- timeNs $ do
            ZMQ.withSocket ctx ZMQ.Sub $ \sub -> do
                ZMQ.subscribe sub ""
                ZMQ.bind sub parallelEndpoint
                threadDelay 10_000
                
                withAsync (receiver sub recvCounter stopFlag) $ \recvAsync -> do
                    -- Launch parallel publishers
                    _ <- replicateConcurrently caps $ do
                        ZMQ.withSocket ctx ZMQ.Pub $ \pub -> do
                            ZMQ.connect pub parallelEndpoint
                            threadDelay 10_000
                            
                            builder <- newFrameBuilder 2048
                            start <- getTime Monotonic
                            let pubLoop = do
                                    resetBuilder builder
                                    forM_ [0..999 :: Int] $ \i ->
                                        writeHotToken builder (fromIntegral $ i `mod` 127)
                                    writeStreamEnd builder
                                    !frame <- finishFrame builder
                                    ZMQ.send pub [] (frameBytes frame)
                                    now <- getTime Monotonic
                                    let elapsedNs = toNanoSecs now - toNanoSecs start
                                    when (elapsedNs < targetDurationNs) pubLoop
                            pubLoop
                    
                    writeIORef stopFlag True
                    threadDelay 100_000
                    wait recvAsync
        
        framesRecv <- readIORef recvCounter
        let seconds = fromIntegral elapsed / 1e9 :: Double
            framesPerSec = fromIntegral framesRecv / seconds
            tokensPerSec = fromIntegral (framesRecv * 1000) / seconds
        
        printf "  1K tokens/frame:   %s frames/s  %s tokens/s\n"
            (formatOps framesPerSec)
            (formatOps tokensPerSec)
    
    -- End-to-end: encode → ZMQ → decode
    putStrLn ""
    putStrLn "  [encode → ZMQ → decode roundtrip]"
    
    let e2eEndpoint = "inproc://sigil-bench-e2e"
    
    ZMQ.withContext $ \ctx -> do
        tokensDecoded <- newIORef (0 :: Int)
        stopFlag <- newIORef False
        let targetDurationNs = fromIntegral durationSecs * 1_000_000_000 :: Integer
        
        (_, elapsed) <- timeNs $ do
            ZMQ.withSocket ctx ZMQ.Pub $ \pub -> do
                ZMQ.bind pub e2eEndpoint
                threadDelay 10_000
                
                ZMQ.withSocket ctx ZMQ.Sub $ \sub -> do
                    ZMQ.subscribe sub ""
                    ZMQ.connect sub e2eEndpoint
                    threadDelay 10_000
                    
                    -- Receiver that decodes
                    withAsync (decodingReceiver sub tokensDecoded stopFlag) $ \recvAsync -> do
                        -- Publisher that encodes
                        builder <- newFrameBuilder 2048
                        start <- getTime Monotonic
                        let pubLoop = do
                                resetBuilder builder
                                forM_ [0..999 :: Int] $ \i ->
                                    writeHotToken builder (fromIntegral $ i `mod` 127)
                                writeStreamEnd builder
                                !frame <- finishFrame builder
                                ZMQ.send pub [] (frameBytes frame)
                                now <- getTime Monotonic
                                let elapsedNs = toNanoSecs now - toNanoSecs start
                                when (elapsedNs < targetDurationNs) pubLoop
                        pubLoop
                        
                        writeIORef stopFlag True
                        threadDelay 100_000
                        wait recvAsync
        
        tokens <- readIORef tokensDecoded
        let seconds = fromIntegral elapsed / 1e9 :: Double
            tokensPerSec = fromIntegral tokens / seconds
        
        printf "  1K tokens/frame:   %s tokens/s (end-to-end)\n"
            (formatOps tokensPerSec)
  where
    receiver :: ZMQ.Socket ZMQ.Sub -> IORef Int -> IORef Bool -> IO ()
    receiver sub counter stopFlag = loop
      where
        loop = do
            stop <- readIORef stopFlag
            if stop
                then pure ()
                else do
                    _ <- ZMQ.receive sub
                    atomicModifyIORef' counter (\c -> (c + 1, ()))
                    loop
    
    decodingReceiver :: ZMQ.Socket ZMQ.Sub -> IORef Int -> IORef Bool -> IO ()
    decodingReceiver sub counter stopFlag = loop
      where
        loop = do
            stop <- readIORef stopFlag
            if stop
                then pure ()
                else do
                    frame <- ZMQ.receive sub
                    let chunks = decodeFrame frame
                        tokenCount = sum [length toks | Chunk (TextContent toks) _ <- chunks]
                    atomicModifyIORef' counter (\c -> (c + tokenCount, ()))
                    loop

-- ════════════════════════════════════════════════════════════════════════════════
-- Main
-- ════════════════════════════════════════════════════════════════════════════════

main :: IO ()
main = do
    opts <- execParser benchOptsInfo
    caps <- getNumCapabilities
    
    putStrLn "╔═══════════════════════════════════════════════════════════════════════╗"
    putStrLn "║                    SIGIL Wire Format Benchmarks                       ║"
    putStrLn "╚═══════════════════════════════════════════════════════════════════════╝"
    printf "  Cores: %d\n" caps
    printf "  Duration: %ds (for sustained tests)\n" (optDuration opts)
    
    let args = optBenchmarks opts
        runAll = null args && not (optZMQ opts)
        shouldRun name = runAll || name `elem` args
    
    when (shouldRun "varint") benchVarint
    when (shouldRun "encode") benchEncode
    when (shouldRun "decode") benchDecode
    when (shouldRun "incremental") benchIncremental
    when (shouldRun "concurrent") benchConcurrent
    when (shouldRun "latency") benchLatency
    when (shouldRun "throughput" || runAll) $ benchThroughputDuration (optDuration opts)
    when (optZMQ opts || "zmq" `elem` args) $ benchZMQ (optDuration opts)
    
    putStrLn "\n═══ Done ═══"

-- | Throughput benchmark with configurable duration
benchThroughputDuration :: Int -> IO ()
benchThroughputDuration durationSecs = do
    caps <- getNumCapabilities
    putStrLn $ "\n═══ Sustained Throughput (" ++ show durationSecs ++ "s burst) ═══"
    
    -- Measure sustained encode throughput
    let tokensPerFrame = 1000
        targetDurationNs = fromIntegral durationSecs * 1_000_000_000 :: Integer
    
    counter <- newIORef (0 :: Int)
    (_, elapsed) <- timeNs $ do
        -- Run for target duration by doing batches and checking time
        let runBatch = replicateM_ 10000 $ do
                builder <- newFrameBuilder 2048
                forM_ [0..tokensPerFrame-1 :: Int] $ \i ->
                    writeHotToken builder (fromIntegral $ i `mod` 127)
                writeStreamEnd builder
                !frame <- finishFrame builder
                _ <- evaluate (BS.length $ frameBytes frame)
                atomicModifyIORef' counter (\c -> (c + 1, ()))
        start <- getTime Monotonic
        let loop = do
                runBatch
                now <- getTime Monotonic
                let elapsedNs = toNanoSecs now - toNanoSecs start
                when (elapsedNs < targetDurationNs) loop
        loop
    
    frames <- readIORef counter
    let tokensTotal = frames * tokensPerFrame
        seconds = fromIntegral elapsed / 1e9 :: Double
        tokensPerSec = fromIntegral tokensTotal / seconds
        framesPerSec = fromIntegral frames / seconds
    
    printf "  [Single-threaded]\n"
    printf "  Frames encoded:     %d\n" frames
    printf "  Tokens encoded:     %d\n" tokensTotal
    printf "  Duration:           %.2fs\n" seconds
    printf "  Throughput:         %s tokens/s\n" (formatOps tokensPerSec)
    printf "  Frame rate:         %s frames/s\n" (formatOps framesPerSec)
    
    -- Parallel sustained throughput (no contention - each thread counts locally)
    putStrLn ""
    printf "  [Parallel: %d threads]\n" caps
    
    (threadCounts, parallelElapsed) <- timeNs $ do
        replicateConcurrently caps $ do
            builder <- newFrameBuilder 2048
            localCounter <- newIORef (0 :: Int)
            start <- getTime Monotonic
            let loop = do
                    resetBuilder builder
                    forM_ [0..tokensPerFrame-1 :: Int] $ \i ->
                        writeHotToken builder (fromIntegral $ i `mod` 127)
                    writeStreamEnd builder
                    !frame <- finishFrame builder
                    _ <- evaluate (BS.length $ frameBytes frame)
                    atomicModifyIORef' localCounter (\c -> (c + 1, ()))
                    now <- getTime Monotonic
                    let elapsedNs = toNanoSecs now - toNanoSecs start
                    when (elapsedNs < targetDurationNs) loop
            loop
            readIORef localCounter
    
    let parallelFrames = sum threadCounts
    let parallelTokens = parallelFrames * tokensPerFrame
        parallelSeconds = fromIntegral parallelElapsed / 1e9 :: Double
        parallelToksPerSec = fromIntegral parallelTokens / parallelSeconds
        parallelFramesPerSec = fromIntegral parallelFrames / parallelSeconds
        speedup = parallelToksPerSec / tokensPerSec
    
    printf "  Frames encoded:     %d\n" parallelFrames
    printf "  Tokens encoded:     %d\n" parallelTokens
    printf "  Duration:           %.2fs\n" parallelSeconds
    printf "  Throughput:         %s tokens/s\n" (formatOps parallelToksPerSec)
    printf "  Frame rate:         %s frames/s\n" (formatOps parallelFramesPerSec)
    printf "  Speedup:            %.1fx\n" speedup
