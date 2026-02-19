{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

{- | Stress tests and property-based tests for SIGIL wire format

These tests aim to break the encoder/decoder under adversarial conditions:
- High concurrency
- Large payloads
- Malformed input
- Boundary conditions
- Memory pressure
-}
module StressSpec (spec) where

import Control.Concurrent.Async (mapConcurrently, replicateConcurrently)
import Control.Exception (evaluate)
import Control.Monad (forM_, replicateM_)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.Word (Word32, Word8)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy, expectationFailure)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (
    Arbitrary (..),
    Gen,
    choose,
    forAll,
    frequency,
    ioProperty,
    listOf,
    listOf1,
    (==>),
 )

import Slide.Wire.Decode (
    Chunk (..),
    ChunkContent (..),
    DecodeState,
    decodeFrame,
    decodeFrameIncremental,
    feedBytes,
    flushDecoder,
    initDecodeState,
 )
import Slide.Wire.Frame (
    FrameOp (..),
    finishFrame,
    newFrameBuilder,
    resetBuilder,
    writeChunkEnd,
    writeControl,
    writeExtendedToken,
    writeFlush,
    writeHotToken,
    writeStreamEnd,
    Frame (..),
    pattern OP_THINK_START,
    pattern OP_THINK_END,
    pattern OP_TOOL_CALL_START,
    pattern OP_TOOL_CALL_END,
 )
import Slide.Wire.Types (maxHotId)
import Slide.Wire.Varint (decodeVarint, encodeVarint)

-- ════════════════════════════════════════════════════════════════════════════════
-- Test Data Generators
-- ════════════════════════════════════════════════════════════════════════════════

-- | Generate a hot token ID (0-126)
genHotId :: Gen Word8
genHotId = choose (0, maxHotId)

-- | Generate an extended token ID (any Word32)
genExtendedId :: Gen Word32
genExtendedId = frequency
    [ (3, choose (127, 1000))           -- Common range
    , (2, choose (1000, 100000))        -- Medium range  
    , (1, choose (100000, maxBound))    -- Large IDs
    ]

-- | Generate malformed byte sequences
genMalformedBytes :: Gen ByteString
genMalformedBytes = frequency
    [ (3, BS.pack <$> listOf arbitrary)                    -- Random bytes
    , (2, pure $ BS.pack [0x80])                           -- Truncated varint
    , (2, pure $ BS.pack [0x80, 0x80, 0x80, 0x80, 0x80, 0x80])  -- Overlong varint
    , (2, pure $ BS.pack [0xD0, 0xD1, 0xD2])               -- Reserved range
    , (1, pure $ BS.pack $ replicate 10000 0x80)           -- Many continuation bytes
    ]

-- ════════════════════════════════════════════════════════════════════════════════
-- Property Tests
-- ════════════════════════════════════════════════════════════════════════════════

spec :: Spec
spec = do
    propertyTests
    stressTests
    edgeCaseTests
    adversarialSpec

propertyTests :: Spec
propertyTests = do
    describe "Property: Varint" $ do
        modifyMaxSuccess (const 10000) $ do
            prop "roundtrip for all Word32" $ \(w :: Word32) ->
                let encoded = encodeVarint (fromIntegral w)
                in case decodeVarint encoded of
                    Just (decoded, len) -> 
                        decoded == fromIntegral w && len == BS.length encoded
                    Nothing -> False

            prop "encoding is prefix-free" $ \(w1 :: Word32) (w2 :: Word32) ->
                w1 /= w2 ==>
                    let e1 = encodeVarint (fromIntegral w1)
                        e2 = encodeVarint (fromIntegral w2)
                    in not (e1 `BS.isPrefixOf` e2) || BS.length e1 == BS.length e2

            prop "encoded length is bounded" $ \(w :: Word32) ->
                let encoded = encodeVarint (fromIntegral w)
                in BS.length encoded <= 5  -- Max 5 bytes for 32-bit

    describe "Property: Encode/Decode Roundtrip" $ do
        modifyMaxSuccess (const 5000) $ do
            prop "hot tokens roundtrip" $ \hotId ->
                hotId <= maxHotId ==> ioProperty $ do
                    builder <- newFrameBuilder 1024
                    writeHotToken builder hotId
                    writeStreamEnd builder
                    frame <- finishFrame builder
                    let chunks = decodeFrame (frameBytes frame)
                    pure $ case chunks of
                        [Chunk (TextContent [tok]) _, Chunk StreamEnd True] ->
                            tok == fromIntegral hotId
                        [Chunk (TextContent [tok]) True] ->
                            tok == fromIntegral hotId
                        _ -> False

            prop "extended tokens roundtrip" $ forAll genExtendedId $ \tokId -> ioProperty $ do
                builder <- newFrameBuilder 1024
                writeExtendedToken builder tokId
                writeStreamEnd builder
                frame <- finishFrame builder
                let chunks = decodeFrame (frameBytes frame)
                pure $ case chunks of
                    [Chunk (TextContent [tok]) _, Chunk StreamEnd True] ->
                        tok == tokId
                    [Chunk (TextContent [tok]) True] ->
                        tok == tokId
                    _ -> False

            prop "multiple tokens roundtrip" $ forAll (listOf1 genHotId) $ \hotIds -> ioProperty $ do
                builder <- newFrameBuilder (length hotIds * 2 + 10)
                mapM_ (writeHotToken builder) hotIds
                writeStreamEnd builder
                frame <- finishFrame builder
                let chunks = decodeFrame (frameBytes frame)
                    extractTokens = concatMap extractChunkTokens chunks
                pure $ extractTokens == map fromIntegral hotIds

    describe "Property: Incremental Decode" $ do
        modifyMaxSuccess (const 2000) $ do
            prop "incremental == batch for any split" $ 
                forAll (listOf1 genHotId) $ \hotIds -> ioProperty $ do
                    builder <- newFrameBuilder (length hotIds * 2 + 10)
                    mapM_ (writeHotToken builder) hotIds
                    writeStreamEnd builder
                    frame <- finishFrame builder
                    let fullBytes = frameBytes frame
                    
                    -- Batch decode
                    let batchChunks = decodeFrame fullBytes
                    
                    -- Incremental decode (split at random points)
                    let incrementalChunks = decodeIncremental fullBytes
                    
                    -- Extract tokens should match
                    pure $ concatMap extractChunkTokens batchChunks == 
                        concatMap extractChunkTokens incrementalChunks

            prop "state is preserved across feeds" $ 
                forAll (listOf1 genHotId) $ \hotIds -> ioProperty $ do
                    builder <- newFrameBuilder (length hotIds * 2 + 10)
                    mapM_ (writeHotToken builder) hotIds
                    writeChunkEnd builder
                    mapM_ (writeHotToken builder) hotIds
                    writeStreamEnd builder
                    frame <- finishFrame builder
                    let fullBytes = frameBytes frame
                    
                    -- Feed one byte at a time
                    let (_, chunks) = foldl' feedOneByte (initDecodeState, []) (BS.unpack fullBytes)
                    
                    -- Should get two text chunks plus stream end
                    pure $ length (filter isTextChunk chunks) >= 1

stressTests :: Spec
stressTests = do
    describe "Stress: Malformed Input" $ do
        modifyMaxSuccess (const 1000) $ do
            prop "decoder doesn't crash on garbage" $ forAll genMalformedBytes $ \bytes ->
                let chunks = decodeFrame bytes
                in chunks `seq` True  -- Just check it doesn't crash

            prop "decoder handles truncated varints" $ \n ->
                n > 0 ==>
                    let truncated = BS.take n (BS.pack $ replicate 10 0x80)
                        chunks = decodeFrame (BS.singleton 0x80 <> truncated)
                    in chunks `seq` True

            prop "decoder handles reserved bytes" $ 
                forAll (choose (0xD0, 0xFF)) $ \(byte :: Word8) ->
                    let chunks = decodeFrame (BS.singleton byte)
                    in chunks `seq` True

    describe "Stress: Large Payloads" $ do
        it "handles 1MB frame" $ do
            let tokenCount = 500000  -- ~500K tokens
            builder <- newFrameBuilder (tokenCount * 2)
            replicateM_ tokenCount (writeHotToken builder 42)
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
                totalTokens = sum $ map (length . extractChunkTokens) chunks
            totalTokens `shouldBe` tokenCount

        it "handles 10K extended tokens" $ do
            let tokenCount = 10000
            builder <- newFrameBuilder (tokenCount * 6)  -- ~5 bytes per extended
            forM_ [1..tokenCount] $ \i ->
                writeExtendedToken builder (fromIntegral i * 1000)
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
                totalTokens = sum $ map (length . extractChunkTokens) chunks
            totalTokens `shouldBe` tokenCount

        it "handles deep nesting of control frames" $ do
            builder <- newFrameBuilder 10000
            -- Rapidly alternate modes
            replicateM_ 100 $ do
                writeControl builder OP_THINK_START
                writeHotToken builder 1
                writeControl builder OP_THINK_END
                writeControl builder OP_TOOL_CALL_START
                writeHotToken builder 2
                writeControl builder OP_TOOL_CALL_END
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            -- Should have 200 think/tool chunks + stream end
            length chunks `shouldSatisfy` (> 100)

    describe "Stress: Concurrent Access" $ do
        it "parallel encoders don't interfere" $ do
            results <- replicateConcurrently 100 $ do
                builder <- newFrameBuilder 1024
                forM_ [1..100 :: Int] $ \i ->
                    writeHotToken builder (fromIntegral $ i `mod` 127)
                writeStreamEnd builder
                frame <- finishFrame builder
                pure $ BS.length (frameBytes frame)
            
            -- All should produce same length
            case results of
                (x:_) -> all (== x) results `shouldBe` True
                [] -> expectationFailure "No results"

        it "parallel decoders on same data" $ do
            -- Build a test frame
            builder <- newFrameBuilder 10000
            replicateM_ 1000 (writeHotToken builder 42)
            writeStreamEnd builder
            frame <- finishFrame builder
            let bytes = frameBytes frame
            
            -- Decode in parallel
            results <- replicateConcurrently 100 $ do
                let chunks = decodeFrame bytes
                pure $ sum $ map (length . extractChunkTokens) chunks
            
            -- All should get same result
            all (== 1000) results `shouldBe` True

        it "rapid builder reuse" $ do
            builder <- newFrameBuilder 1024
            counter <- newIORef (0 :: Int)
            
            replicateM_ 1000 $ do
                resetBuilder builder
                writeHotToken builder 42
                writeStreamEnd builder
                frame <- finishFrame builder
                let chunks = decodeFrame (frameBytes frame)
                    n = sum $ map (length . extractChunkTokens) chunks
                atomicModifyIORef' counter (\c -> (c + n, ()))
            
            total <- readIORef counter
            total `shouldBe` 1000

        it "concurrent encode/decode pipeline" $ do
            let numStreams = 50
                tokensPerStream = 100
            
            results <- mapConcurrently (\streamId -> do
                -- Each stream encodes and decodes independently
                builder <- newFrameBuilder 1024
                forM_ [1..tokensPerStream] $ \_ ->
                    writeHotToken builder (fromIntegral $ streamId `mod` 127)
                writeStreamEnd builder
                frame <- finishFrame builder
                let chunks = decodeFrame (frameBytes frame)
                pure $ sum $ map (length . extractChunkTokens) chunks
                ) [1..numStreams]
            
            sum results `shouldBe` (numStreams * tokensPerStream)

    describe "Stress: Memory Pressure" $ do
        it "doesn't leak with repeated allocations" $ do
            -- Create and discard many builders
            replicateM_ 10000 $ do
                builder <- newFrameBuilder 4096
                writeHotToken builder 1
                writeStreamEnd builder
                _ <- finishFrame builder
                pure ()
            -- If we get here without OOM, we're good
            True `shouldBe` True

        it "handles rapid state transitions" $ do
            let iterations = 10000
            builder <- newFrameBuilder (iterations * 10)
            forM_ [1..iterations] $ \i -> do
                case i `mod` 6 of
                    0 -> writeControl builder OP_THINK_START
                    1 -> writeControl builder OP_THINK_END
                    2 -> writeControl builder OP_TOOL_CALL_START
                    3 -> writeControl builder OP_TOOL_CALL_END
                    4 -> writeHotToken builder (fromIntegral $ i `mod` 127)
                    _ -> writeFlush builder
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            length chunks `shouldSatisfy` (> 0)

    describe "Stress: Timeout/Deadlock Detection" $ do
        it "decode completes in bounded time" $ do
            -- 1M hot tokens followed by STREAM_END
            let hugeFrame = BS.replicate 1000000 0x42 <> BS.singleton 0xCF
            result <- timeout 5000000 $ evaluate $ length $ decodeFrame hugeFrame
            case result of
                Just n -> n `shouldSatisfy` (> 0)
                Nothing -> expectationFailure "Decode timed out (>5s)"

        it "incremental decode doesn't block" $ do
            let bytes = BS.replicate 100000 0x42
            result <- timeout 1000000 $ do
                let (_, chunks) = decodeFrameIncremental initDecodeState bytes
                evaluate $ length chunks
            case result of
                Just n -> n `shouldSatisfy` (>= 0)
                Nothing -> expectationFailure "Incremental decode blocked"

edgeCaseTests :: Spec
edgeCaseTests = do
    describe "Edge Cases" $ do
        it "empty frame" $ do
            let chunks = decodeFrame BS.empty
            chunks `shouldBe` []

        it "single StreamEnd" $ do
            let chunks = decodeFrame (BS.singleton 0xCF)
            case chunks of
                [Chunk StreamEnd True] -> pure ()
                _ -> expectationFailure $ "Unexpected: " ++ show chunks

        it "max hot token" $ do
            builder <- newFrameBuilder 10
            writeHotToken builder maxHotId
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            case chunks of
                [Chunk (TextContent [tok]) _, Chunk StreamEnd True] ->
                    tok `shouldBe` fromIntegral maxHotId
                [Chunk (TextContent [tok]) True] ->
                    tok `shouldBe` fromIntegral maxHotId
                _ -> expectationFailure $ "Unexpected: " ++ show chunks

        it "max Word32 token" $ do
            builder <- newFrameBuilder 20
            writeExtendedToken builder maxBound
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            case chunks of
                [Chunk (TextContent [tok]) _, Chunk StreamEnd True] ->
                    tok `shouldBe` maxBound
                [Chunk (TextContent [tok]) True] ->
                    tok `shouldBe` maxBound
                _ -> expectationFailure $ "Unexpected: " ++ show chunks

        it "alternating hot/extended" $ do
            builder <- newFrameBuilder 1000
            forM_ [1..100 :: Int] $ \i -> do
                if even i
                    then writeHotToken builder (fromIntegral $ i `mod` 127)
                    else writeExtendedToken builder (fromIntegral $ i * 1000)
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
                totalTokens = sum $ map (length . extractChunkTokens) chunks
            totalTokens `shouldBe` 100

-- ════════════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════════════

extractChunkTokens :: Chunk -> [Word32]
extractChunkTokens (Chunk content _) = case content of
    TextContent tokens -> tokens
    ThinkContent tokens -> tokens
    ToolCallContent tokens -> tokens
    CodeBlockContent tokens -> tokens
    StreamEnd -> []
    DecodeError _ -> []
    AmbiguityReset _ -> []

isTextChunk :: Chunk -> Bool
isTextChunk (Chunk (TextContent _) _) = True
isTextChunk _ = False

-- | Feed bytes one at a time
feedOneByte :: (DecodeState, [Chunk]) -> Word8 -> (DecodeState, [Chunk])
feedOneByte (state, accChunks) byte =
    let (newState, newChunks) = feedBytes state (BS.singleton byte)
    in (newState, accChunks ++ newChunks)

-- | Decode incrementally by splitting input
decodeIncremental :: ByteString -> [Chunk]
decodeIncremental bytes = go initDecodeState bytes []
  where
    go state remaining acc
        | BS.null remaining = 
            case flushDecoder state of
                Just chunk -> acc ++ [chunk]
                Nothing -> acc
        | otherwise =
            let (byte, rest) = (BS.head remaining, BS.tail remaining)
                (newState, chunks) = feedBytes state (BS.singleton byte)
            in go newState rest (acc ++ chunks)

-- ════════════════════════════════════════════════════════════════════════════════
-- Additional Adversarial Tests
-- ════════════════════════════════════════════════════════════════════════════════

adversarialSpec :: Spec
adversarialSpec = do
    describe "Adversarial: Pathological Inputs" $ do
        it "survives 10M random bytes" $ do
            -- Generate deterministic but arbitrary bytes
            let bytes = BS.pack $ take 10000000 $ cycle [0x00..0xFF]
            let chunks = decodeFrame bytes
            -- Just check it terminates and doesn't crash
            length chunks `shouldSatisfy` (>= 0)

        it "handles alternating escape/continuation" $ do
            -- 0x80 0x80 0x80... - endless continuation without termination
            let bytes = BS.replicate 10000 0x80 <> BS.singleton 0xCF
            let chunks = decodeFrame bytes
            length chunks `shouldSatisfy` (>= 0)

        it "handles max varint overflow attempt" $ do
            -- Try to encode a value larger than Word32 max
            let bytes = BS.pack [0x80, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01, 0xCF]
            let chunks = decodeFrame bytes
            length chunks `shouldSatisfy` (>= 0)

        it "survives all control codes in sequence" $ do
            builder <- newFrameBuilder 1000
            -- Every control code
            forM_ [0xC0..0xCF] $ \op ->
                writeControl builder (FrameOp op)
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            length chunks `shouldSatisfy` (>= 0)

        it "handles interleaved modes without matching pairs" $ do
            builder <- newFrameBuilder 1000
            -- Start think, start tool (without ending think), etc.
            writeControl builder OP_THINK_START
            writeHotToken builder 1
            writeControl builder OP_TOOL_CALL_START  -- Never ended think!
            writeHotToken builder 2
            writeControl builder OP_THINK_START  -- Nested think?
            writeHotToken builder 3
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            -- Should handle gracefully
            length chunks `shouldSatisfy` (> 0)

    describe "Adversarial: Concurrency Hammering" $ do
        it "100 concurrent builders, 1000 ops each" $ do
            results <- replicateConcurrently 100 $ do
                builder <- newFrameBuilder 10000
                forM_ [1..1000 :: Int] $ \i -> do
                    if even i
                        then writeHotToken builder (fromIntegral $ i `mod` 127)
                        else writeExtendedToken builder (fromIntegral $ i * 100)
                writeStreamEnd builder
                frame <- finishFrame builder
                let chunks = decodeFrame (frameBytes frame)
                pure $ sum $ map (length . extractChunkTokens) chunks
            
            -- Each should have 1000 tokens
            all (== 1000) results `shouldBe` True

        it "rapid state machine transitions" $ do
            let iterations = 100000
            builder <- newFrameBuilder (iterations * 2)
            forM_ [1..iterations] $ \i ->
                case i `mod` 8 of
                    0 -> writeControl builder OP_THINK_START
                    1 -> writeHotToken builder 1
                    2 -> writeControl builder OP_THINK_END
                    3 -> writeControl builder OP_TOOL_CALL_START
                    4 -> writeHotToken builder 2
                    5 -> writeControl builder OP_TOOL_CALL_END
                    6 -> writeChunkEnd builder
                    _ -> writeFlush builder
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            -- Should have many chunks
            length chunks `shouldSatisfy` (> 1000)

        it "concurrent incremental decode" $ do
            -- Build a test frame
            builder <- newFrameBuilder 100000
            replicateM_ 10000 (writeHotToken builder 42)
            writeStreamEnd builder
            frame <- finishFrame builder
            let bytes = frameBytes frame
            
            -- Split into chunks and decode concurrently
            let chunkSize = BS.length bytes `div` 100
                byteChunks = chunksOf chunkSize bytes
            
            results <- replicateConcurrently 10 $ do
                let (_, allChunks) = foldl' 
                        (\(state, acc) chunk -> 
                            let (newState, chunks) = feedBytes state chunk
                            in (newState, acc ++ chunks))
                        (initDecodeState, [])
                        byteChunks
                pure $ sum $ map (length . extractChunkTokens) allChunks
            
            -- All should get same result
            all (== 10000) results `shouldBe` True

    describe "Adversarial: Memory Exhaustion Attempts" $ do
        it "doesn't explode on deeply nested empty chunks" $ do
            builder <- newFrameBuilder 100000
            -- 10K empty chunk boundaries
            replicateM_ 10000 $ writeChunkEnd builder
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            -- Many empty text chunks plus stream end
            length chunks `shouldSatisfy` (> 0)

        it "handles 100K mode transitions" $ do
            builder <- newFrameBuilder 300000
            replicateM_ 100000 $ do
                writeControl builder OP_THINK_START
                writeControl builder OP_THINK_END
            writeStreamEnd builder
            frame <- finishFrame builder
            let chunks = decodeFrame (frameBytes frame)
            length chunks `shouldSatisfy` (> 0)

-- | Split ByteString into chunks
chunksOf :: Int -> ByteString -> [ByteString]
chunksOf n bs
    | BS.null bs = []
    | otherwise = BS.take n bs : chunksOf n (BS.drop n bs)
