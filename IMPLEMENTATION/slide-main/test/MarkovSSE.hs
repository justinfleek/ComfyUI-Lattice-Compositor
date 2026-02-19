{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Markov Chain SIGIL Frame Generator for Stress Testing

Generates maximally convincing polyhedral tensor calculus text, tokenizes it
using a real HuggingFace tokenizer, encodes into SIGIL binary frames, and
publishes over ZMQ for the listener to decode and display.

This exercises the full production code path:
  MarkovText → Tokenizer.encode → HotTable → Frame.write* → ZMQ.send

Usage:
  buck2 run //:markov -- -t tokenizers/llama-3-8b-Instruct/tokenizer.json
  
Then in another terminal:
  buck2 run //:slide -- listen -t tokenizers/llama-3-8b-Instruct/tokenizer.json --dump-frames
-}
module MarkovSSE (main) where

import Control.Concurrent (threadDelay)
import Control.Exception (bracket)
import Control.Monad (forM_, when)
import Data.Aeson (object, (.=))
import Data.Aeson qualified as Aeson
import Data.ByteString qualified as BS
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time.Clock.POSIX (getPOSIXTime)
import Data.Word (Word32, Word64)
import Numeric (showHex)
import Options.Applicative
import System.IO (hFlush, stdout)
import System.Random (StdGen, mkStdGen, randomIO, randomR)
import System.ZMQ4 qualified as ZMQ

import Slide.HotTable (HotTable, defaultHotTable, lookupHot)
import Slide.Tokenizer (HFTokenizer, encode, loadTokenizerJSON)
import Slide.Wire.Frame (
    Frame (..),
    finishFrame,
    newFrameBuilder,
    writeExtendedToken,
    writeHotToken,
    writeStreamEnd,
 )

-- ════════════════════════════════════════════════════════════════════════════════
--                                                                  // cli // o
-- ════════════════════════════════════════════════════════════════════════════════

data MarkovOptions = MarkovOptions
    { optTokenizer :: !FilePath
    , optZmqBind :: !Text
    , optSeed :: !(Maybe Int)
    , optNumResponses :: !Int
    , optTokensPerResponse :: !Int
    , optDelayMs :: !Int
    , optVerbose :: !Bool
    }

parseMarkovOptions :: Parser MarkovOptions
parseMarkovOptions =
    MarkovOptions
        <$> strOption
            ( long "tokenizer"
                <> short 't'
                <> metavar "PATH"
                <> value "tokenizers/llama-3-8b-Instruct/tokenizer.json"
                <> help "Tokenizer JSON path"
            )
        <*> strOption
            ( long "zmq"
                <> short 'z'
                <> metavar "BIND"
                <> value "tcp://*:5555"
                <> help "ZMQ PUB bind address"
            )
        <*> optional
            ( option auto
                ( long "seed"
                    <> short 's'
                    <> metavar "INT"
                    <> help "Random seed (default: random)"
                )
            )
        <*> option auto
            ( long "responses"
                <> short 'n'
                <> metavar "N"
                <> value 10
                <> help "Number of responses to generate (default: 10)"
            )
        <*> option auto
            ( long "tokens"
                <> metavar "N"
                <> value 200
                <> help "Max tokens per response (default: 200)"
            )
        <*> option auto
            ( long "delay"
                <> short 'd'
                <> metavar "MS"
                <> value 20
                <> help "Delay between tokens in ms (default: 20)"
            )
        <*> switch
            ( long "verbose"
                <> short 'v'
                <> help "Show debug output"
            )

markovOptsInfo :: ParserInfo MarkovOptions
markovOptsInfo =
    info
        (parseMarkovOptions <**> helper)
        ( fullDesc
            <> progDesc "Generate fake polyhedral tensor calculus over SIGIL/ZMQ"
            <> header "markov - stress test SIGIL pipeline with Markov-generated math"
        )

-- ════════════════════════════════════════════════════════════════════════════════
-- Stream Metadata (matches app/Main.hs)
-- ════════════════════════════════════════════════════════════════════════════════

data StreamMetadata = StreamMetadata
    { metaStreamId :: !Text
    , metaModel :: !Text
    , metaTimestamp :: !Double
    }

instance Aeson.ToJSON StreamMetadata where
    toJSON meta =
        object
            [ "stream_id" .= metaStreamId meta
            , "model" .= metaModel meta
            , "timestamp" .= metaTimestamp meta
            ]

_modelToTopic :: Text -> BS.ByteString
_modelToTopic model = BS.toStrict $ Aeson.encode $ "model/" <> model

-- ════════════════════════════════════════════════════════════════════════════════
-- Markov Chain Types
-- ════════════════════════════════════════════════════════════════════════════════

type NGram = [Text]
type MarkovChain = Map NGram [(Text, Double)]

chainOrder :: Int
chainOrder = 3

-- ════════════════════════════════════════════════════════════════════════════════
-- Domain-Specific Vocabulary
-- ════════════════════════════════════════════════════════════════════════════════

_polyhedralVocab :: [Text]
_polyhedralVocab =
    [ "polytope", "polyhedron", "halfspace", "hyperplane", "vertex", "facet"
    , "cone", "fan", "lattice", "integer hull", "Minkowski sum"
    , "affine transform", "unimodular", "Hermite normal form"
    , "Chernikova", "Farkas lemma", "Fourier-Motzkin elimination"
    , "parametric integer programming", "Presburger arithmetic"
    , "schedule", "tiling", "skewing", "interchange", "fusion", "fission"
    , "dependence polyhedron", "iteration domain", "access relation"
    , "Omega library", "isl", "Polly", "PENCIL", "PPCG"
    , "loop nest", "perfectly nested", "imperfectly nested"
    , "data locality", "parallelism", "vectorization"
    , "rectangular tiling", "hexagonal tiling", "diamond tiling"
    ]

_tensorVocab :: [Text]
_tensorVocab =
    [ "tensor", "contraction", "outer product", "Kronecker product"
    , "index notation", "Einstein summation", "raised index", "lowered index"
    , "covariant", "contravariant", "metric tensor", "Christoffel symbols"
    , "Riemann curvature", "Ricci tensor", "stress-energy tensor"
    , "tensor network", "MPS", "PEPS", "MERA", "TTN"
    , "bond dimension", "entanglement entropy", "area law"
    , "tensor decomposition", "CP decomposition", "Tucker decomposition"
    , "tensor train", "hierarchical Tucker", "tensor ring"
    , "einsum", "opt_einsum", "contraction path", "flop count"
    , "mode-n product", "unfolding", "matricization", "tensorization"
    ]

_mathSymbols :: [Text]
_mathSymbols =
    [ "∀", "∃", "∈", "∉", "⊂", "⊃", "⊆", "⊇", "∪", "∩"
    , "∅", "ℕ", "ℤ", "ℚ", "ℝ", "ℂ", "ℍ", "𝕜"
    , "→", "←", "↔", "⇒", "⇐", "⇔", "↦", "↪", "↠"
    , "⊗", "⊕", "⊖", "⊙", "⊛", "⊘", "⊚", "⊜"
    , "∧", "∨", "¬", "⊤", "⊥", "⊢", "⊨", "⊩"
    , "∑", "∏", "∫", "∮", "∂", "∇", "△", "□"
    , "≤", "≥", "≠", "≈", "≅", "≡", "≢", "≪", "≫"
    , "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ"
    , "λ", "μ", "ν", "ξ", "π", "ρ", "σ", "τ", "υ", "φ"
    , "χ", "ψ", "ω", "Γ", "Δ", "Θ", "Λ", "Ξ", "Π", "Σ"
    , "Φ", "Ψ", "Ω"
    , "⟨", "⟩", "⟦", "⟧", "⟪", "⟫", "⌈", "⌉", "⌊", "⌋"
    , "∘", "·", "×", "÷", "±", "∓", "√", "∛", "∜"
    , "∞", "ℵ", "ℶ", "ℷ", "𝟘", "𝟙", "𝟚"
    ]

-- ════════════════════════════════════════════════════════════════════════════════
-- Training Corpus
-- ════════════════════════════════════════════════════════════════════════════════

trainingCorpus :: [Text]
trainingCorpus =
    [ "The polyhedral model represents loop nests as integer polyhedra in a multidimensional iteration space."
    , "Each statement is associated with an iteration domain defined by affine constraints on loop indices."
    , "Dependence analysis computes the set of pairs of iterations that must execute in order."
    , "The dependence polyhedron captures all source-sink pairs constrained by data dependencies."
    , "Affine scheduling assigns a multidimensional timestamp to each iteration preserving dependencies."
    , "Feautrier's algorithm computes a legal affine schedule using parametric integer programming."
    , "The Pluto algorithm finds schedules that maximize coarse-grained parallelism and locality."
    , "Loop tiling partitions the iteration space into smaller blocks that fit in cache."
    , "Rectangular tiling uses axis-aligned hyperplanes to define tile boundaries."
    , "Diamond tiling handles stencil computations with time-skewing for wavefront parallelism."
    , "Tensor contraction generalizes matrix multiplication to higher-order tensors."
    , "Einstein summation notation implicitly sums over repeated indices in tensor expressions."
    , "The contraction path determines the order of pairwise contractions in a tensor network."
    , "Optimal contraction ordering minimizes the total number of floating point operations."
    , "Tensor decomposition approximates a tensor as a sum of rank-one components."
    , "CP decomposition expresses a tensor as a sum of outer products of vectors."
    , "Tucker decomposition factors a tensor into a core tensor and factor matrices."
    , "Tensor train format represents a tensor as a chain of three-way core tensors."
    , "Matrix product states are the tensor train decomposition applied to quantum states."
    , "The bond dimension controls the approximation quality and computational cost."
    , "Entanglement entropy measures quantum correlations across a bipartition."
    , "The area law states that ground state entanglement scales with boundary size."
    , "DMRG optimizes MPS representations by sweeping through sites variationally."
    , "TEBD evolves tensor networks in time using Trotter decomposition of the Hamiltonian."
    , "The polyhedral compilation framework uses Presburger arithmetic for exact analysis."
    , "Fourier-Motzkin elimination projects a polyhedron onto a lower-dimensional space."
    , "Chernikova's algorithm computes the vertices and rays of a polyhedron."
    , "The isl library provides exact integer set and map operations."
    , "Polly is an LLVM pass that applies polyhedral optimizations to LLVM IR."
    , "PPCG generates CUDA code from polyhedral representations of loop nests."
    , "The affine scheduling problem is NP-hard in general but tractable for fixed dimensions."
    , "Unimodular transformations preserve the integer lattice and loop bounds."
    , "Skewing adds a linear combination of outer loop indices to inner loops."
    , "Loop interchange permutes the order of loops in a perfectly nested loop."
    , "Loop fusion combines multiple loops into one to improve data locality."
    , "Loop fission splits a loop into multiple loops to enable parallelization."
    , "The Minkowski sum of two polytopes is the set of pairwise sums of their points."
    , "A polytope is bounded iff it can be expressed as the convex hull of finitely many points."
    , "The polar dual of a polytope exchanges vertices and facets."
    , "A simplicial cone is generated by linearly independent rays."
    , "The Hilbert basis of a cone is the minimal generating set over the integers."
    , "Tensor network contraction is equivalent to computing a marginalization in graphical models."
    , "The treewidth of the contraction graph bounds the complexity of optimal contraction."
    , "Consider the lattice P where α ∈ ℤⁿ and β ⊗ γ converges."
    , "Let T be a bounded tensor. Then ∑ᵢ Tᵢⱼ ⊗ Uʲᵏ yields a covariant factorization."
    , "By Farkas' lemma, the cone is pointed iff the iteration space tiles."
    , "The affine hull of {x | Ax ≤ b} can be computed in O(n³) time."
    , "Note that ⟨ψ|φ⟩ ≈ Tr(ρσ) by the area law for entanglement entropy."
    ]

-- ════════════════════════════════════════════════════════════════════════════════
-- Markov Chain Construction
-- ════════════════════════════════════════════════════════════════════════════════

buildChain :: [Text] -> MarkovChain
buildChain corpus = Map.fromListWith (++) $ concatMap extractNGrams corpus
  where
    extractNGrams :: Text -> [(NGram, [(Text, Double)])]
    extractNGrams text =
        let tokens = T.words text
            padded = replicate chainOrder "<START>" ++ tokens ++ ["<END>"]
            windows = slidingWindow (chainOrder + 1) padded
        in [(take chainOrder w, [(last w, 1.0)]) | w <- windows, length w == chainOrder + 1]

    slidingWindow :: Int -> [a] -> [[a]]
    slidingWindow n xs
        | length xs < n = []
        | otherwise = take n xs : slidingWindow n (drop 1 xs)

sampleChain :: MarkovChain -> StdGen -> Int -> ([Text], StdGen)
sampleChain chain gen0 maxTokens = go gen0 (replicate chainOrder "<START>") [] maxTokens
  where
    go :: StdGen -> NGram -> [Text] -> Int -> ([Text], StdGen)
    go gen _ acc 0 = (reverse acc, gen)
    go gen context acc remaining =
        case Map.lookup context chain of
            Nothing -> (reverse acc, gen)
            Just candidates ->
                let (nextToken, gen') = weightedChoice gen candidates
                in if nextToken == "<END>"
                    then (reverse acc, gen')
                    else go gen' (drop 1 context ++ [nextToken]) (nextToken : acc) (remaining - 1)

    weightedChoice :: StdGen -> [(Text, Double)] -> (Text, StdGen)
    weightedChoice gen [] = ("<UNK>", gen)
    weightedChoice gen options@((firstTok, _) : _) =
        let total = sum $ map snd options
            (r, gen') = randomR (0, total) gen
            pick _ [] = (firstTok, gen')
            pick threshold ((tok, weight) : rest)
                | threshold <= weight = (tok, gen')
                | otherwise = pick (threshold - weight) rest
        in pick r options

defaultChain :: MarkovChain
defaultChain = buildChain trainingCorpus

-- ════════════════════════════════════════════════════════════════════════════════
--                                                                // sigil // f
-- ════════════════════════════════════════════════════════════════════════════════

-- | Emit a single frame containing tokens, using hot table compression
emitTokenFrame ::
    ZMQ.Socket ZMQ.Pub ->
    StreamMetadata ->
    HotTable ->
    [Word32] ->
    Bool ->
    IO ()
emitTokenFrame pub meta hotTable tokenIds verbose = do
    builder <- newFrameBuilder 4096

    forM_ tokenIds $ \tokenId ->
        case lookupHot hotTable tokenId of
            Just hotId -> writeHotToken builder hotId
            Nothing -> writeExtendedToken builder tokenId

    frame <- finishFrame builder
    let bytes = frameBytes frame
        topic = "model/" <> BS.toStrict (Aeson.encode (metaModel meta))
        metaJson = BS.toStrict $ Aeson.encode meta

    when verbose $ do
        putStr $ "  -> frame: " ++ show (length tokenIds) ++ " tokens, "
        putStrLn $ show (BS.length bytes) ++ " bytes"
        hFlush stdout

    ZMQ.sendMulti pub (topic :| [metaJson, bytes])

-- | Emit stream end frame
emitStreamEnd :: ZMQ.Socket ZMQ.Pub -> StreamMetadata -> Bool -> IO ()
emitStreamEnd pub meta verbose = do
    builder <- newFrameBuilder 64
    writeStreamEnd builder
    frame <- finishFrame builder
    let bytes = frameBytes frame
        topic = "model/" <> BS.toStrict (Aeson.encode (metaModel meta))
        metaJson = BS.toStrict $ Aeson.encode meta

    when verbose $ putStrLn "  -> [EOS]"

    ZMQ.sendMulti pub (topic :| [metaJson, bytes])

-- ════════════════════════════════════════════════════════════════════════════════
-- Main
-- ════════════════════════════════════════════════════════════════════════════════

main :: IO ()
main = do
    opts <- execParser markovOptsInfo

    putStrLn "╔═══════════════════════════════════════════════════════════════════════╗"
    putStrLn "║              Markov SIGIL Frame Generator                             ║"
    putStrLn "╚═══════════════════════════════════════════════════════════════════════╝"
    putStrLn ""

    -- Load tokenizer
    putStrLn $ "Loading tokenizer: " ++ optTokenizer opts
    tokenizer <- loadTokenizerJSON (optTokenizer opts)

    -- Get random seed
    seed <- case optSeed opts of
        Just s -> pure s
        Nothing -> randomIO

    putStrLn $ "Random seed: " ++ show seed
    putStrLn $ "ZMQ bind: " ++ T.unpack (optZmqBind opts)
    putStrLn $ "Responses: " ++ show (optNumResponses opts)
    putStrLn $ "Tokens/response: " ++ show (optTokensPerResponse opts)
    putStrLn $ "Delay: " ++ show (optDelayMs opts) ++ "ms"
    putStrLn ""

    -- Initialize ZMQ
    bracket ZMQ.context ZMQ.term $ \ctx ->
        bracket (ZMQ.socket ctx ZMQ.Pub) ZMQ.close $ \pub -> do
            ZMQ.bind pub (T.unpack $ optZmqBind opts)

            -- Let subscribers connect
            putStrLn "Waiting for subscribers..."
            threadDelay 1_000_000

            putStrLn "Streaming..."
            putStrLn ""

            -- Generate responses
            let hotTable = defaultHotTable
                gen0 = mkStdGen seed

            generateResponses opts tokenizer hotTable pub gen0

    putStrLn ""
    putStrLn "Done."

generateResponses ::
    MarkovOptions ->
    HFTokenizer ->
    HotTable ->
    ZMQ.Socket ZMQ.Pub ->
    StdGen ->
    IO ()
generateResponses opts tokenizer hotTable pub gen0 = go gen0 1
  where
    go _ n | n > optNumResponses opts = pure ()
    go gen n = do
        -- Generate stream ID
        streamId <- randomIO :: IO Word64
        let streamIdHex = T.pack $ showHex streamId ""

        timestamp <- realToFrac <$> getPOSIXTime
        let meta = StreamMetadata
                { metaStreamId = streamIdHex
                , metaModel = "markov/polyhedral-tensor-v1"
                , metaTimestamp = timestamp
                }

        putStrLn $ "── Response " ++ show n ++ "/" ++ show (optNumResponses opts) ++ " ──"
        putStrLn $ "   stream_id: " ++ T.unpack streamIdHex

        -- Generate text from Markov chain
        let (words_, gen') = sampleChain defaultChain gen (optTokensPerResponse opts)
            text = T.unwords words_

        when (optVerbose opts) $ do
            putStrLn $ "   text: " ++ T.unpack (T.take 80 text) ++ "..."

        -- Tokenize
        tokenIds <- encode tokenizer text

        putStrLn $ "   tokens: " ++ show (length tokenIds)

        -- Stream tokens in small batches (simulating incremental generation)
        let batchSize = 8
            batches = chunksOf batchSize tokenIds

        forM_ batches $ \batch -> do
            emitTokenFrame pub meta hotTable batch (optVerbose opts)
            threadDelay (optDelayMs opts * 1000)

        -- Send stream end
        emitStreamEnd pub meta (optVerbose opts)

        putStrLn ""
        
        -- Small delay between responses
        threadDelay 500_000

        go gen' (n + 1)

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)
