--| slide - Console cowboy for the sprawl
--|
--| Ingress adapter that jacks into OpenAI-compatible inference endpoints,
--| parses their SSE/JSON garbage, and emits clean SIGIL binary frames over ZMQ.
--|
--| Build: ./dhall-to-buck BUILD.dhall > BUCK

let A = ./dhall/prelude/package.dhall
let S = ./dhall/prelude/to-starlark.dhall

-- Library sources (all modules under src/Slide/)
let librarySrcs =
      [ "src/Slide/Chunk.hs"
      , "src/Slide/Configuration.hs"
      , "src/Slide/HotTable.hs"
      , "src/Slide/Model.hs"
      , "src/Slide/Parse.hs"
      , "src/Slide/Provider.hs"
      , "src/Slide/Provider/HTTP2.hs"
      , "src/Slide/Provider/OpenAI.hs"
      , "src/Slide/Provider/OpenRouter.hs"
      , "src/Slide/Provider/Vertex/Anthropic.hs"
      , "src/Slide/Tokenizer.hs"
      , "src/Slide/Tokenizer/FFI.hs"
      , "src/Slide/Wire/Decode.hs"
      , "src/Slide/Wire/Encode.hs"
      , "src/Slide/Wire/Frame.hs"
      , "src/Slide/Wire/Types.hs"
      , "src/Slide/Wire/Varint.hs"
      ]

-- Executable sources
let appSrcs = [ "app/Main.hs" ]

-- C++ FFI sources for tokenizers binding
let cxxSrcs = [ "cbits/tokenizers_c.cpp" ]

-- All Haskell packages needed
let packages =
      [ "base"
      , "aeson"
      , "async"
      , "blake3"
      , "bytestring"
      , "case-insensitive"
      , "containers"
      , "crypton"
      , "data-default-class"
      , "dhall"
      , "http2"
      , "http-semantics"
      , "http-types"
      , "katip"
      , "megaparsec"
      , "memory"
      , "network"
      , "optparse-applicative"
      , "prometheus-client"
      , "prometheus-metrics-ghc"
      , "random"
      , "text"
      , "time"
      , "time-manager"
      , "tls"
      , "vector"
      , "wai"
      , "warp"
      , "zeromq4-haskell"
      ]

-- Language extensions
let extensions =
      [ "BangPatterns"
      , "CApiFFI"
      , "DerivingStrategies"
      , "ForeignFunctionInterface"
      , "LambdaCase"
      , "NumericUnderscores"
      , "OverloadedStrings"
      , "PatternSynonyms"
      , "StrictData"
      , "PackageImports"
      ]

-- GHC options
let ghcOptions =
      [ "-O2"
      , "-threaded"
      , "-rtsopts"
      , "-with-rtsopts=-N -A64m -I0"
      , "-isrc"
      ]

-- External libraries (from Nix via .buckconfig.local)
let extraLibs =
      [ "tokenizers_cpp"
      , "tokenizers_c"
      , "sentencepiece"
      ]

-- Benchmark sources
let benchSrcs = [ "bench/Main.hs" ]

-- Benchmark packages (library packages + bench-specific)
let benchPackages = packages #
      [ "clock"
      , "deepseq"
      ]

-- Test sources
let testSrcs =
      [ "test/Main.hs"
      , "test/ChunkSpec.hs"
      , "test/ConfigurationSpec.hs"
      , "test/DecodeSpec.hs"
      , "test/EncodeSpec.hs"
      , "test/FrameSpec.hs"
      , "test/HotTableSpec.hs"
      , "test/ModelSpec.hs"
      , "test/ParseSpec.hs"
      , "test/RoundtripSpec.hs"
      , "test/StressSpec.hs"
      , "test/TokenizerFFISpec.hs"
      , "test/ToolCallSpec.hs"
      , "test/TypesSpec.hs"
      , "test/VarintSpec.hs"
      ]

-- Test packages (library packages + test-specific)
let testPackages = packages #
      [ "hspec"
      , "QuickCheck"
      , "temporary"
      ]

-- slide executable with FFI
let slide =
      (A.haskellFFIBinary "slide" (librarySrcs # appSrcs) cxxSrcs)
        with packages = packages
        with language_extensions = extensions
        with ghc_options = ghcOptions
        with extra_libs = extraLibs
        with include_dirs = [ "cbits" ]

-- test executable with FFI
let slideTest =
      (A.haskellFFIBinary "slide-test" (librarySrcs # testSrcs) cxxSrcs)
        with packages = testPackages
        with language_extensions = extensions # [ "ScopedTypeVariables" ]
        with ghc_options = [ "-O0", "-threaded", "-rtsopts", "-with-rtsopts=-N", "-isrc", "-itest" ]
        with extra_libs = extraLibs
        with include_dirs = [ "cbits" ]

-- benchmark executable with FFI (optimized)
let slideBench =
      (A.haskellFFIBinary "bench" (librarySrcs # benchSrcs) cxxSrcs)
        with packages = benchPackages
        with language_extensions = extensions
        with ghc_options = [ "-O2", "-threaded", "-rtsopts", "-with-rtsopts=-N -A64m -I0", "-isrc" ]
        with extra_libs = extraLibs
        with include_dirs = [ "cbits" ]

-- markov SSE generator (needs FFI for tokenizer)
let markovSrcs =
      [ "test/MarkovSSE.hs"
      , "src/Slide/HotTable.hs"
      , "src/Slide/Tokenizer.hs"
      , "src/Slide/Tokenizer/FFI.hs"
      , "src/Slide/Wire/Frame.hs"
      , "src/Slide/Wire/Types.hs"
      , "src/Slide/Wire/Varint.hs"
      ]

let markovPackages =
      [ "base"
      , "aeson"
      , "bytestring"
      , "containers"
      , "optparse-applicative"
      , "random"
      , "text"
      , "vector"
      , "zeromq4-haskell"
      ]

let markov =
      (A.haskellFFIBinary "markov" markovSrcs cxxSrcs)
        with packages = markovPackages
        with language_extensions = extensions
        with ghc_options = [ "-O2", "-threaded", "-rtsopts", "-with-rtsopts=-N", "-isrc", "-main-is", "MarkovSSE" ]
        with extra_libs = extraLibs
        with include_dirs = [ "cbits" ]

in  { rules = [ S.haskellFFIBinary slide, S.haskellFFITest slideTest, S.haskellFFIBinary slideBench, S.haskellFFIBinary markov ]
    , header =
        ''
        # Generated from BUILD.dhall
        # 
        # Library paths for tokenizers-cpp come from .buckconfig.local [slide] section
        # which is auto-generated by `nix develop`
        # The haskell_ffi_binary rule reads these paths via read_root_config()
        #
        # Benchmarks: buck2 run //:bench
        # Run specific: buck2 run //:bench -- encode decode
        # Throughput burst: buck2 run //:bench -- throughput
        # Markov SSE: buck2 run //:markov
        
        load("@toolchains//:haskell.bzl", "haskell_binary", "haskell_ffi_binary", "haskell_ffi_test")
        ''
    }
