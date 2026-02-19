{
  description = "slide — nobody in la fucks with me, you got that?";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    systems.url = "github:nix-systems/default";
    flake-parts.url = "github:hercules-ci/flake-parts";

    # sensenet: build infrastructure, toolchains, nix-compile
    sensenet = {
      url = "github:straylight-software/sensenet/nix-compile/strict-straylight";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Rust tooling for tokenizers-cpp FFI
    crane.url = "github:ipetkov/crane";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    # Secrets management
    agenix-shell = {
      url = "github:aciceri/agenix-shell";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;

      imports = [
        inputs.sensenet.flakeModules.sensenet
      ];

      perSystem =
        { pkgs, system, config, ... }:
        let
          inherit (pkgs.haskell.packages) ghc912;

          rustPkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ (import inputs.rust-overlay) ];
          };
          craneLib = (inputs.crane.mkLib rustPkgs).overrideToolchain rustPkgs.rust-bin.stable.latest.default;

          tokenizers-cpp = pkgs.callPackage ./nix/tokenizers-cpp.nix { inherit craneLib; };

          agenixInstallScript = inputs.agenix-shell.lib.installationScript system {
            secrets.OPENROUTER_API_KEY.file = ./secrets/openrouter-api-key.age;
          };

          # GHC with all required packages
          ghcWithPackages = ghc912.ghcWithPackages (hp: [
            hp.aeson
            hp.async
            hp.blake3
            hp.bytestring
            hp.case-insensitive
            hp.clock
            hp.containers
            hp.crypton
            hp.data-default-class
            hp.deepseq
            hp.dhall
            hp.http2
            hp.http-semantics
            hp.http-types
            hp.katip
            hp.megaparsec
            hp.memory
            hp.network
            hp.optparse-applicative
            hp.prometheus-client
            hp.prometheus-metrics-ghc
            hp.random
            hp.text
            hp.time
            hp.time-manager
            hp.tls
            hp.vector
            hp.wai
            hp.warp
            hp.zeromq4-haskell
            hp.hspec
            hp.QuickCheck
            hp.temporary
          ]);

          # Shared build inputs for Haskell FFI binaries
          haskellBuildInputs = [
            tokenizers-cpp
            pkgs.zeromq
            pkgs.gcc
          ];

          # Build a Haskell FFI binary
          mkHaskellBinary = name: mainModule: srcs: pkgs.stdenv.mkDerivation {
            pname = name;
            version = "0.1.0";
            src = ./.;

            nativeBuildInputs = [ ghcWithPackages pkgs.gcc ];
            buildInputs = haskellBuildInputs;

            buildPhase = ''
              export LIBRARY_PATH="${tokenizers-cpp}/lib:$LIBRARY_PATH"
              export C_INCLUDE_PATH="${tokenizers-cpp}/include:$C_INCLUDE_PATH"
              export LD_LIBRARY_PATH="${tokenizers-cpp}/lib:$LD_LIBRARY_PATH"

              # Compile C++ FFI
              g++ -c -fPIC -I${tokenizers-cpp}/include \
                -std=c++17 -O2 \
                cbits/tokenizers_c.cpp -o tokenizers_c.o

              # Compile and link Haskell
              ghc -O2 -threaded \
                -main-is ${mainModule} \
                -XGHC2024 \
                -XBangPatterns \
                -XOverloadedStrings \
                -XNumericUnderscores \
                -XLambdaCase \
                -XPatternSynonyms \
                -XDerivingStrategies \
                -XStrictData \
                -isrc -itest -Icbits \
                -I${tokenizers-cpp}/include \
                -L${tokenizers-cpp}/lib \
                -optl-Wl,-rpath,${tokenizers-cpp}/lib \
                -lstdc++ -ltokenizers_cpp -ltokenizers_c -lsentencepiece \
                tokenizers_c.o \
                ${builtins.concatStringsSep " " srcs} \
                -o ${name}
            '';

            installPhase = ''
              mkdir -p $out/bin
              cp ${name} $out/bin/
            '';
          };

          # Tokenizers data directory
          tokenizersData = pkgs.runCommand "slide-tokenizers" {} ''
            mkdir -p $out
            cp -r ${./tokenizers}/* $out/
          '';

        in
        {
          # ══════════════════════════════════════════════════════════════════════
          # Packages
          # ══════════════════════════════════════════════════════════════════════
          packages = {
            # Tokenizer data files
            tokenizers = tokenizersData;

            # Main slide binary
            slide = mkHaskellBinary "slide" "Main" [
              "app/Main.hs"
              "src/Slide/Chunk.hs"
              "src/Slide/Configuration.hs"
              "src/Slide/HotTable.hs"
              "src/Slide/Model.hs"
              "src/Slide/Parse.hs"
              "src/Slide/Provider.hs"
              "src/Slide/Provider/HTTP2.hs"
              "src/Slide/Provider/OpenAI.hs"
              "src/Slide/Provider/OpenRouter.hs"
              "src/Slide/Provider/Vertex/Anthropic.hs"
              "src/Slide/Tokenizer.hs"
              "src/Slide/Tokenizer/FFI.hs"
              "src/Slide/Wire/Decode.hs"
              "src/Slide/Wire/Encode.hs"
              "src/Slide/Wire/Frame.hs"
              "src/Slide/Wire/Types.hs"
              "src/Slide/Wire/Varint.hs"
            ];

            # Markov generator
            markov = mkHaskellBinary "markov" "MarkovSSE" [
              "test/MarkovSSE.hs"
              "src/Slide/HotTable.hs"
              "src/Slide/Model.hs"
              "src/Slide/Tokenizer.hs"
              "src/Slide/Tokenizer/FFI.hs"
              "src/Slide/Wire/Frame.hs"
              "src/Slide/Wire/Types.hs"
              "src/Slide/Wire/Varint.hs"
            ];

            default = config.packages.slide;
          };

          # ══════════════════════════════════════════════════════════════════════
          # devShells — alias sensenet-default to default
          # ══════════════════════════════════════════════════════════════════════
          devShells.default = config.devShells.sensenet-default;

          # ══════════════════════════════════════════════════════════════════════
          # sensenet project
          # ══════════════════════════════════════════════════════════════════════
          sensenet.projects.default = {
            src = ./.;
            targets = [ "//:slide" ];
            toolchain = {
              cxx.enable = true;
              haskell = {
                enable = true;
                ghcpackages = ghc912;
                packages = hp: [
                  hp.aeson
                  hp.async
                  hp.blake3
                  hp.bytestring
                  hp.case-insensitive
                  hp.containers
                  hp.crypton
                  hp.data-default-class
                  hp.dhall
                  hp.http2
                  hp.http-semantics
                  hp.http-types
                  hp.katip
                  hp.megaparsec
                  hp.memory
                  hp.network
                  hp.optparse-applicative
                  hp.prometheus-client
                  hp.prometheus-metrics-ghc
                  hp.random
                  hp.text
                  hp.time
                  hp.time-manager
                  hp.tls
                  hp.vector
                  hp.wai
                  hp.warp
                  hp.zeromq4-haskell
                  # Test dependencies
                  hp.hspec
                  hp.hspec-discover
                  hp.QuickCheck
                  hp.temporary
                ];
              };
            };
            extrapackages = [
              tokenizers-cpp
              pkgs.zeromq
            ];
            extrabuckconfigsections = ''

              [slide]
              tokenizers_cpp_lib = ${tokenizers-cpp}/lib
              tokenizers_cpp_include = ${tokenizers-cpp}/include
            '';
            devshellpackages = [
              pkgs.dhall
              pkgs.dhall-json
              ghc912.cabal-install
              ghc912.haskell-language-server
              pkgs.age
            ];
            devshellhook = ''
              export LIBRARY_PATH="${tokenizers-cpp}/lib"
              export C_INCLUDE_PATH="${tokenizers-cpp}/include"
              export LD_LIBRARY_PATH="${tokenizers-cpp}/lib"

              source ${pkgs.lib.getExe agenixInstallScript}

              echo ""
              echo "  ╷┌─┐┐ ┬┬  ┌─┐┌┐┐┌─┐  ┐─┐┬  o┬─┐┌─┐"
              echo "  ││─┤└┬┘│  ├─ │││├─   └─┐│  ││ │├─ "
              echo "╶─┘┘ ┴ ┴ ┘─┘┴─┘┘└┘┴─┘  ──┘┘─┘┘┘─┘┴─┘"
              echo ""
              echo "  buck2 build //:slide"
              echo ""
            '';
          };

          # ══════════════════════════════════════════════════════════════════════
          # Apps - pure nix run, no devshell required
          # ══════════════════════════════════════════════════════════════════════
          apps = 
            let
              slidebin = "${config.packages.slide}/bin/slide";
              defaultTokenizer = "${tokenizersData}/llama-3-8b-Instruct/tokenizer.json";

              # Helper to create a jack app with a profile
              mkJackApp = name: model: {
                type = "app";
                program = toString (pkgs.writeShellScript "jack-${name}" ''
                  set -euo pipefail
                  : "''${OPENROUTER_API_KEY:?OPENROUTER_API_KEY required}"
                  exec ${slidebin} jack \
                    --provider openrouter \
                    --model "${model}" \
                    --api-key "$OPENROUTER_API_KEY" \
                    --tokenizer identity \
                    "$@"
                '');
              };
            in {
              # ─────────────────────────────────────────────────────────────────
              # OpenRouter profiles (use OPENROUTER_API_KEY from env)
              # ─────────────────────────────────────────────────────────────────
              claude = mkJackApp "claude" "anthropic/claude-sonnet-4";
              deepseek = mkJackApp "deepseek" "deepseek/deepseek-r1";
              llama = mkJackApp "llama" "meta-llama/llama-3.1-70b-instruct";
              gemini = mkJackApp "gemini" "google/gemini-2.0-flash-001";
              kimi = mkJackApp "kimi" "moonshotai/kimi-k2.5";

              # ─────────────────────────────────────────────────────────────────
              # Generic jack with model override
              # ─────────────────────────────────────────────────────────────────
              jack = {
                type = "app";
                program = toString (pkgs.writeShellScript "jack" ''
                  set -euo pipefail
                  : "''${OPENROUTER_API_KEY:?OPENROUTER_API_KEY required}"
                  MODEL=''${MODEL:-"anthropic/claude-sonnet-4"}
                  exec ${slidebin} jack \
                    --provider openrouter \
                    --model "$MODEL" \
                    --api-key "$OPENROUTER_API_KEY" \
                    --tokenizer identity \
                    "$@"
                '');
              };

              # ─────────────────────────────────────────────────────────────────
              # Vertex AI (requires gcloud auth)
              # ─────────────────────────────────────────────────────────────────
              vertex = {
                type = "app";
                program = toString (pkgs.writeShellScript "jack-vertex" ''
                  set -euo pipefail
                  command -v gcloud >/dev/null || { echo "gcloud required"; exit 1; }
                  TOKEN=$(gcloud auth print-access-token)
                  PROJECT=$(gcloud config get-value project)
                  REGION=''${REGION:-us-central1}
                  ENDPOINT="https://''${REGION}-aiplatform.googleapis.com/v1beta1/projects/''${PROJECT}/locations/''${REGION}/endpoints/openai/chat/completions"
                  exec ${slidebin} jack \
                    "$ENDPOINT" \
                    --provider vertex \
                    --api-key "$TOKEN" \
                    --tokenizer identity \
                    "$@"
                '');
              };

              # ─────────────────────────────────────────────────────────────────
              # Listener
              # ─────────────────────────────────────────────────────────────────
              listen = {
                type = "app";
                program = toString (pkgs.writeShellScript "listen" ''
                  set -euo pipefail
                  TOKENIZER=''${TOKENIZER:-${defaultTokenizer}}
                  exec ${slidebin} listen \
                    --tokenizer "$TOKENIZER" \
                    "$@"
                '');
              };

              # ─────────────────────────────────────────────────────────────────
              # Listener with OpenAI output format
              # ─────────────────────────────────────────────────────────────────
              listen-openai = {
                type = "app";
                program = toString (pkgs.writeShellScript "listen-openai" ''
                  set -euo pipefail
                  TOKENIZER=''${TOKENIZER:-identity}
                  exec ${slidebin} listen \
                    --tokenizer "$TOKENIZER" \
                    --format openai \
                    "$@"
                '');
              };

              # ─────────────────────────────────────────────────────────────────
              # Listener with debug frame dumps (hyperwall mode)
              # ─────────────────────────────────────────────────────────────────
              listen-debug = {
                type = "app";
                program = toString (pkgs.writeShellScript "listen-debug" ''
                  set -euo pipefail
                  TOKENIZER=''${TOKENIZER:-${tokenizersData}/llama-3-8b-Instruct/tokenizer.json}
                  exec ${config.packages.slide}/bin/slide listen \
                    --tokenizer "$TOKENIZER" \
                    --dump-frames \
                    -v \
                    "$@"
                '');
              };

              # ─────────────────────────────────────────────────────────────────
              # Markov SIGIL frame generator (pure nix build)
              # ─────────────────────────────────────────────────────────────────
              markov = {
                type = "app";
                program = toString (pkgs.writeShellScript "markov" ''
                  set -euo pipefail
                  TOKENIZER=''${TOKENIZER:-${tokenizersData}/llama-3-8b-Instruct/tokenizer.json}
                  exec ${config.packages.markov}/bin/markov \
                    --tokenizer "$TOKENIZER" \
                    "$@"
                '');
              };
            };
        };
    };
}
