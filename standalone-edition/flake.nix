{
  description = "ComfyUI Lattice Compositor — Haskell, Lean4, PureScript";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    hasktorch = {
      url = "github:hasktorch/hasktorch";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # NVIDIA SDK with CUDA 13.1 + TensorRT for GPU inference
    nvidia-sdk = {
      url = "path:../IMPLEMENTATION/nvidia-sdk-main";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    purs-nix = {
      url = "github:purs-nix/purs-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskemathesis = {
      url = "github:weyl-ai/haskemathesis";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # PureScript frontend libraries (non-flake sources for purs-nix)
    hydrogen = {
      url = "github:straylight-software/hydrogen";
      flake = false;
    };
    halogen-html-renderer = {
      url = "github:straylight-software/halogen-html-renderer";
      flake = false;
    };
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      hasktorch,
      nvidia-sdk,
      purs-nix,
      purescript-overlay,
      haskemathesis,
      hydrogen,
      halogen-html-renderer,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];

      perSystem =
        {
          config,
          pkgs,
          system,
          ...
        }:
        let
          pursOverlayPkgs = import nixpkgs {
            inherit system;
            overlays = [ purescript-overlay.overlays.default ];
          };
          pythonEnv = pkgs.python3.withPackages (ps: [
            ps.aiohttp
            ps.numpy
            ps.pillow
            ps.scipy
          ]);

          # purs-nix setup
          ps = purs-nix {
            inherit system;
            pkgs = nixpkgs.legacyPackages.${system};
          };

          # PureScript package definition using purs-nix
          lattice-ps = ps.purs {
            dir = ./lattice-core/purescript;
            srcs = [ "src" ];
            dependencies = with ps.ps-pkgs; [
              aff
              aff-promise
              arraybuffer-types
              argonaut-codecs
              argonaut-core
              argonaut-generic
              arrays
              canvas
              console
              datetime
              effect
              either
              enums
              exceptions
              foldable-traversable
              foreign
              foreign-object
              gen
              halogen
              halogen-subscriptions
              halogen-vdom
              integers
              js-timers
              lists
              maybe
              media-types
              newtype
              now
              nullable
              numbers
              ordered-collections
              partial
              prelude
              quickcheck
              random
              refs
              safe-coerce
              spec
              spec-discovery
              spec-quickcheck
              string-parsers
              strings
              transformers
              tuples
              typelevel-prelude
              uuid
              web-dom
              web-events
              web-file
              web-html
              web-socket
              web-storage
              web-uievents
            ];
          };

          # ════════════════════════════════════════════════════════════════════
          #                                                     // cuda // hasktorch
          # ════════════════════════════════════════════════════════════════════
          #
          # Nixpkgs with CUDA support + nvidia-sdk overlay + hasktorch overlay
          # This provides GPU-accelerated libtorch and TensorRT
          #
          pkgsCuda = import nixpkgs {
            inherit system;
            config = {
              allowUnfree = true;
              cudaSupport = true;
            };
            overlays = [
              nvidia-sdk.overlays.default
              hasktorch.overlays.default
            ];
          };

          # NVIDIA SDK components for TensorRT FFI
          nvidiaSdk = nvidia-sdk.packages.${system}.nvidia-sdk;
          tensorrt = nvidia-sdk.packages.${system}.tensorrt;

          # Nixpkgs with hasktorch overlay (CPU fallback for non-CUDA systems)
          pkgsWithHasktorch = import nixpkgs {
            inherit system;
            overlays = [ hasktorch.overlays.default ];
          };

          # Custom Haskell package set with fixes for broken packages
          # Uses CUDA-enabled pkgs on x86_64-linux, CPU fallback elsewhere
          hsPkgBase = if system == "x86_64-linux" then pkgsCuda else pkgsWithHasktorch;
          hsPkgs = hsPkgBase.haskellPackages.override {
            overrides = hself: hsuper: {
              # http2-tls is marked broken in nixpkgs, but works fine
              http2-tls = pkgs.haskell.lib.markUnbroken hsuper.http2-tls;
              # Use haskemathesis from flake input
              haskemathesis = haskemathesis.packages.${system}.default;
            };
          };

          # PureScript UI bundle - purs-nix handles compilation + esbuild bundling
          lattice-bundle = lattice-ps.bundle {
            esbuild = {
              format = "iife";
              minify = true;
              outfile = "main.js";
            };
            main = true;
            module = "Lattice.UI.Main";
          };

        in
        {
          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.nodejs_20
              pythonEnv
              pkgs.ripgrep
              pkgs.fd
              pkgs.biome
              # Use GHC with hasktorch (CUDA-enabled on x86_64-linux)
              (hsPkgs.ghcWithPackages (ps: [
                ps.hasktorch
                ps.vector
                ps.containers
                ps.mtl
              ]))
              pkgs.cabal-install
              pkgs.haskell-language-server
              pkgs.gh
              pursOverlayPkgs.purs
              pursOverlayPkgs.spago-unstable
              pursOverlayPkgs.purs-tidy
              pursOverlayPkgs.purs-backend-es
              pkgs.esbuild
              pkgs.dhall
              pkgs.dhall-json
              # C libraries for Haskell packages
              pkgs.zlib
              pkgs.pkg-config
              pkgs.openssl
              pkgs.snappy
              pkgs.protobuf
              # CMake for TensorRT C++ library
              pkgs.cmake
              pkgs.ninja
            ];
            # Make sure C libraries are found at runtime
            LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath (
              [
                pkgs.zlib
                pkgs.openssl
                pkgs.snappy
              ]
              ++ pkgs.lib.optionals (system == "x86_64-linux") [
                nvidiaSdk
                tensorrt
              ]
            );
            # Make sure C libraries are found at link time
            LIBRARY_PATH = pkgs.lib.makeLibraryPath (
              [
                pkgs.zlib
                pkgs.openssl
                pkgs.snappy
              ]
              ++ pkgs.lib.optionals (system == "x86_64-linux") [
                nvidiaSdk
                tensorrt
              ]
            );

            # CUDA/TensorRT environment variables (x86_64-linux only)
            shellHook = pkgs.lib.optionalString (system == "x86_64-linux") ''
              export CUDA_PATH="${nvidiaSdk}"
              export CUDA_HOME="${nvidiaSdk}"
              export TENSORRT_HOME="${tensorrt}"
              echo "CUDA 13.1 + TensorRT available for GPU inference"
              echo "CUDA_PATH=$CUDA_PATH"
              echo "TENSORRT_HOME=$TENSORRT_HOME"
            '';
          };

          # CUDA-enabled devShell (explicit, always tries CUDA)
          devShells.cuda = pkgs.lib.optionalAttrs (system == "x86_64-linux") (
            pkgs.mkShell {
              packages = [
                (hsPkgs.ghcWithPackages (ps: [
                  ps.hasktorch
                  ps.vector
                  ps.containers
                  ps.mtl
                ]))
                pkgs.cabal-install
                nvidiaSdk
                tensorrt
                pkgs.cmake
                pkgs.ninja
                pkgs.pkg-config
              ];

              LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
                nvidiaSdk
                tensorrt
              ];

              shellHook = ''
                export CUDA_PATH="${nvidiaSdk}"
                export CUDA_HOME="${nvidiaSdk}"
                export TENSORRT_HOME="${tensorrt}"
                echo "CUDA devShell: CUDA 13.1 + TensorRT"
              '';
            }
          );

          # Haskell packages built with cabal
          packages.lattice = hsPkgs.callCabal2nix "lattice" ./. { };

          # Armitage build system CLI
          packages.armitage = hsPkgs.callCabal2nix "lattice" ./. { };

          # PureScript UI - built from source using purs-nix
          packages.ui = pkgs.stdenvNoCC.mkDerivation {
            pname = "lattice-compositor-ui";
            version = "0.1.0";
            src = ./lattice-core/purescript;

            # No build phase needed - purs-nix already bundled the JS
            dontBuild = true;

            installPhase = ''
                            runHook preInstall
                            mkdir -p $out

                            # Copy the bundled JS from purs-nix (bundle is a single file)
                            cp ${lattice-bundle} $out/main.js

                            # Copy static assets from public/
                            if [ -d public ]; then
                              cp public/index.html $out/ 2>/dev/null || true
                              cp public/styles.css $out/ 2>/dev/null || true
                            fi

                            # Create index.html if not present
                            if [ ! -f $out/index.html ]; then
                              cat > $out/index.html << 'EOF'
              <!DOCTYPE html>
              <html lang="en">
              <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>Lattice Compositor</title>
                <link rel="stylesheet" href="styles.css">
              </head>
              <body>
                <div id="app"></div>
                <script src="main.js"></script>
              </body>
              </html>
              EOF
                            fi

                            # Create empty styles.css if not present
                            if [ ! -f $out/styles.css ]; then
                              touch $out/styles.css
                            fi

                            runHook postInstall
            '';

            meta = {
              description = "Lattice Compositor UI - PureScript/Halogen";
              license = pkgs.lib.licenses.mit;
            };
          };

          # Default package
          packages.default = config.packages.lattice;

          # NixOS VM test for E2E testing
          checks.vm-e2e = pkgs.testers.runNixOSTest {
            name = "lattice-e2e";

            nodes.machine =
              { pkgs, ... }:
              {
                # Enable graphical environment for browser tests
                services.xserver.enable = true;
                services.xserver.displayManager.lightdm.enable = true;
                services.xserver.desktopManager.xfce.enable = true;

                # Serve the UI on port 8080
                services.nginx = {
                  enable = true;
                  virtualHosts."localhost" = {
                    listen = [
                      {
                        addr = "127.0.0.1";
                        port = 8080;
                      }
                    ];
                    root = "${config.packages.ui}";
                    locations."/" = {
                      tryFiles = "$uri $uri/ /index.html";
                    };
                  };
                };

                # Required for headless browser testing
                environment.systemPackages = with pkgs; [
                  chromium
                  nodejs_20
                  curl
                ];

                # Open firewall for local testing
                networking.firewall.allowedTCPPorts = [ 8080 ];
              };

            testScript = ''
              machine.start()
              machine.wait_for_unit("nginx.service")
              machine.wait_for_open_port(8080)

              # Test that the UI is served correctly
              result = machine.succeed("curl -s http://localhost:8080/")
              assert "lattice" in result.lower() or "<!DOCTYPE html>" in result, f"UI not served correctly: {result[:200]}"

              # Test that main.js is served (use -o /dev/null to avoid broken pipe with head)
              result = machine.succeed("curl -sf http://localhost:8080/main.js -o /dev/null -w '%{http_code}'")
              assert result.strip() == "200", f"main.js not served correctly: HTTP {result}"

              # Test that styles.css is served
              result = machine.succeed("curl -sf http://localhost:8080/styles.css -o /dev/null -w '%{http_code}'")
              assert result.strip() == "200", f"styles.css not served correctly: HTTP {result}"

              print("✓ All E2E VM tests passed!")
            '';
          };
        };
    };
}
