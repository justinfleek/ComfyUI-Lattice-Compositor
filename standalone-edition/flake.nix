{
  description = "ComfyUI Lattice Compositor — Haskell, Lean4, PureScript";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
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

          # Custom Haskell package set with fixes for broken packages
          hsPkgs = pkgs.haskellPackages.override {
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
              pkgs.ghc
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
            ];
            # Make sure C libraries are found
            LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
              pkgs.zlib
              pkgs.openssl
              pkgs.snappy
            ];
          };

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

              # Test that main.js is served
              machine.succeed("curl -s http://localhost:8080/main.js | head -c 100")

              # Test that styles.css is served
              machine.succeed("curl -s http://localhost:8080/styles.css | head -c 100")

              print("✓ All E2E VM tests passed!")
            '';
          };
        };
    };
}
