{
  description = "ComfyUI Lattice Compositor — Haskell, Lean4, PureScript";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      purescript-overlay,
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

          # UI static files for serving
          uiStatic = ./lattice-core/purescript/public;
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
          packages.lattice = pkgs.haskellPackages.callCabal2nix "lattice" ./. { };

          # Armitage build system CLI
          packages.armitage = pkgs.haskellPackages.callCabal2nix "lattice" ./. { };

          packages.ui = pkgs.buildNpmPackage {
            pname = "lattice-compositor-ui";
            version = "0.1.0";
            src = ./ui;
            npmDepsHash = "";
            buildPhase = "npm run build";
            installPhase = "cp -r dist $out";
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
                    root = "${uiStatic}";
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
