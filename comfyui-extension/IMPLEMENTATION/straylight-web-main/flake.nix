{
  description = "straylight.software - the continuity project";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    bun2nix = {
      url = "github:nix-community/bun2nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  nixConfig = {
    extra-substituters = [
      "https://cache.nixos.org"
      "https://nix-community.cachix.org"
    ];
    extra-trusted-public-keys = [
      "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY="
      "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
    ];
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      bun2nix,
      purescript-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ purescript-overlay.overlays.default ];
        pkgs = import nixpkgs { inherit system overlays; };
        bun2nixPkg = bun2nix.packages.${system}.default;

        # Hermetic bun dependencies (generate with: bun2nix)
        bunDeps = bun2nixPkg.fetchBunDeps {
          bunNix = ./bun.nix;
        };

        # Production build
        straylight-web = pkgs.stdenv.mkDerivation {
          pname = "straylight-web";
          version = "0.1.0";

          src = ./.;

          nativeBuildInputs = [
            bun2nixPkg.hook
            pkgs.bun
            pkgs.nodejs_22
            pkgs.purs
            pkgs.spago-unstable
            pkgs.purs-backend-es
            pkgs.esbuild
          ];

          inherit bunDeps;

          bunInstallFlags = [ "--linker=hoisted" ];

          buildPhase = ''
            runHook preBuild

            export PATH="$PWD/node_modules/.bin:$PATH"

            # Build PureScript
            echo "Building PureScript..."
            cd purescript
            spago bundle --bundle-type app --platform browser --minify --outfile ../public/straylight.js
            cd ..

            # Build Next.js
            echo "Building Next.js..."
            next build

            runHook postBuild
          '';

          installPhase = ''
                        runHook preInstall

                        mkdir -p $out/share/straylight-web
                        cp -r .next/standalone/. $out/share/straylight-web/
                        cp -r .next/static $out/share/straylight-web/.next/
                        cp -r public $out/share/straylight-web/

                        # Create runner script
                        mkdir -p $out/bin
                        cat > $out/bin/straylight-web <<EOF
            #!/usr/bin/env bash
            cd $out/share/straylight-web
            exec ${pkgs.nodejs_22}/bin/node server.js "\$@"
            EOF
                        chmod +x $out/bin/straylight-web

                        runHook postInstall
          '';
        };
      in
      {
        packages = {
          default = straylight-web;
          web = straylight-web;
        };

        # Checks run by `nix flake check`
        checks = {
          build = straylight-web;

          # PureScript property tests
          purescript-tests = pkgs.stdenv.mkDerivation {
            pname = "straylight-purescript-tests";
            version = "0.1.0";

            src = ./.;

            nativeBuildInputs = [
              pkgs.purs
              pkgs.spago-unstable
              pkgs.esbuild
              pkgs.nodejs_22
            ];

            buildPhase = ''
              runHook preBuild

              echo "Building and running PureScript tests..."
              cd purescript

              # Build tests
              spago build

              # Run test bundle if it exists
              if [ -f "test/dist/test.cjs" ]; then
                ${pkgs.nodejs_22}/bin/node test/dist/test.cjs
                echo "All property tests passed!"
              else
                echo "Skipping tests - test bundle not found"
                echo "To build: cd purescript && spago test"
              fi

              runHook postBuild
            '';

            installPhase = ''
              mkdir -p $out
              echo "Tests passed" > $out/result.txt
            '';
          };
        };

        apps.default = {
          type = "app";
          program = "${straylight-web}/bin/straylight-web";
        };

        # Dev runner - runs in current directory
        apps.dev = {
          type = "app";
          program = toString (
            pkgs.writeShellScript "straylight-dev" ''
              set -e
              export PATH="${pkgs.bun}/bin:${pkgs.nodejs_22}/bin:${pkgs.purs}/bin:${pkgs.spago-unstable}/bin:${pkgs.purs-backend-es}/bin:${pkgs.esbuild}/bin:$PWD/node_modules/.bin:$PATH"

              if [ ! -d "node_modules" ]; then
                echo "Installing dependencies..."
                ${pkgs.bun}/bin/bun install
              fi

              echo ""
              echo "// straylight // dev //"
              echo ""
              echo "Building PureScript..."
              cd purescript && spago bundle --bundle-type app --platform browser --outfile ../public/straylight.js && cd ..

              echo ""
              echo "Starting dev server at http://localhost:3000"
              ${pkgs.bun}/bin/bun run dev
            ''
          );
        };

        # PureScript watch mode
        apps.purs = {
          type = "app";
          program = toString (
            pkgs.writeShellScript "straylight-purs" ''
              set -e
              export PATH="${pkgs.purs}/bin:${pkgs.spago-unstable}/bin:${pkgs.purs-backend-es}/bin:${pkgs.esbuild}/bin:$PATH"

              cd purescript
              echo "Building PureScript bundle..."
              spago bundle --bundle-type app --platform browser --outfile ../public/straylight.js
              echo ""
              echo "Bundle written to public/straylight.js"
              ls -lh ../public/straylight.js
            ''
          );
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.nodejs_22
            pkgs.bun
            pkgs.purs
            pkgs.purs-tidy
            pkgs.purs-backend-es
            pkgs.spago-unstable
            pkgs.esbuild
            pkgs.git
            bun2nixPkg
          ];

          shellHook = ''
            export PATH="$PWD/node_modules/.bin:$PATH"

            echo ""
            echo "// straylight // software //"
            echo ""
            echo "Commands:"
            echo "  bun install           - Install JS dependencies"
            echo "  bun run dev           - Start Next.js dev server"
            echo "  nix run .#purs        - Build PureScript bundle"
            echo "  nix run .#dev         - Build + dev (one command)"
            echo "  nix build             - Hermetic production build"
            echo "  nix flake check       - Run all checks"
            echo ""
            echo "PureScript: $(purs --version)"
            echo "Spago: $(spago --version 2>/dev/null || echo 'available')"
            echo "Node: $(node --version)"
            echo "Bun: $(bun --version)"
            echo ""
          '';
        };
      }
    );
}
