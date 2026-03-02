{
  description = "Radix Pure - Pure PureScript/Halogen UI components + Verified PureScript extraction";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      purescript-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [ purescript-overlay.overlays.default ];
        pkgs = import nixpkgs { inherit system overlays; };

        # Radix component generator
        radix-compiler = pkgs.writeShellScriptBin "radix-compiler" ''
          exec ${pkgs.lean4}/bin/lean --run ${./compiler/RadixCompiler.lean} "$@"
        '';

        # Lean4-to-PureScript demos
        lean-demo =
          name:
          pkgs.writeShellScriptBin "lean-${name}" ''
            exec ${pkgs.lean4}/bin/lean --run ${./lean4-to-purescript}/${name}.lean "$@"
          '';

      in
      {
        packages = {
          compiler = radix-compiler;
          default = radix-compiler;

          # Verified extraction demos
          ps-parser = lean-demo "PSParser";
          verified-prelude = lean-demo "VerifiedPrelude";
          system-f = lean-demo "SystemFComplete";
          system-f-poly = lean-demo "SystemFPoly";
          typeclasses = lean-demo "TypeClasses";
          proof-carrying = lean-demo "ProofCarryingAST";
        };

        apps = {
          # Radix compiler
          default = {
            type = "app";
            program = "${radix-compiler}/bin/radix-compiler";
          };
          compiler = self.apps.${system}.default;

          # Halogen example app
          example = {
            type = "app";
            program = "${
              pkgs.writeShellApplication {
                name = "radix-halogen-example";
                runtimeInputs = [
                  pkgs.spago-unstable
                  pkgs.purs
                  pkgs.python3
                ];
                text = ''
                  set -euo pipefail

                  PORT="''${PORT:-1234}"
                  echo "Building PureScript example..."
                  spago build
                  echo ""
                  echo "═══════════════════════════════════════════════════════════"
                  echo "  Radix Pure Example"
                  echo "  Open http://localhost:''${PORT}/example/ in your browser"
                  echo "═══════════════════════════════════════════════════════════"
                  echo ""
                  exec python3 -m http.server "''${PORT}" --directory .
                '';
              }
            }/bin/radix-halogen-example";
          };

          # Verified extraction demos
          ps-parser = {
            type = "app";
            program = "${lean-demo "PSParser"}/bin/lean-PSParser";
          };
          verified-prelude = {
            type = "app";
            program = "${lean-demo "VerifiedPrelude"}/bin/lean-VerifiedPrelude";
          };
          system-f = {
            type = "app";
            program = "${lean-demo "SystemFComplete"}/bin/lean-SystemFComplete";
          };
          system-f-poly = {
            type = "app";
            program = "${lean-demo "SystemFPoly"}/bin/lean-SystemFPoly";
          };
          typeclasses = {
            type = "app";
            program = "${lean-demo "TypeClasses"}/bin/lean-TypeClasses";
          };
          proof-carrying = {
            type = "app";
            program = "${lean-demo "ProofCarryingAST"}/bin/lean-ProofCarryingAST";
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.purs
            pkgs.spago-unstable
            pkgs.purs-tidy
            pkgs.purs-backend-es
            pkgs.nodejs_22
            pkgs.lean4
          ];

          shellHook = ''
            echo "═══════════════════════════════════════════════════════════"
            echo "  Radix Pure + Verified PureScript"
            echo "═══════════════════════════════════════════════════════════"
            echo ""
            echo "Radix (component generation):"
            echo "  nix run .                       Show help"
            echo "  nix run . -- Dialog             Generate Dialog skeleton"
            echo "  nix run . -- Tabs               Generate Tabs skeleton"
            echo ""
            echo "Verified PureScript (proofs):"
            echo "  nix run .#verified-prelude      Prelude combinators + laws"
            echo "  nix run .#system-f              STLC, no axioms"
            echo "  nix run .#typeclasses           Monad laws for List"
            echo "  nix run .#ps-parser             Parse + annotate PureScript"
            echo ""
            echo "Build:"
            echo "  spago build                     Build PureScript"
            echo ""
          '';
        };
      }
    );
}
