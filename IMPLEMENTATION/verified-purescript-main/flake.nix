{
  description = "Verified PureScript - Proof-carrying PureScript extracted from Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };

        # Run a Lean file
        lean-run =
          name: file:
          pkgs.writeShellScriptBin name ''
            exec ${pkgs.lean4}/bin/lean --run ${./.}/${file}.lean "$@"
          '';

      in
      {
        packages = {
          # Core verified modules (no axioms, no sorries)
          verified-prelude = lean-run "verified-prelude" "VerifiedPrelude";
          system-f = lean-run "system-f" "SystemFComplete";
          system-f-poly = lean-run "system-f-poly" "SystemFPoly";
          typeclasses = lean-run "typeclasses" "TypeClasses";

          # Code generation / parsing
          ps-parser = lean-run "ps-parser" "PSParser";
          proof-carrying = lean-run "proof-carrying" "ProofCarryingAST";
          extraction = lean-run "extraction" "Extraction";
          summary = lean-run "summary" "Summary";

          default = self.packages.${system}.verified-prelude;
        };

        apps = {
          # Verified core
          verified-prelude = {
            type = "app";
            program = "${self.packages.${system}.verified-prelude}/bin/verified-prelude";
          };
          system-f = {
            type = "app";
            program = "${self.packages.${system}.system-f}/bin/system-f";
          };
          system-f-poly = {
            type = "app";
            program = "${self.packages.${system}.system-f-poly}/bin/system-f-poly";
          };
          typeclasses = {
            type = "app";
            program = "${self.packages.${system}.typeclasses}/bin/typeclasses";
          };

          # Code generation
          ps-parser = {
            type = "app";
            program = "${self.packages.${system}.ps-parser}/bin/ps-parser";
          };
          proof-carrying = {
            type = "app";
            program = "${self.packages.${system}.proof-carrying}/bin/proof-carrying";
          };
          extraction = {
            type = "app";
            program = "${self.packages.${system}.extraction}/bin/extraction";
          };
          summary = {
            type = "app";
            program = "${self.packages.${system}.summary}/bin/summary";
          };

          default = self.apps.${system}.verified-prelude;
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [ pkgs.lean4 ];

          shellHook = ''
            echo "═══════════════════════════════════════════════════════════"
            echo "  // verified purescript //"
            echo "  Proof-carrying PureScript extracted from Lean 4"
            echo "═══════════════════════════════════════════════════════════"
            echo ""
            echo "Verified core (no axioms):"
            echo "  nix run .#verified-prelude   Prelude combinators + algebraic laws"
            echo "  nix run .#system-f           STLC with substitution lemma"
            echo "  nix run .#system-f-poly      System F with type polymorphism"
            echo "  nix run .#typeclasses        Eq, Semigroup, Monoid, Functor, Monad"
            echo ""
            echo "Code generation:"
            echo "  nix run .#ps-parser          Parse + annotate PureScript"
            echo "  nix run .#proof-carrying     Proof-carrying AST demo"
            echo "  nix run .#extraction         Code extraction utilities"
            echo "  nix run .#summary            Project overview"
            echo ""
            echo "Direct:"
            echo "  lean --run VerifiedPrelude.lean"
            echo "  lean --run SystemFComplete.lean"
            echo ""
          '';
        };
      }
    );
}
