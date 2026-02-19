{
  description = "Bulletproof types - everything from Lean proofs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{ flake-parts, ... }:
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
          self',
          inputs',
          pkgs,
          system,
          lib,
          ...
        }:
        let
          elan = pkgs.elan;

          # Apply purescript-overlay for spago-unstable (registry-based, no git race condition)
          ps-pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [ inputs.purescript-overlay.overlays.default ];
          };

          python-env = pkgs.python311.withPackages (
            ps: with ps; [
              nanobind
              numpy
              pytest
            ]
          );

        in
        {
          # ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
          #                                                              // dev // shell
          # Lean/Lake builds are done manually, not through Nix
          # (Lake's non-deterministic builds break Nix's FOD model)
          # ════════════════════════════════════════════════════════════════════════════
          devShells.default = pkgs.mkShell {
            packages = [
              elan
              pkgs.git
              pkgs.cacert
              python-env
              pkgs.meson
              pkgs.ninja
              pkgs.pkg-config
              pkgs.elmPackages.elm
              pkgs.elmPackages.elm-format
              pkgs.nodejs
              pkgs.gnumake
              ps-pkgs.purs
              ps-pkgs.spago-unstable
              ps-pkgs.purs-tidy
            ];

            shellHook = ''
              echo ""
              echo "lattice-core dev shell"
              echo ""
              echo "Lean build (run manually):"
              echo "  cd lean && lake build"
              echo ""
              echo "First time setup:"
              echo "  cd lean && lake update && lake build"
              echo ""
            '';
          };
        };
    };
}
