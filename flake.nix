{
  description = "ComfyUI Lattice Compositor — Haskell, Lean4, PureScript";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs@{ flake-parts, nixpkgs, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];

      perSystem = { config, pkgs, system, ... }: let
        pythonEnv = pkgs.python3.withPackages (ps: [
          ps.aiohttp
          ps.numpy
          ps.pillow
          ps.scipy
        ]);
      in {
        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.nodejs_20
            pythonEnv
            pkgs.ripgrep
            pkgs.fd
            pkgs.biome
            pkgs.ghc
            pkgs.cabal-install
            pkgs.gh
          ];
        };

        packages.ui = pkgs.buildNpmPackage {
          pname = "lattice-compositor-ui";
          version = "0.1.0";
          src = ./ui;
          npmDepsHash = "";
          buildPhase = "npm run build";
          installPhase = "cp -r dist $out";
        };
      };
    };
}
