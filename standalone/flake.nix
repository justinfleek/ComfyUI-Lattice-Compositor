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
            ];
            # Make sure C libraries are found
            LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [
              pkgs.zlib
              pkgs.openssl
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
        };
    };
}
