{
  description = "Weyl Motion Graphics Compositor for ComfyUI";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;
            cudaSupport = true;
          };
        };

        pythonEnv = pkgs.python311.withPackages (ps: with ps; [
          torch
          torchvision
          numpy
          pillow
          opencv4
          aiohttp
        ]);

      in {
        packages.default = pkgs.stdenv.mkDerivation {
          pname = "comfyui-weyl-compositor";
          version = "1.0.0";

          src = ./.;

          buildInputs = [
            pythonEnv
            pkgs.nodejs_20
          ];

          buildPhase = ''
            cd ui
            npm ci
            npm run build
            cd ..
          '';

          installPhase = ''
            mkdir -p $out/custom_nodes/comfyui-weyl-compositor
            cp -r nodes server web dist $out/custom_nodes/comfyui-weyl-compositor/
            cp __init__.py pyproject.toml $out/custom_nodes/comfyui-weyl-compositor/
          '';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            pythonEnv
            pkgs.nodejs_20
            pkgs.nodePackages.npm
          ];

          shellHook = ''
            echo "Weyl Compositor development environment"
            echo "Run 'cd ui && npm install && npm run dev' for frontend"
          '';
        };
      }
    );
}
