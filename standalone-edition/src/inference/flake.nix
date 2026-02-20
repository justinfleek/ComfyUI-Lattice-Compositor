{
  description = "Lattice Diffusion Inference - HaskTorch + TensorRT";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs =
    inputs@{
      flake-parts,
      nixpkgs,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" ];

      perSystem =
        {
          config,
          pkgs,
          system,
          ...
        }:
        let
          # CUDA toolkit version
          cudaVersion = "12";

          # TensorRT paths (adjust based on your installation)
          tensorrtPath = "/opt/tensorrt";

          # Build the C++ inference library
          lattice-inference = pkgs.stdenv.mkDerivation {
            pname = "lattice-inference";
            version = "0.1.0";

            src = ./.;

            nativeBuildInputs = with pkgs; [
              cmake
              ninja
              pkg-config
            ];

            buildInputs = with pkgs; [
              cudaPackages.cudatoolkit
              cudaPackages.cudnn
              # TensorRT needs to be provided externally or via overlay
            ];

            cmakeFlags = [
              "-DCMAKE_BUILD_TYPE=Release"
              "-DCMAKE_CUDA_ARCHITECTURES=89;86;80;75" # Ada, Ampere, Turing
            ];

            # Set CUDA paths
            preConfigure = ''
              export CUDA_PATH=${pkgs.cudaPackages.cudatoolkit}
              export CUDNN_PATH=${pkgs.cudaPackages.cudnn}
            '';

            meta = {
              description = "Lattice diffusion inference C++ library";
              license = pkgs.lib.licenses.mit;
              platforms = [ "x86_64-linux" ];
            };
          };

          # Haskell package set with our diffusion library
          hsPkgs = pkgs.haskellPackages.override {
            overrides = hself: hsuper: {
              # Add vector for GPU buffer management
              lattice-diffusion = hself.callCabal2nix "lattice" ../../. {
                # Link against our C++ library
                # lattice-inference = lattice-inference;
              };
            };
          };
        in
        {
          # Development shell with all CUDA tools
          devShells.default = pkgs.mkShell {
            packages = with pkgs; [
              # Build tools
              cmake
              ninja
              pkg-config
              gnumake

              # CUDA
              cudaPackages.cudatoolkit
              cudaPackages.cudnn

              # Haskell
              ghc
              cabal-install
              haskell-language-server

              # Debugging
              gdb
              valgrind
              nvidia-nsight
            ];

            # Environment variables for CUDA
            shellHook = ''
              export CUDA_PATH=${pkgs.cudaPackages.cudatoolkit}
              export CUDNN_PATH=${pkgs.cudaPackages.cudnn}
              export LD_LIBRARY_PATH=${pkgs.cudaPackages.cudatoolkit}/lib:${pkgs.cudaPackages.cudnn}/lib:$LD_LIBRARY_PATH
              export LIBRARY_PATH=${pkgs.cudaPackages.cudatoolkit}/lib:${pkgs.cudaPackages.cudnn}/lib:$LIBRARY_PATH

              # Check for TensorRT
              if [ -d "${tensorrtPath}" ]; then
                export TENSORRT_PATH="${tensorrtPath}"
                export LD_LIBRARY_PATH="${tensorrtPath}/lib:$LD_LIBRARY_PATH"
                export LIBRARY_PATH="${tensorrtPath}/lib:$LIBRARY_PATH"
                export CPLUS_INCLUDE_PATH="${tensorrtPath}/include:$CPLUS_INCLUDE_PATH"
                echo "TensorRT found at ${tensorrtPath}"
              else
                echo "Warning: TensorRT not found at ${tensorrtPath}"
                echo "Set TENSORRT_PATH or install TensorRT to /opt/tensorrt"
              fi

              echo "CUDA development environment ready"
              echo "  CUDA: ${pkgs.cudaPackages.cudatoolkit.version}"
              echo "  cuDNN: ${pkgs.cudaPackages.cudnn.version}"
            '';
          };

          # Development shell for pure Haskell work (no CUDA)
          devShells.haskell = pkgs.mkShell {
            packages = with pkgs; [
              ghc
              cabal-install
              haskell-language-server
            ];
          };

          # C++ library package
          packages.lattice-inference = lattice-inference;

          # Default package
          packages.default = lattice-inference;
        };
    };
}
