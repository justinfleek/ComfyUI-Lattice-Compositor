{
  description = "s4: GPU inference runtime for NVFP4 quantization and SageAttention";

  inputs = {
    weyl-compile.url = "path:/home/b7r6/src/staging/weyl-compile";
    nixpkgs.follows = "weyl-compile/nixpkgs";
  };

  outputs =
    {
      self,
      weyl-compile,
      nixpkgs,
      ...
    }@inputs:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;

      # Import nixpkgs with weyl-std overlay
      mkWeylPkgs =
        system:
        import nixpkgs {
          inherit system;
          overlays = [ inputs.weyl-compile.inputs.weyl-std.overlays.default ];
        };
    in
    {
      # Development shells
      devShells = forAllSystems (
        system:
        let
          pkgs = mkWeylPkgs system;
          weyl-pkgs = weyl-compile.packages.${system};
        in
        {
          default = pkgs.mkShell {
            name = "s4-dev";

            buildInputs = [
              # Buck2 and toolchains from weyl-compile
              weyl-pkgs.buck2

              # Python for testing
              (pkgs.python3.withPackages (
                ps: with ps; [
                  pytest
                  hypothesis
                  pybind11
                ]
              ))

              # Development tools
              pkgs.valgrind
              pkgs.gdb
              pkgs.clang-tools
              pkgs.git
            ];

            shellHook = ''
              echo "s4 development environment"
              echo "  Buck2: ${weyl-pkgs.buck2}/bin/buck2"
              echo ""
              echo "Quick start:"
              echo "  buck2 build //:s4_core          # Build header-only core"
              echo "  buck2 build //src/cuda:nvfp4    # Build CUDA kernels"
              echo "  buck2 test //...                # Run all tests"
              echo ""

              # Set up Buck2 environment
              export CUDA_PATH="${weyl-pkgs.cuda}"
              export PATH="${weyl-pkgs.buck2}/bin:$PATH"
            '';
          };
        }
      );

      # Packages
      packages = forAllSystems (
        system:
        let
          pkgs = mkWeylPkgs system;
          weyl-pkgs = weyl-compile.packages.${system};

          # Use weyl-std's stdenv with CUDA support
          weylStdenv = pkgs.weyl.stdenv.cuda or pkgs.weyl.stdenv.default;

          # C++ toolchain for Buck2 - unwrapped clang with proper includes
          cxxToolchain = pkgs.runCommand "s4-cxx-toolchain" { } ''
            mkdir -p $out/bin

            # Unwrapped clang binaries (not the nix wrapper)
            ln -s ${weylStdenv.cc.cc}/bin/clang $out/bin/cc
            ln -s ${weylStdenv.cc.cc}/bin/clang++ $out/bin/c++

            # Bintools from stdenv
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/ar $out/bin/ar
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/nm $out/bin/nm
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/objcopy $out/bin/objcopy
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/ranlib $out/bin/ranlib
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/strip $out/bin/strip
            ln -s ${weylStdenv.cc.bintools.bintools}/bin/ld $out/bin/ld

            # Create metadata for buck2-nix to find includes
            mkdir -p $out/nix-support
            echo "${weylStdenv.cc.cc.lib}/lib/clang/${weylStdenv.cc.cc.version}/include" > $out/nix-support/clang-resource-dir
            echo "${pkgs.glibc.dev}/include" > $out/nix-support/libc-include
            echo "${pkgs.gcc.cc}/include/c++/${pkgs.gcc.cc.version}" > $out/nix-support/libcxx-include
          '';
        in
        {
          # Export custom cxx toolchain
          cxx = cxxToolchain;

          # Re-export other weyl-compile packages
          inherit (weyl-pkgs) cuda python3 buck2;

          # Core library (header-only, no CUDA)
          s4-core = pkgs.stdenv.mkDerivation {
            pname = "s4-core";
            version = "0.1.0";
            src = ./.;

            nativeBuildInputs = [ weyl-pkgs.buck2 ];

            buildPhase = ''
              export PATH="${weyl-pkgs.buck2}/bin:$PATH"
              buck2 build //:s4_core
            '';

            installPhase = ''
              mkdir -p $out/include
              cp -r s4 $out/include/
            '';

            meta = {
              description = "s4 core library (header-only, host-only)";
              license = pkgs.lib.licenses.mit;
            };
          };

          # Full library with CUDA components
          s4-cuda = pkgs.stdenv.mkDerivation {
            pname = "s4-cuda";
            version = "0.1.0";
            src = ./.;

            nativeBuildInputs = [
              weyl-pkgs.buck2
              weyl-pkgs.cuda
            ];

            buildPhase = ''
              export PATH="${weyl-pkgs.buck2}/bin:$PATH"
              export CUDA_PATH="${weyl-pkgs.cuda}"
              buck2 build //src/cuda:nvfp4 //src/attention:attention
            '';

            installPhase = ''
              mkdir -p $out/{include,lib}
              cp -r s4 $out/include/
              cp -r buck-out/*/gen/src/cuda/*.a $out/lib/ || true
              cp -r buck-out/*/gen/src/attention/*.a $out/lib/ || true
            '';

            meta = {
              description = "s4 full library with CUDA support";
              license = pkgs.lib.licenses.mit;
            };
          };

          default = self.packages.${system}.s4-cuda;
        }
      );

      # Checks for `nix flake check`
      checks = forAllSystems (system: {
        build-core = self.packages.${system}.s4-core;
        build-cuda = self.packages.${system}.s4-cuda;
      });
    };
}
