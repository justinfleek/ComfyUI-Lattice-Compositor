{
  description = "Isospin Buck2 toolchain flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      rust-overlay,
    }:
    let
      inherit (nixpkgs) lib;
      systems = [ "x86_64-linux" ];
      forAllSystems =
        fn:
        lib.genAttrs systems (
          system:
          fn (
            import nixpkgs {
              inherit system;
              overlays = [ (import rust-overlay) ];
            }
          )
        );
    in
    {
      packages = forAllSystems (pkgs: {
        rustc = pkgs.rust-bin.stable."1.89.0".default.override {
          extensions = [
            "rust-src"
            "clippy"
            "rustfmt"
          ];
          targets = [ "x86_64-unknown-linux-gnu" ];
        };

        clippy = pkgs.rust-bin.stable."1.89.0".clippy;

        python3 = pkgs.python3;

        cxx = pkgs.stdenv.mkDerivation {
          name = "buck2-cxx";
          dontUnpack = true;
          dontCheck = true;
          nativeBuildInputs = [ pkgs.makeWrapper ];
          buildPhase = ''
            function capture_env() {
              local -ar vars=(
                NIX_CC_WRAPPER_TARGET_HOST_
                NIX_CFLAGS_COMPILE
                NIX_DONT_SET_RPATH
                NIX_ENFORCE_NO_NATIVE
                NIX_HARDENING_ENABLE
                NIX_IGNORE_LD_THROUGH_GCC
                NIX_LDFLAGS
                NIX_NO_SELF_RPATH
              )
              for prefix in "''${vars[@]}"; do
                for v in $( eval 'echo "''${!'"$prefix"'@}"' ); do
                  echo "--set"
                  echo "$v"
                  echo "''${!v}"
                done
              done
            }

            mkdir -p "$out/bin"
            for tool in ar nm objcopy ranlib strip; do
              ln -st "$out/bin" "$NIX_CC/bin/$tool"
            done
            mapfile -t < <(capture_env)
            makeWrapper "$NIX_CC/bin/$CC" "$out/bin/cc" "''${MAPFILE[@]}"
            makeWrapper "$NIX_CC/bin/$CXX" "$out/bin/c++" "''${MAPFILE[@]}"
          '';
        };

        # Build aws-lc with static libraries
        aws-lc = pkgs.aws-lc.overrideAttrs (oldAttrs: {
          cmakeFlags = (oldAttrs.cmakeFlags or [ ]) ++ [
            "-DBUILD_SHARED_LIBS=OFF"
          ];

          # Custom install to match aws-lc-sys expectations
          postInstall = ''
            # Rename static libraries to match aws-lc-sys expectations
            if [ -f $out/lib/libcrypto.a ]; then
              cp $out/lib/libcrypto.a $out/lib/libaws_lc_0_35_0_crypto.a
            fi
            if [ -f $out/lib/libssl.a ]; then
              cp $out/lib/libssl.a $out/lib/libaws_lc_0_35_0_ssl.a
            fi
          '';
        });
      });
    };
}
