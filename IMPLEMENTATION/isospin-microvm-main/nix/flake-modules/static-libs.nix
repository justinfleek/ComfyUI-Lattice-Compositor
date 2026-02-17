# nix/flake-modules/static-libs.nix
#
# Static libraries required for Buck2 linking
#
# Provides:
#   packages.awsLcStatic - aws-lc with prefixed symbols
#   packages.libseccompStatic - static libseccomp
#   packages.zstdStatic - static zstd
#
# Usage:
#   export AWS_LC_LIB_DIR=$(nix build .#awsLcStatic --print-out-paths)/lib
#   export LIBSECCOMP_LIB_DIR=$(nix build .#libseccompStatic --print-out-paths)/lib
#   export ZSTD_LIB_DIR=$(nix build .#zstdStatic --print-out-paths)/lib
#
{ ... }:
{
  _class = "flake";

  config.perSystem =
    { pkgs, isospinConfig, ... }:
    let
      cfg = isospinConfig.static-libs;

      libseccompStatic = pkgs.libseccomp.overrideAttrs (old: {
        dontDisableStatic = true;
        configureFlags = (old.configureFlags or [ ]) ++ [
          "--enable-static"
          "--disable-shared"
        ];
      });

      awsLcStatic = pkgs.aws-lc.overrideAttrs (old: {
        cmakeFlags = (old.cmakeFlags or [ ]) ++ [
          "-DBUILD_SHARED_LIBS=OFF"
          "-DBORINGSSL_PREFIX=aws_lc_0_35_0"
          "-DBORINGSSL_PREFIX_HEADERS=${cfg.aws-lc-prefix-headers}"
        ];
        postInstall = ''
          if [ -f $out/lib/libcrypto.a ]; then
            cp $out/lib/libcrypto.a $out/lib/libaws_lc_0_35_0_crypto.a
          fi
          if [ -f $out/lib/libssl.a ]; then
            cp $out/lib/libssl.a $out/lib/libaws_lc_0_35_0_ssl.a
          fi
        '';
      });

      zstdStatic = (pkgs.zstd.override { static = true; }).out;
    in
    {
      _module.args = {
        inherit libseccompStatic awsLcStatic zstdStatic;
      };

      packages = {
        inherit libseccompStatic awsLcStatic zstdStatic;
      };
    };
}
