# nix/modules/flake/typed-build.nix
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                            // typed-build //
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
#     The matrix had its roots in primitive arcade games, in early
#     graphics programs and military experimentation with cranial
#     jacks. On the Sony, a two-dimensional space war faded behind
#     a forest of mathematically generated ferns, demonstrating the
#     spatial possibilities of logarithmic spirals.
#
#                                                         — Neuromancer
#
# Configuration module for Straylight typed build system (call-package).
# Allows enabling/disabling language backends for .hs, .purs, and .nix files.
#
#                                                                     // usage
#
#   {
#     inputs.straylight.url = "github:straylight-software/straylight";
#
#     outputs = { self, straylight, ... }:
#       straylight.lib.mkFlake { inherit inputs; } {
#         imports = [ straylight.modules.flake.typed-build ];
#
#         straylight.build = {
#           enable = true;
#           languages = {
#             haskell.enable = true;   # Enable .hs files (default: true)
#             purescript.enable = false; # Enable .purs files (default: false)
#             nix.enable = true;       # Enable .nix files (default: true)
#           };
#         };
#       };
#   }
#
# This configures which language backends are available in call-package.
# When a backend is disabled, call-package will throw a helpful error
# if someone tries to use that file extension.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
{ config, lib, ... }:
let
  cfg = config.straylight.build;
in
{
  _class = "flake";

  # ════════════════════════════════════════════════════════════════════════════
  # Options
  # ════════════════════════════════════════════════════════════════════════════
  options.straylight.build = {
    enable = lib.mkEnableOption "Straylight typed build system (call-package)";

    languages = {
      haskell = {
        enable = lib.mkOption {
          type = lib.types.bool;
          default = true;
          description = "Enable Haskell backend (.hs files)";
        };
      };

      purescript = {
        enable = lib.mkOption {
          type = lib.types.bool;
          default = false;
          description = ''
            Enable PureScript backend (.purs files).

            NOTE: PureScript WASM backend is not yet available.
            This option prepares infrastructure for when it becomes available.
          '';
        };
      };

      nix = {
        enable = lib.mkOption {
          type = lib.types.bool;
          default = true;
          description = "Enable Nix backend (.nix files, validated)";
        };
      };
    };
  };

  # ════════════════════════════════════════════════════════════════════════════
  # Config
  # ════════════════════════════════════════════════════════════════════════════
  config = lib.mkIf cfg.enable {
    # Export configuration for use in call-package
    # The actual enforcement happens in call-package implementation
    # (nix/_main.nix and nix/modules/flake/prelude.nix)
    #
    # This module provides the configuration interface. The call-package
    # functions check cfg.languages.*.enable to determine if a backend
    # should be available.
    #
    # Note: This is a configuration-only module. The actual call-package
    # implementation is in the prelude module and uses these options.
    straylight.build.config = {
      inherit (cfg.languages) haskell purescript nix;
    };
  };
}
