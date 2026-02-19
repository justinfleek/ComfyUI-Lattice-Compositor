# nix/prelude/phases.nix
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                              // phases bridge //
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
#     The bridge between typed actions and traditional mkDerivation phases.
#     Enables incremental adoption: use typed actions in one phase at a time.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Bridge for incremental adoption: convert typed actions to shell strings
# for use in traditional mkDerivation phases.
#
# This enables gradual migration: existing packages can use typed actions
# in one phase at a time without full rewrite.
#
{ lib
, wasm-plugin
}:

let
  inherit (wasm-plugin) actionsToShell;

  # Extract tool dependencies from actions (for manual nativeBuildInputs)
  # Users must add these manually: nativeBuildInputs = [ pkgs.jq ] ++ phases.toolDeps actions
  extractToolDeps = actions:
    lib.unique (
      lib.concatMap
        (action:
          if action.action or "" == "toolRun" then
            [ action.pkg ]
          else
            [ ])
        actions
    );

in
{
  # ──────────────────────────────────────────────────────────────────────────
  #                        // phases.interpret //
  # ──────────────────────────────────────────────────────────────────────────
  # Convert a list of typed actions to a shell script string.
  #
  # This is the bridge that enables incremental adoption:
  #
  #   stdenv.mkDerivation {
  #     pname = "my-package";
  #     # ... all existing attrs unchanged ...
  #
  #     # Replace just postInstall with typed actions
  #     postInstall = straylight.phases.interpret [
  #       {
  #         action = "toolRun";
  #         pkg = "${pkgs.jq}/bin/jq";
  #         args = [ "-r" ".version" "$out/package.json" ];
  #       }
  #       {
  #         action = "patchelfRpath";
  #         path = "bin/myapp";
  #         rpaths = [ "$out/lib" ];
  #       }
  #     ];
  #   }
  #
  # The actions come from WASM evaluation (via straylight.eval) or can be
  # constructed manually as attrsets matching the Action type.
  #
  # Returns: shell script string suitable for use in mkDerivation phases
  #
  interpret = actions:
    assert lib.isList actions;
    actionsToShell actions;

  # ──────────────────────────────────────────────────────────────────────────
  #                        // phases.toolDeps //
  # ──────────────────────────────────────────────────────────────────────────
  # Extract tool dependencies from actions.
  #
  # Usage:
  #   nativeBuildInputs = [ pkgs.jq pkgs.patchelf ]
  #     ++ straylight.phases.toolDeps myActions;
  #
  # This is a convenience helper. Tool deps are automatically tracked in
  # full typed packages, but for incremental adoption you must add them
  # manually.
  #
  toolDeps = actions:
    assert lib.isList actions;
    extractToolDeps actions;
}
