# nix/prelude/straylight.nix
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                // straylight //
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
#     He'd operated on an almost permanent adrenaline high, a byproduct
#     of youth and proficiency, jacked into a custom cyberspace deck
#     that projected his disembodied consciousness into the consensual
#     hallucination that was the matrix.
#
#                                                         — Neuromancer
#
# The straylight interface: evaluate typed Haskell/PureScript expressions from Nix.
#
# Zero bash. Zero untyped strings. One interface.
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# USAGE:
#
#   # Basic: evaluate a typed package
#   straylight.eval "Straylight.Packages.Nvidia.nccl" {}
#
#   # With arguments
#   straylight.eval "Straylight.Build.withFlags" { pkg = myPkg; flags = ["-O3"]; }
#
#   # Import a whole module
#   nvidia = straylight.import "Straylight.Packages.Nvidia"
#   nvidia.nccl   # → derivation
#   nvidia.cudnn  # → derivation
#
# SETUP:
#
#   # In your flake:
#   wasm-infra = import ./nix/prelude/wasm-plugin.nix { ... };
#   straylight = import ./nix/prelude/straylight.nix {
#     inherit lib pkgs;
#     wasmFile = wasm-infra.straylightWasm;
#   };
#
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
{
  lib,
  pkgs,
  wasmFile,
  stdenvFn ? pkgs.stdenv.mkDerivation,
}:
let
  # Import the WASM plugin infrastructure
  wasmPlugin = import ./wasm-plugin.nix {
    inherit lib;
    inherit (pkgs) stdenv runCommand;
    # ghc-wasm-meta not needed for loading, only for building
    ghc-wasm-meta = null;
  };

  # ────────────────────────────────────────────────────────────────────────────
  # Module name → WASM export name mapping
  # ────────────────────────────────────────────────────────────────────────────
  # "Straylight.Packages.Nvidia.nccl" → "nvidia_nccl"
  # "Straylight.Nix.Packages.ZlibNg" → "zlib_ng"
  #
  moduleToExport =
    modulePath:
    let
      parts = lib.splitString "." modulePath;
      # Take everything after known prefixes
      relevantParts =
        if lib.length parts >= 3 && lib.elemAt parts 0 == "Straylight" && lib.elemAt parts 1 == "Packages" then
          lib.drop 2 parts
        else if
          lib.length parts >= 4
          && lib.elemAt parts 0 == "Straylight"
          && lib.elemAt parts 1 == "Nix"
          && lib.elemAt parts 2 == "Packages"
        then
          lib.drop 3 parts
        else
          parts;
      # CamelCase to snake_case
      toSnake =
        s:
        let
          chars = lib.stringToCharacters s;
          converted = lib.concatMapStrings (
            c:
            if lib.elem c (lib.stringToCharacters "ABCDEFGHIJKLMNOPQRSTUVWXYZ") then "_${lib.toLower c}" else c
          ) chars;
        in
        lib.removePrefix "_" converted;
    in
    lib.concatMapStringsSep "_" toSnake relevantParts;

  # ────────────────────────────────────────────────────────────────────────────
  # Feature check
  # ────────────────────────────────────────────────────────────────────────────
  requireWasm =
    if wasmPlugin.features.can-load then
      true
    else
      throw ''
        ════════════════════════════════════════════════════════════════════════════════
        straylight.eval requires straylight-nix with builtins.wasm support.
        ════════════════════════════════════════════════════════════════════════════════

        Current status: ${wasmPlugin.features.status}

        To enable:
          1. Build and install straylight-nix:
             nix build github:straylight-software/straylight-nix

          2. Use it as your Nix binary

          3. Verify: nix eval --expr 'builtins ? wasm'  # should return true

        ════════════════════════════════════════════════════════════════════════════════
      '';

  # ────────────────────────────────────────────────────────────────────────────
  # Known module exports (for straylight.import)
  # ────────────────────────────────────────────────────────────────────────────
  knownModules = {
    "Straylight.Packages.Nvidia" = [
      "nccl"
      "cudnn"
      "tensorrt"
      "cutensor"
      "cusparselt"
      "cutlass"
    ];
    "Straylight.Nix.Packages.Nvidia" = [
      "nccl"
      "cudnn"
      "tensorrt"
      "cutensor"
      "cusparselt"
      "cutlass"
    ];
    "Straylight.Packages" = [
      "zlib-ng"
      "fmt"
      "mdspan"
      "cutlass"
      "rapidjson"
      "nlohmann-json"
      "spdlog"
      "catch2"
      "abseil-cpp"
    ];
  };

in
{
  # ════════════════════════════════════════════════════════════════════════════
  # straylight.eval : String -> AttrSet -> NixValue
  # ════════════════════════════════════════════════════════════════════════════
  # Evaluate a typed expression by module path.
  #
  # Examples:
  #   straylight.eval "Straylight.Packages.Nvidia.nccl" {}
  #   straylight.eval "Straylight.Build.withFlags" { pkg = myPkg; flags = ["-O3"]; }
  #
  eval =
    modulePath: args:
    assert requireWasm;
    let
      exportName = moduleToExport modulePath;
      spec = builtins.wasm wasmFile exportName args;
    in
    wasmPlugin.buildFromSpec { inherit spec pkgs stdenvFn; };

  # ════════════════════════════════════════════════════════════════════════════
  # straylight.import : String -> AttrSet
  # ════════════════════════════════════════════════════════════════════════════
  # Import a module as an attrset of its exports.
  #
  # Examples:
  #   nvidia = straylight.import "Straylight.Packages.Nvidia"
  #   nvidia.nccl  # → derivation
  #
  import =
    moduleName:
    assert requireWasm;
    let
      exports =
        knownModules.${moduleName}
          or (throw "Unknown module: ${moduleName}. Known: ${toString (builtins.attrNames knownModules)}");
      mkExport =
        name:
        let
          exportName = moduleToExport "${moduleName}.${name}";
          spec = builtins.wasm wasmFile exportName { };
        in
        {
          inherit name;
          value = wasmPlugin.buildFromSpec { inherit spec pkgs stdenvFn; };
        };
    in
    builtins.listToAttrs (map mkExport exports);

  # ════════════════════════════════════════════════════════════════════════════
  # straylight.spec : String -> AttrSet -> AttrSet
  # ════════════════════════════════════════════════════════════════════════════
  # Get raw spec without building (for debugging/introspection).
  #
  spec =
    modulePath: args:
    assert requireWasm;
    let
      exportName = moduleToExport modulePath;
    in
    builtins.wasm wasmFile exportName args;

  # ════════════════════════════════════════════════════════════════════════════
  # straylight.phases : Incremental Adoption Bridge
  # ════════════════════════════════════════════════════════════════════════════
  # Convert typed actions to shell strings for use in traditional mkDerivation phases.
  #
  # This enables gradual migration: existing packages can use typed actions
  # in one phase at a time without full rewrite.
  #
  # Example:
  #   postInstall = straylight.phases.interpret [
  #     { action = "toolRun"; pkg = "${pkgs.jq}/bin/jq"; args = [ "-r" ".version" "$out/package.json" ]; }
  #     { action = "patchelfRpath"; path = "bin/myapp"; rpaths = [ "$out/lib" ]; }
  #   ];
  #
  phases = import ./phases.nix {
    inherit lib;
    wasm-plugin = wasmPlugin;
  };

  # ════════════════════════════════════════════════════════════════════════════
  # Introspection
  # ════════════════════════════════════════════════════════════════════════════

  inherit (wasmPlugin) features;
  inherit knownModules;
  inherit moduleToExport;
}
