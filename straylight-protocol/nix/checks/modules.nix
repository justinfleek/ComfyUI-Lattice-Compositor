# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                              // straylight // module // compilation // tests
#
#  Verifies that all Straylight.* modules compile successfully.
#  This catches import errors, type errors, and missing dependencies.
#
#  We use GHC's --make mode which handles dependency ordering automatically.
# ════════════════════════════════════════════════════════════════════════════
{
  pkgs,
  system,
  lib,
  ...
}:
let
  # Get script source and GHC from the overlay
  inherit (pkgs.straylight.script) src ghc;

  # ════════════════════════════════════════════════════════════════════════════
  #                                                                      // test
  # ════════════════════════════════════════════════════════════════════════════
  # Compile all Straylight.* modules using GHC's --make mode.
  # This automatically handles dependency ordering and verifies everything compiles.

  test-straylight-modules = pkgs.stdenv.mkDerivation {
    name = "test-straylight-modules";
    inherit src;
    dontUnpack = true;

    nativeBuildInputs = [ ghc ];

    buildPhase = ''
      runHook preBuild

      echo "Compiling all Straylight modules..."
      echo ""

      # Create temp directory for build artifacts
      mkdir -p build

      # Use --make to compile all modules with automatic dependency resolution
      # We compile the "top-level" modules that pull in everything else:
      # - Straylight.Script.Tools (imports all tool wrappers)
      # - Straylight.Script.Vm (imports Vfio, Oci, Config)
      # - Straylight.Nix (imports Types, Value, FFI)
      # - Straylight.Nix.Syntax (imports Derivation, CMake)

      ghc --make -Wall -Wno-unused-imports \
        -hidir build -odir build \
        -i$src \
        $src/Straylight/Script.hs \
        $src/Straylight/Script/Tools.hs \
        $src/Straylight/Script/Vm.hs \
        $src/Straylight/Script/Oci.hs \
        $src/Straylight/Nix.hs \
        $src/Straylight/Nix/Syntax.hs \
        2>&1 || {
          echo ""
          echo "FAILED: Module compilation failed"
          exit 1
        }

      echo ""
      echo "All Straylight modules compiled successfully"

      runHook postBuild
    '';

    installPhase = ''
      mkdir -p $out
      echo "SUCCESS" > $out/SUCCESS
      echo "All Straylight modules compiled successfully" >> $out/SUCCESS
    '';

    meta = {
      description = "Test that all Straylight.* Haskell modules compile successfully";
    };
  };

  # ════════════════════════════════════════════════════════════════════════════
  #                                                                      // test
  # ════════════════════════════════════════════════════════════════════════════
  # Verify all compiled scripts in straylight.script.compiled build successfully

  test-straylight-compiled-scripts = pkgs.runCommand "test-straylight-compiled-scripts" { } ''
    echo "Verifying compiled Straylight scripts..."
    echo ""

    # Check that key binaries exist and are executable
    ${lib.concatMapStringsSep "\n"
      (name: ''
        echo "  Checking ${name}..."
        if [ ! -x "${pkgs.straylight.script.compiled.${name}}/bin/${name}" ]; then
          echo "FAILED: ${name} not found or not executable"
          exit 1
        fi
        echo "    ${pkgs.straylight.script.compiled.${name}}/bin/${name}"
      '')
      [
        "vfio-bind"
        "vfio-unbind"
        "vfio-list"
        "oci-run"
        "oci-gpu"
        "oci-inspect"
        "oci-pull"
        "fhs-run"
        "gpu-run"
        "fc-run"
        "fc-build"
        "ch-run"
        "ch-gpu"
      ]
    }

    mkdir -p $out
    echo "SUCCESS" > $out/SUCCESS
    echo "All compiled Straylight scripts verified" >> $out/SUCCESS
  '';

in
# Only run on Linux (Straylight.Nix has FFI bindings that may need Linux)
lib.optionalAttrs (system == "x86_64-linux" || system == "aarch64-linux") {
  inherit
    test-straylight-modules
    test-straylight-compiled-scripts
    ;
}
