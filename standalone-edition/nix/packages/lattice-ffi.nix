# nix/packages/lattice-ffi.nix
#
# Build shared library for Haskell FFI bindings
# Exports C-compatible functions for Python interop
#
{ pkgs, prelude, lib }:

let
  inherit (prelude) ghc;
  
  # Haskell dependencies for FFI modules
  haskell-deps = hp: [
    hp.tasty
    hp.tasty-hunit
    hp.tasty-quickcheck
    hp.aeson
    hp.text
    hp.bytestring
    hp.crypton
    hp.containers
    hp.scientific
    hp.hashable
    hp.vector
    hp.unordered-containers
  ];
  
  #                                                                       // ghc
  ghc-with-deps = ghc.pkgs'.ghcWithPackages haskell-deps;
  
in
pkgs.stdenv.mkDerivation {
  pname = "lattice-ffi";
  version = "0.1.0";
  
  src = lib.cleanSourceWith {
    src = ../..;
    filter = path: type:
      let
        base-name = baseNameOf path;
      in
        # Include source files
        (lib.hasSuffix ".hs" base-name) ||
        # Include directories
        (type == "directory");
  };
  
  nativeBuildInputs = [
    ghc-with-deps
    pkgs.gmp
    pkgs.libffi
  ];
  
  # Build phase - compile FFI modules to shared library
  buildPhase = ''
    runHook preBuild
    
    echo "Building Lattice FFI shared library..."
    
    # Create build directory
    mkdir -p build
    
    # Compile all FFI modules together into shared library
    # Note: GHC will automatically compile dependencies
    # 
    #                                                                  // critical
    ghc -shared -dynamic -fPIC \
      -i$src/src \
      -i$src/nix \
      -optl-Wl,-soname,liblattice-ffi.so \
      -optl-Wl,--no-as-needed \
      $src/src/lattice/FFI/FrameInterpolation.hs \
      $src/src/lattice/FFI/ModelIntegrity.hs \
      $src/src/lattice/FFI/AudioStemSeparation.hs \
      $src/src/lattice/FFI/ProjectValidation.hs \
      $src/src/lattice/FFI/SVGPathParsing.hs \
      $src/src/lattice/FFI/KeyframeState.hs \
      $src/src/lattice/FFI/AnimationState.hs \
      $src/src/lattice/FFI/DatabaseFFI.hs \
      -o build/liblattice-ffi.so || {
        echo "FAILED: FFI library compilation failed"
        exit 1
      }
    
    echo "FFI library built successfully: build/liblattice-ffi.so"
    
    runHook postBuild
  '';
  
  # Install phase - copy library and headers
  installPhase = ''
    runHook preInstall
    
    mkdir -p $out/lib $out/include
    
    # Copy shared library
    cp build/liblattice-ffi.so $out/lib/
    
    # Create C header file with function declarations
    cat > $out/include/lattice-ffi.h << 'EOF'
/* Lattice FFI C Header
 * Auto-generated header for Python interop
 * Functions exported from Haskell FFI modules
 */

#ifndef LATTICE_FFI_H
#define LATTICE_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Frame Interpolation */
int32_t slowdown_to_factor(double slowdown);
char* validate_interpolation_params(const char* json_input);

/* Model Integrity */
char* compute_hash(const char* bytes, int32_t length);
int32_t verify_hash(const char* computed, const char* expected);
char* validate_decomposition_params(const char* json_input);

/* Audio Stem Separation */
char* get_model_config(const char* model_name);
char* get_available_models(void);
char* get_attribution_info(void);
char* validate_stem_separation_params(const char* json_input);

/* Project Validation */
char* calculate_max_depth(const char* json_input, int32_t current_depth);
char* validate_expressions(const char* json_input, const char* path);
char* validate_single_expression(const char* expression, const char* path);
char* validate_numeric_bounds(const char* json_input, const char* path);
char* validate_paths(const char* json_input, const char* path);
char* count_layers(const char* json_input);
char* validate_string_lengths(const char* json_input, const char* path);
char* validate_array_lengths(const char* json_input, const char* path);
int32_t validate_project_id(const char* project_id);

/* SVG Path Parsing */
char* parse_svg_to_paths(const char* svg_string, int32_t img_width, int32_t img_height);
char* parse_path_data(const char* path_data, int32_t path_idx);

/* Keyframe State */
char* safe_frame_ffi(const char* json_input);
char* find_property_by_path_ffi(const char* json_input);
char* find_surrounding_keyframes_ffi(const char* json_input);
char* has_keyframes_in_clipboard_ffi(const char* json_input);
char* has_position_separated_ffi(const char* json_input);
char* has_scale_separated_ffi(const char* json_input);
char* get_property_value_at_frame_ffi(const char* json_input);

/* Animation State */
char* has_work_area_ffi(const char* json_input);
char* effective_start_frame_ffi(const char* json_input);
char* get_current_frame_ffi(const char* json_input);
char* get_frame_count_ffi(const char* json_input);
char* get_fps_ffi(const char* json_input);
char* get_effective_end_frame_ffi(const char* json_input);
char* get_current_time_ffi(const char* json_input);

/* Database Operations */
char* database_query(const char* db_path, const char* sql_query);
char* initialize_schema(const char* db_path, const char* enabled_flags_json);
char* save_chat_message(const char* db_path, const char* message_json);
char* get_chat_history(const char* db_path, const char* project_id_json, int32_t limit);

#ifdef __cplusplus
}
#endif

#endif /* LATTICE_FFI_H */
EOF
    
    echo "Header file created: $out/include/lattice-ffi.h"
    
    runHook postInstall
  '';
  
  # Meta information
  meta = {
    description = "Lattice FFI shared library for Python interop";
    license = lib.licenses.mit;
    platforms = lib.platforms.all;
  };
}
