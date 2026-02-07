-- |
-- Module      : Color.FFICodegen
-- Description : Generate TypeScript FFI bridge code from Lean definitions
-- 
-- Generates Node.js/VSCode extension code that calls Haskell FFI functions
-- via Python bridge or direct C bindings
--

import Color.Extract

namespace Color.FFICodegen

open Color.Extract

/-! ## FFI Bridge Code Generation -/

/-- Generate TypeScript FFI bridge module -/
def generateFFIBridge : String :=
"-- |
-- Auto-generated TypeScript FFI bridge for theme generation
-- DO NOT EDIT - regenerate with `lake exe extract ffi-typescript`
--
-- This module bridges TypeScript (VSCode extension) to Haskell FFI functions
-- via Python subprocess calls or direct C bindings.
--

import { ThemeConfig, ThemeVariant } from \"./types\";
import * as vscode from \"vscode\";
import { exec } from \"child_process\";
import { promisify } from \"util\";

const execAsync = promisify(exec);

/**
 * Path to Python bridge script (calls Haskell FFI)
 * Set via environment variable or use default
 */
const PYTHON_BRIDGE_PATH = process.env.LATTICE_PYTHON_BRIDGE || 
  \"python\";

/**
 * Path to Haskell FFI shared library
 * Set via environment variable or use default
 */
const HASKELL_LIB_PATH = process.env.LATTICE_FFI_LIB || 
  \"liblattice-ffi.so\";

/**
 * Generate theme variants from configuration
 * 
 * Calls Haskell FFI function: generateThemeVariantsFFI
 * via Python bridge script
 * 
 * @param config Theme configuration
 * @returns Promise resolving to array of theme variants
 */
export async function generateThemeVariants(
  config: ThemeConfig
): Promise<ThemeVariant[]> {
  try {
    // Serialize config to JSON
    const configJson = JSON.stringify(config);
    
    // Call Python bridge script
    const pythonScript = `
import sys
import json
from pathlib import Path

# Add lattice FFI to path
sys.path.insert(0, str(Path(__file__).parent.parent / \"src\" / \"lattice\" / \"FFI\"))

from theme_generator_ffi import generate_theme_variants_ffi

if __name__ == \"__main__\":
    config_json = sys.stdin.read()
    result = generate_theme_variants_ffi(config_json)
    print(result)
`;
    
    // Execute Python script with config as stdin
    const { stdout, stderr } = await execAsync(
      `echo ${JSON.stringify(configJson)} | ${PYTHON_BRIDGE_PATH} -c \"${pythonScript}\"`,
      { maxBuffer: 10 * 1024 * 1024 }  // 10MB buffer
    );
    
    if (stderr) {
      console.error(\"Python bridge error:\", stderr);
    }
    
    // Parse result
    const result = JSON.parse(stdout.trim());
    
    if (result.error) {
      throw new Error(result.error);
    }
    
    return result as ThemeVariant[];
  } catch (error) {
    vscode.window.showErrorMessage(
      `Theme generation failed: ${error instanceof Error ? error.message : String(error)}`
    );
    throw error;
  }
}

/**
 * Generate single theme from configuration
 * 
 * Calls Haskell FFI function: generateThemeFFI
 * 
 * @param config Theme configuration
 * @returns Promise resolving to base16 palette
 */
export async function generateTheme(
  config: ThemeConfig
): Promise<Base16Palette> {
  try {
    const configJson = JSON.stringify(config);
    
    const pythonScript = `
import sys
import json
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / \"src\" / \"lattice\" / \"FFI\"))

from theme_generator_ffi import generate_theme_ffi

if __name__ == \"__main__\":
    config_json = sys.stdin.read()
    result = generate_theme_ffi(config_json)
    print(result)
`;
    
    const { stdout, stderr } = await execAsync(
      `echo ${JSON.stringify(configJson)} | ${PYTHON_BRIDGE_PATH} -c \"${pythonScript}\"`,
      { maxBuffer: 10 * 1024 * 1024 }
    );
    
    if (stderr) {
      console.error(\"Python bridge error:\", stderr);
    }
    
    const result = JSON.parse(stdout.trim());
    
    if (result.error) {
      throw new Error(result.error);
    }
    
    return result as Base16Palette;
  } catch (error) {
    vscode.window.showErrorMessage(
      `Theme generation failed: ${error instanceof Error ? error.message : String(error)}`
    );
    throw error;
  }
}

/**
 * Validate theme configuration
 * Ensures all values are within valid ranges
 */
export function validateThemeConfig(config: ThemeConfig): boolean {
  // Validate hue: 0-360
  if (config.baseColor.hue < 0 || config.baseColor.hue >= 360) {
    return false;
  }
  if (config.heroColor.hue < 0 || config.heroColor.hue >= 360) {
    return false;
  }
  
  // Validate saturation: 0-1
  if (config.baseColor.saturation < 0 || config.baseColor.saturation > 1) {
    return false;
  }
  if (config.heroColor.saturation < 0 || config.heroColor.saturation > 1) {
    return false;
  }
  
  // Validate lightness: 0-1
  if (config.baseColor.lightness < 0 || config.baseColor.lightness > 1) {
    return false;
  }
  if (config.heroColor.lightness < 0 || config.heroColor.lightness > 1) {
    return false;
  }
  
  // Validate black balance: 0-1
  if (config.blackBalance < 0 || config.blackBalance > 1) {
    return false;
  }
  
  return true;
}
"

/-- Generate Python bridge module -/
def generatePythonBridge : String :=
"-- |
-- Auto-generated Python bridge for theme generation FFI
-- DO NOT EDIT - regenerate with `lake exe extract ffi-python`
--
-- This module provides Python wrappers for Haskell FFI functions
-- that can be called from Node.js/VSCode extension
--

import json
import ctypes
import sys
from pathlib import Path
from typing import Dict, List, Any, Optional

# Import native FFI bindings
try:
    from ._native import (
        _get_function,
        _cstring_to_python,
        _python_to_cstring,
        init_haskell_rts,
    )
except ImportError:
    # Fallback if _native not available
    def _get_function(*args, **kwargs):
        return None
    def _cstring_to_python(ptr):
        return None
    def _python_to_cstring(s):
        return None
    def init_haskell_rts():
        return True

# Initialize Haskell RTS on import
init_haskell_rts()

def generate_theme_variants_ffi(config_json: str) -> str:
    \"\"\"
    Generate theme variants from JSON configuration.
    
    Args:
        config_json: JSON string with ThemeConfig
        
    Returns:
        JSON string with array of ThemeVariant objects
    \"\"\"
    func = _get_function(
        \"generateThemeVariantsFFI\",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p  # Returns CString pointer
    )
    
    if func is None:
        return json.dumps({\"error\": \"FFI function generateThemeVariantsFFI not available\"})
    
    try:
        result_ptr = func(_python_to_cstring(config_json))
        result_json = _cstring_to_python(result_ptr)
        
        if result_json is None:
            return json.dumps({\"error\": \"No result from Haskell function\"})
        
        return result_json
    except Exception as e:
        return json.dumps({\"error\": str(e)})

def generate_theme_ffi(config_json: str) -> str:
    \"\"\"
    Generate single theme from JSON configuration.
    
    Args:
        config_json: JSON string with ThemeConfig
        
    Returns:
        JSON string with Base16Palette object
    \"\"\"
    func = _get_function(
        \"generateThemeFFI\",
        argtypes=[ctypes.c_char_p],
        restype=ctypes.c_void_p
    )
    
    if func is None:
        return json.dumps({\"error\": \"FFI function generateThemeFFI not available\"})
    
    try:
        result_ptr = func(_python_to_cstring(config_json))
        result_json = _cstring_to_python(result_ptr)
        
        if result_json is None:
            return json.dumps({\"error\": \"No result from Haskell function\"})
        
        return result_json
    except Exception as e:
        return json.dumps({\"error\": str(e)})

if __name__ == \"__main__\":
    # CLI interface for testing
    if len(sys.argv) < 2:
        print(\"Usage: python theme_generator_ffi.py <config_json>\")
        sys.exit(1)
    
    config_json = sys.argv[1]
    result = generate_theme_variants_ffi(config_json)
    print(result)
"

end Color.FFICodegen
