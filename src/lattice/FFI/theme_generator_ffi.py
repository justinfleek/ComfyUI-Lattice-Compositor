"""
Python FFI bridge for theme generation
Wraps _native.py to provide theme generation functions
"""

import sys
import json
from pathlib import Path

# Add this directory to path
sys.path.insert(0, str(Path(__file__).parent))

try:
    from _native import call_ffi_function
except ImportError:
    # Fallback if _native not available
    def call_ffi_function(function_name: str, input_json: str) -> str:
        return json.dumps({"error": "FFI library not available"})

def generate_theme_variants_ffi(config_json: str) -> str:
    """
    Generate theme variants from JSON configuration.
    
    Args:
        config_json: JSON string with ThemeConfig
        
    Returns:
        JSON string with array of ThemeVariant objects
    """
    return call_ffi_function("generateThemeVariantsFFI", config_json)

def generate_theme_ffi(config_json: str) -> str:
    """
    Generate single theme from JSON configuration.
    
    Args:
        config_json: JSON string with ThemeConfig
        
    Returns:
        JSON string with Base16Palette object
    """
    return call_ffi_function("generateThemeFFI", config_json)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        config_json = sys.stdin.read()
    else:
        config_json = sys.argv[1]
    
    result = generate_theme_variants_ffi(config_json)
    print(result)
