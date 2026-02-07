import { ThemeConfig, ThemeVariant } from "./types";
import { exec } from "child_process";
import { promisify } from "util";
import * as path from "path";
import * as vscode from "vscode";

const execAsync = promisify(exec);

const PYTHON_BRIDGE_PATH = process.env.LATTICE_PYTHON_BRIDGE || "python";
const FFI_SCRIPT_PATH = path.join(
  __dirname,
  "..",
  "..",
  "..",
  "src",
  "lattice",
  "FFI",
  "theme_generator_ffi.py"
);

/**
 * Generate theme variants from configuration
 * 
 * Calls Python bridge script which calls Haskell FFI
 * 
 * @param config Theme configuration
 * @returns Promise resolving to array of theme variants
 */
export async function generateThemeVariants(
  config: ThemeConfig
): Promise<ThemeVariant[]> {
  const configJson = JSON.stringify(config);
  
  try {
    // Call Python script with JSON input via stdin
    const { stdout, stderr } = await execAsync(
      `"${PYTHON_BRIDGE_PATH}" "${FFI_SCRIPT_PATH}"`,
      {
        input: configJson,
        maxBuffer: 10 * 1024 * 1024, // 10MB
        encoding: "utf8",
      }
    );
    
    if (stderr && stderr.trim()) {
      console.warn("FFI bridge stderr:", stderr);
    }
    
    const result = JSON.parse(stdout.trim());
    
    if (result.error) {
      throw new Error(result.error);
    }
    
    // Validate result is array
    if (!Array.isArray(result)) {
      throw new Error("FFI bridge returned non-array result");
    }
    
    return result as ThemeVariant[];
  } catch (error) {
    const errorMessage = error instanceof Error ? error.message : String(error);
    vscode.window.showErrorMessage(`Theme generation failed: ${errorMessage}`);
    throw new Error(`FFI call failed: ${errorMessage}`);
  }
}
