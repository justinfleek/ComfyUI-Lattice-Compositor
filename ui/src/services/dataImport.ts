/**
 * Data Import Service
 *
 * Handles importing and parsing JSON, CSV, and TSV files
 * for data-driven animation. Data files are imported as
 * "footage" items accessible via expressions.
 */

import type {
  CSVDataAsset,
  CSVParseOptions,
  CSVSourceData,
  DataAsset,
  DataFileType,
  DataParseResult,
  FootageDataAccessor,
  JSONDataAsset,
  JSONParseOptions,
  JSONValue,
} from "@/types/dataAsset";
import type { RuntimeValue } from "@/types/ses-ambient";
import {
  getDataFileType,
  isCSVAsset,
  isJSONAsset,
  isSupportedDataFile,
} from "@/types/dataAsset";
import { parseAndSanitize } from "./security/jsonSanitizer";

// ============================================================================
// DATA STORE (In-memory storage for data assets)
// ============================================================================

const dataAssets: Map<string, DataAsset> = new Map();

// ============================================================================
// JSON PARSING
// ============================================================================

/**
 * Parse JSON content
 */
export function parseJSON(
  content: string,
  name: string,
  options: JSONParseOptions = {},
): DataParseResult {
  let processedContent = content;

  // Strip comments if allowed
  if (options.allowComments) {
    // Remove single-line comments
    processedContent = processedContent.replace(/\/\/.*$/gm, "");
    // Remove multi-line comments
    processedContent = processedContent.replace(/\/\*[\s\S]*?\*\//g, "");
  }

  // Use security-hardened JSON parser with depth/size limits
  const result = parseAndSanitize(processedContent, {
    maxDepth: 50, // Prevent deeply nested JSON bombs
    maxArrayLength: 100_000, // Prevent large array allocation
    maxStringLength: 10 * 1024 * 1024, // 10MB max string
    maxTotalKeys: 1_000_000, // Prevent many small objects
    removePrototypeKeys: true, // Block prototype pollution
  });

  if (!result.valid) {
    throw new Error(`[DataImport] Failed to parse JSON file "${name}": ${result.error}. File may be corrupted or invalid. Check the file format and try again.`);
  }

  // Throw on security warnings (don't just log - security issues are fatal)
  if (result.warnings.length > 0) {
    throw new Error(`[DataImport] Security warnings for "${name}": ${result.warnings.join(", ")}. File may contain malicious content. Import blocked for security.`);
  }

  // System F/Omega proof: Type guard for unknown → JSONValue
  // Type proof: parseAndSanitize returns unknown, but we know it's valid JSON
  // Since parseAndSanitize validates JSON structure, we can safely cast to JSONValue
  const sourceData = result.data as import("@/types/dataAsset").JSONValue;

  const asset: JSONDataAsset = {
    id: `data_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name,
    type: name.toLowerCase().endsWith(".mgjson") ? "mgjson" : "json",
    rawContent: content,
    lastModified: Date.now(),
    sourceData,
  };

  return { success: true, asset };
}

// ============================================================================
// CSV/TSV PARSING
// ============================================================================

/**
 * Parse CSV content
 */
export function parseCSV(
  content: string,
  name: string,
  options: CSVParseOptions = {},
): DataParseResult {
  const {
    delimiter = ",",
    hasHeaders = true,
    trimWhitespace = true,
    skipEmptyRows = true,
  } = options;

  const warnings: string[] = [];
  const lines = content.split(/\r?\n/);
  const rows: string[][] = [];

  for (let i = 0; i < lines.length; i++) {
    let line = lines[i];

    if (trimWhitespace) {
      line = line.trim();
    }

    if (skipEmptyRows && !line) {
      continue;
    }

    // Parse CSV line (handling quoted values)
    const row = parseCSVLine(line, delimiter);

    if (trimWhitespace) {
      for (let j = 0; j < row.length; j++) {
        row[j] = row[j].trim();
      }
    }

    rows.push(row);
  }

  if (rows.length === 0) {
    throw new Error(`[DataImport] CSV file "${name}" is empty or contains no valid data. File must contain at least one row of data.`);
  }

  const headers = hasHeaders ? rows[0] : rows[0].map((_, i) => `col${i}`);
  const dataRows = hasHeaders ? rows.slice(1) : rows;

  // Validate column count consistency
  const expectedColumns = headers.length;
  for (let i = 0; i < dataRows.length; i++) {
    if (dataRows[i].length !== expectedColumns) {
      warnings.push(
        `Row ${i + (hasHeaders ? 2 : 1)} has ${dataRows[i].length} columns, expected ${expectedColumns}`,
      );
      // Pad or trim to match
      while (dataRows[i].length < expectedColumns) {
        dataRows[i].push("");
      }
      if (dataRows[i].length > expectedColumns) {
        dataRows[i] = dataRows[i].slice(0, expectedColumns);
      }
    }
  }

  const asset: CSVDataAsset = {
    id: `data_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name,
    type: delimiter === "\t" ? "tsv" : "csv",
    rawContent: content,
    lastModified: Date.now(),
    headers,
    rows: dataRows,
    numRows: dataRows.length + (hasHeaders ? 1 : 0), // Include header in count
    numColumns: headers.length,
  };

  return {
    success: true,
    asset,
    warnings: warnings.length > 0 ? warnings : undefined,
  };
}

/**
 * Parse TSV content (tab-separated)
 */
export function parseTSV(
  content: string,
  name: string,
  options: Omit<CSVParseOptions, "delimiter"> = {},
): DataParseResult {
  return parseCSV(content, name, { ...options, delimiter: "\t" });
}

/**
 * Parse a single CSV line, handling quoted values
 */
function parseCSVLine(line: string, delimiter: string): string[] {
  const result: string[] = [];
  let current = "";
  let inQuotes = false;

  for (let i = 0; i < line.length; i++) {
    const char = line[i];
    const nextChar = line[i + 1];

    if (inQuotes) {
      if (char === '"' && nextChar === '"') {
        // Escaped quote
        current += '"';
        i++; // Skip next quote
      } else if (char === '"') {
        // End of quoted value
        inQuotes = false;
      } else {
        current += char;
      }
    } else {
      if (char === '"') {
        // Start of quoted value
        inQuotes = true;
      } else if (char === delimiter) {
        // End of field
        result.push(current);
        current = "";
      } else {
        current += char;
      }
    }
  }

  // Add last field
  result.push(current);

  return result;
}

// ============================================================================
// AUTO-DETECT AND PARSE
// ============================================================================

/**
 * Parse data file with auto-detection of type
 */
export function parseDataFile(
  content: string,
  filename: string,
): DataParseResult {
  // System F/Omega proof: Validate file type before calling utility
  // Type proof: filename ∈ string → DataFileType
  // Mathematical proof: File must be supported (checked by isSupportedDataFile) before calling getDataFileType
  if (!isSupportedDataFile(filename)) {
    throw new Error(`[DataImport] Unsupported file type: "${filename}". Supported types: .json, .csv, .tsv, .mgjson. Use a supported file format.`);
  }
  
  const fileType = getDataFileType(filename);

  switch (fileType) {
    case "json":
    case "mgjson":
      return parseJSON(content, filename);
    case "csv":
      return parseCSV(content, filename);
    case "tsv":
      return parseTSV(content, filename);
    default:
      throw new Error(`[DataImport] Unknown file type: "${fileType}" for file "${filename}". This should not happen - file type detection returned an unsupported value.`);
  }
}

// ============================================================================
// DATA ASSET MANAGEMENT
// ============================================================================

/**
 * Import data from file content
 */
export function importDataAsset(
  content: string,
  filename: string,
): DataParseResult {
  // parseDataFile now throws on errors instead of returning success: false
  const result = parseDataFile(content, filename);
  
  // If we get here, parsing succeeded
  if (result.asset) {
    dataAssets.set(result.asset.name, result.asset);
    console.log(`[DataImport] Imported data asset: ${filename}`);
  }

  return result;
}

/**
 * Import data from File object
 */
export async function importDataFromFile(file: File): Promise<DataParseResult> {
  if (!isSupportedDataFile(file.name)) {
    throw new Error(`[DataImport] Unsupported file type: "${file.name}". Supported types: .json, .csv, .tsv, .mgjson. Use a supported file format.`);
  }

  try {
    const content = await file.text();
    return importDataAsset(content, file.name);
  } catch (error) {
    // Re-throw if it's already our error format, otherwise wrap it
    if (error instanceof Error && error.message.startsWith("[DataImport]")) {
      throw error;
    }
    throw new Error(`[DataImport] Failed to read file "${file.name}": ${error instanceof Error ? error.message : "Unknown error"}. File may be corrupted or inaccessible.`);
  }
}

/**
 * Get data asset by name
 */
export function getDataAsset(name: string): DataAsset | null {
  return dataAssets.get(name) || null;
}

/**
 * Get all data assets
 */
export function getAllDataAssets(): DataAsset[] {
  return Array.from(dataAssets.values());
}

/**
 * Remove data asset
 */
export function removeDataAsset(name: string): boolean {
  return dataAssets.delete(name);
}

/**
 * Clear all data assets
 */
export function clearDataAssets(): void {
  dataAssets.clear();
}

/**
 * Reload data asset from raw content
 */
export function reloadDataAsset(
  name: string,
  newContent?: string,
): DataParseResult {
  const existing = dataAssets.get(name);

  if (!existing) {
    throw new Error(`[DataImport] Cannot reload data asset "${name}": Asset not found. Import the asset first before reloading.`);
  }

  const content = newContent || existing.rawContent;
  // parseDataFile now throws on errors instead of returning success: false
  const result = parseDataFile(content, name);
  
  // If we get here, parsing succeeded
  if (result.asset) {
    // Preserve the original ID
    result.asset.id = existing.id;
    dataAssets.set(name, result.asset);
    console.log(`[DataImport] Reloaded data asset: ${name}`);
  }

  return result;
}

// ============================================================================
// FOOTAGE ACCESSOR CREATION (for expressions)
// ============================================================================

/**
 * Create a footage accessor for use in expressions
 */
export function createFootageAccessor(
  name: string,
): FootageDataAccessor {
  const asset = getDataAsset(name);

  if (!asset) {
    throw new Error(`[DataImport] Data asset not found: ${name}`);
  }

  if (isJSONAsset(asset)) {
    return createJSONAccessor(asset);
  } else if (isCSVAsset(asset)) {
    return createCSVAccessor(asset);
  }

  throw new Error(`[DataImport] Unsupported asset type for data asset "${name}"`);
}

/**
 * Create JSON footage accessor
 */
function createJSONAccessor(asset: JSONDataAsset): FootageDataAccessor {
  return {
    name: asset.name,
    type: asset.type,
    sourceData: asset.sourceData,
  };
}

/**
 * Create CSV footage accessor
 */
function createCSVAccessor(asset: CSVDataAsset): FootageDataAccessor {
  // Convert CSV to JSON-like array for sourceData access
  const sourceData: CSVSourceData = asset.rows.map((row) => {
    const obj: Record<string, string | number | boolean | null> = {};
    asset.headers.forEach((header, index) => {
      const value = row[index];
      // Try to parse as number
      const numValue = parseFloat(value);
      if (Number.isNaN(numValue)) {
        // Check for boolean/null values
        if (value.toLowerCase() === "true") {
          obj[header] = true;
        } else if (value.toLowerCase() === "false") {
          obj[header] = false;
        } else if (value === "" || value.toLowerCase() === "null") {
          obj[header] = null;
        } else {
          obj[header] = value;
        }
      } else {
        obj[header] = numValue;
      }
    });
    return obj;
  });

  return {
    name: asset.name,
    type: asset.type,
    sourceData,

    dataValue: (coords: [number, number | string]): string | number => {
      const [rowIndex, colRef] = coords;

      // Determine column index
      let colIndex: number;
      if (typeof colRef === "string") {
        colIndex = asset.headers.indexOf(colRef);
        if (colIndex === -1) {
          console.warn(`[DataImport] Column not found: ${colRef}`);
          return "";
        }
      } else {
        colIndex = colRef;
      }

      // Row 0 = headers, Row 1+ = data
      if (rowIndex === 0) {
        return asset.headers[colIndex] || "";
      }

      const dataRowIndex = rowIndex - 1;
      if (dataRowIndex < 0 || dataRowIndex >= asset.rows.length) {
        console.warn(`[DataImport] Row index out of bounds: ${rowIndex}`);
        return "";
      }

      if (colIndex < 0 || colIndex >= asset.numColumns) {
        console.warn(`[DataImport] Column index out of bounds: ${colIndex}`);
        return "";
      }

      const value = asset.rows[dataRowIndex][colIndex];

      // Try to parse as number
      const numValue = parseFloat(value);
      return Number.isNaN(numValue) ? value : numValue;
    },

    numRows: () => asset.numRows,
    numColumns: () => asset.numColumns,
    headers: () => [...asset.headers],
  };
}

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/**
 * Extract array from JSON data at path
 */
/**
 * Extract array from JSON data asset at path
 * Returns null if path doesn't exist or value is not an array
 */
export function extractArrayFromJSON(
  asset: JSONDataAsset,
  path: string,
): import("@/types/dataAsset").JSONValue[] | null {
  const parts = path.split(".");
  // System F/Omega proof: Type guard for RuntimeValue sourceData
  // Type proof: sourceData: RuntimeValue → requires runtime type checking before property access
  let current: RuntimeValue = asset.sourceData as RuntimeValue;

  for (const part of parts) {
    if (current === null || current === undefined) {
      throw new Error(`[DataImport] Cannot access path "${path}": value is null or undefined at "${parts.slice(0, parts.indexOf(part)).join(".")}"`);
    }
    // Type guard: Check if current is an object/array before property access
    // Type proof: ∀ x: RuntimeValue, isObjectLike(x) → x has index signature
    if (typeof current !== "object" || current === null) {
      throw new Error(`[DataImport] Cannot access path "${path}": value at "${parts.slice(0, parts.indexOf(part)).join(".")}" is not an object`);
    }
    // Safe property access: current is object-like, part is string key
    const currentObj = current as Record<string, JSONValue>;
    current = currentObj[part] as RuntimeValue;
  }

  return Array.isArray(current) ? (current as JSONValue[]) : null;
}

/**
 * Get value from JSON data at path
 */
/**
 * Get value from JSON data asset at path
 * Returns the JSON value at the specified path
 */
export function getJSONValue(
  asset: JSONDataAsset,
  path: string,
): import("@/types/dataAsset").JSONValue | undefined {
  const parts = path.split(".");
  // System F/Omega proof: Type guard for RuntimeValue sourceData
  // Type proof: sourceData: RuntimeValue → requires runtime type checking before property access
  let current: RuntimeValue = asset.sourceData as RuntimeValue;

  for (const part of parts) {
    if (current === null || current === undefined) {
      throw new Error(`[DataImport] Cannot access path "${path}": value is null or undefined at "${parts.slice(0, parts.indexOf(part)).join(".")}"`);
    }

    // Type guard: Check if current is an object/array before property access
    // Type proof: ∀ x: RuntimeValue, isObjectLike(x) → x has index signature
    if (typeof current !== "object" || current === null) {
      throw new Error(`[DataImport] Cannot access path "${path}": value at "${parts.slice(0, parts.indexOf(part)).join(".")}" is not an object`);
    }

    // Handle array index notation: data[0]
    const arrayMatch = part.match(/^(\w+)\[(\d+)\]$/);
    if (arrayMatch) {
      const key = arrayMatch[1];
      const index = parseInt(arrayMatch[2], 10);
      // Type guard: Ensure current is object-like before accessing key property
      const obj = current as Record<string, JSONValue>;
      const arrayValue = obj[key];
      if (!Array.isArray(arrayValue)) {
        throw new Error(`[DataImport] Cannot access path "${path}": "${key}" is not an array`);
      }
      // Safe array access: arrayValue is array, index is number
      if (index < 0 || index >= arrayValue.length) {
        throw new Error(`[DataImport] Cannot access path "${path}": array index ${index} is out of bounds (array length: ${arrayValue.length})`);
      }
      current = arrayValue[index] as RuntimeValue;
    } else {
      // Safe property access: current is object-like, part is string key
      const obj = current as Record<string, JSONValue>;
      current = obj[part] as RuntimeValue;
    }
  }

  // Type assertion: current is JSONValue after type guards
  return current as JSONValue | undefined;
}

/**
 * Count items in CSV column
 */
export function countCSVRows(asset: CSVDataAsset): number {
  return asset.rows.length;
}

/**
 * Get unique values from CSV column
 */
export function getUniqueColumnValues(
  asset: CSVDataAsset,
  column: string | number,
): string[] {
  const colIndex =
    typeof column === "string" ? asset.headers.indexOf(column) : column;

  if (colIndex === -1 || colIndex >= asset.numColumns) {
    return [];
  }

  const values = new Set<string>();
  for (const row of asset.rows) {
    values.add(row[colIndex]);
  }

  return Array.from(values);
}

/**
 * Sum numeric values in CSV column
 */
export function sumCSVColumn(
  asset: CSVDataAsset,
  column: string | number,
): number {
  const colIndex =
    typeof column === "string" ? asset.headers.indexOf(column) : column;

  if (colIndex === -1 || colIndex >= asset.numColumns) {
    return 0;
  }

  let sum = 0;
  for (const row of asset.rows) {
    const value = parseFloat(row[colIndex]);
    if (!Number.isNaN(value)) {
      sum += value;
    }
  }

  return sum;
}

/**
 * Find max value in CSV column
 */
export function maxCSVColumn(
  asset: CSVDataAsset,
  column: string | number,
): number {
  const colIndex =
    typeof column === "string" ? asset.headers.indexOf(column) : column;

  if (colIndex === -1 || colIndex >= asset.numColumns) {
    return 0;
  }

  let max = -Infinity;
  for (const row of asset.rows) {
    const value = parseFloat(row[colIndex]);
    if (!Number.isNaN(value) && value > max) {
      max = value;
    }
  }

  return max === -Infinity ? 0 : max;
}

/**
 * Find min value in CSV column
 */
export function minCSVColumn(
  asset: CSVDataAsset,
  column: string | number,
): number {
  const colIndex =
    typeof column === "string" ? asset.headers.indexOf(column) : column;

  if (colIndex === -1 || colIndex >= asset.numColumns) {
    return 0;
  }

  let min = Infinity;
  for (const row of asset.rows) {
    const value = parseFloat(row[colIndex]);
    if (!Number.isNaN(value) && value < min) {
      min = value;
    }
  }

  return min === Infinity ? 0 : min;
}

// ============================================================================
// EXPORTS
// ============================================================================

export default {
  // Parsing
  parseJSON,
  parseCSV,
  parseTSV,
  parseDataFile,

  // Asset management
  importDataAsset,
  importDataFromFile,
  getDataAsset,
  getAllDataAssets,
  removeDataAsset,
  clearDataAssets,
  reloadDataAsset,

  // Expression support
  createFootageAccessor,

  // Utilities
  extractArrayFromJSON,
  getJSONValue,
  countCSVRows,
  getUniqueColumnValues,
  sumCSVColumn,
  maxCSVColumn,
  minCSVColumn,
};
