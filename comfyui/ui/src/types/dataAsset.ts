/**
 * Data Asset Types
 *
 * Type definitions for data-driven animation support.
 * Supports JSON, CSV, and TSV data files imported as footage items.
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                   // data // asset // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Type of data file
 */
export type DataFileType = "json" | "csv" | "tsv" | "mgjson";

/**
 * Base interface for all data assets
 */
export interface DataAssetBase {
  id: string;
  name: string;
  type: DataFileType;
  filePath?: string; // Original file path (if imported from file)
  lastModified: number; // Timestamp of last modification
  rawContent: string; // Original raw file content
}

/**
 * JSON Data Asset
 *
 * Stores parsed JSON data accessible via sourceData property.
 */
/**
 * JSON value type - represents any valid JSON value
 * JSON can be: null, boolean, number, string, array, or object
 */
export type JSONValue =
  | null
  | boolean
  | number
  | string
  | JSONValue[]
  | { [key: string]: JSONValue };

export interface JSONDataAsset extends DataAssetBase {
  type: "json" | "mgjson";
  sourceData: JSONValue; // Parsed JSON object (type-safe JSON value)
}

/**
 * CSV/TSV Data Asset
 *
 * Stores parsed tabular data accessible via dataValue() method.
 */
export interface CSVDataAsset extends DataAssetBase {
  type: "csv" | "tsv";
  headers: string[]; // Column headers (first row)
  rows: string[][]; // Data rows (excluding header)
  numRows: number; // Total rows including header
  numColumns: number; // Number of columns
}

/**
 * Union type for all data assets
 */
export type DataAsset = JSONDataAsset | CSVDataAsset;

// ═══════════════════════════════════════════════════════════════════════════
// DATA ACCESSOR INTERFACES (for expressions)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * JSON Data Accessor
 *
 * Returned by footage().sourceData for JSON files.
 * Provides access to parsed JSON structure.
 */
export interface JSONDataAccessor {
  sourceData: JSONValue; // Type-safe JSON value
}

/**
 * CSV Data Accessor
 *
 * Returned by footage() for CSV/TSV files.
 * Provides dataValue(), numRows(), numColumns() methods.
 */
export interface CSVDataAccessor {
  /**
   * Get value at specific row and column
   * @param coords [row, column] - column can be index or header name
   */
  dataValue(coords: [number, number | string]): string | number;

  /**
   * Get total number of rows (including header)
   */
  numRows(): number;

  /**
   * Get total number of columns
   */
  numColumns(): number;

  /**
   * Get all headers
   */
  headers(): string[];

  /**
   * Get raw source data for JSON-style access
   */
  sourceData: CSVSourceData;
}

/**
 * CSV data represented as JSON-like structure
 * Allows array-style access: data[0].columnName
 * Values are strings (from CSV), numbers (if parsed), booleans, or null
 * Matches schema definition in dataAsset-schema.ts
 */
export type CSVSourceData = Array<Record<string, string | number | boolean | null>>;

// ═══════════════════════════════════════════════════════════════════════════
// FOOTAGE ACCESSOR (Combined interface for expressions)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Footage Data Accessor
 *
 * Returned by footage("filename") in expressions.
 * Type depends on whether file is JSON or CSV.
 */
export interface FootageDataAccessor {
  // For JSON files
  sourceData?: JSONValue; // Type-safe JSON value

  // For CSV files
  dataValue?: (coords: [number, number | string]) => string | number;
  numRows?: () => number;
  numColumns?: () => number;
  headers?: () => string[];

  // Metadata
  name: string;
  type: DataFileType;
}

// ═══════════════════════════════════════════════════════════════════════════
// IMPORT/PARSE RESULTS
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Result of parsing a data file
 */
export interface DataParseResult {
  success: boolean;
  asset?: DataAsset;
  error?: string;
  warnings?: string[];
}

/**
 * Options for CSV parsing
 */
export interface CSVParseOptions {
  delimiter?: string; // Default: ',' for CSV, '\t' for TSV
  hasHeaders?: boolean; // Default: true
  trimWhitespace?: boolean; // Default: true
  skipEmptyRows?: boolean; // Default: true
}

/**
 * Options for JSON parsing
 */
export interface JSONParseOptions {
  allowComments?: boolean; // Strip // and /* */ comments
  strict?: boolean; // Strict JSON parsing
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                 // chart // data // helpers
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Common chart data structure
 */
/**
 * Chart data point with additional metadata
 * Additional properties can be any JSON-compatible value
 */
export interface ChartDataPoint {
  label: string;
  value: number;
  [key: string]: JSONValue; // Additional properties (type-safe JSON values)
}

/**
 * Chart data series
 */
export interface ChartSeries {
  name: string;
  data: ChartDataPoint[];
}

/**
 * Extract chart data from JSON or CSV
 */
export interface ChartDataExtractor {
  /**
   * Extract single series from data
   */
  extractSeries(
    data: DataAsset,
    labelKey: string,
    valueKey: string,
  ): ChartDataPoint[];

  /**
   * Extract multiple series from data
   */
  extractMultiSeries(
    data: DataAsset,
    labelKey: string,
    valueKeys: string[],
  ): ChartSeries[];
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                           // type // guards
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Check if asset is JSON type
 */
export function isJSONAsset(asset: DataAsset): asset is JSONDataAsset {
  return asset.type === "json" || asset.type === "mgjson";
}

/**
 * Check if asset is CSV/TSV type
 */
export function isCSVAsset(asset: DataAsset): asset is CSVDataAsset {
  return asset.type === "csv" || asset.type === "tsv";
}

/**
 * Check if file extension is supported data type
 */
export function isSupportedDataFile(filename: string): boolean {
  const ext = filename.toLowerCase().split(".").pop();
  return ["json", "csv", "tsv", "mgjson"].includes(ext || "");
}

/**
 * Get data file type from filename
 * 
 * System F/Omega proof: Explicit validation of file extension
 * Type proof: filename ∈ string → DataFileType (non-nullable)
 * Mathematical proof: File extension must match one of the supported data file types
 */
export function getDataFileType(filename: string): DataFileType {
  const ext = filename.toLowerCase().split(".").pop();
  if (ext === "json") return "json";
  if (ext === "csv") return "csv";
  if (ext === "tsv") return "tsv";
  if (ext === "mgjson") return "mgjson";
  
  // System F/Omega proof: Explicit validation of file extension
  // Type proof: ext ∈ string | undefined
  // Mathematical proof: File extension must match one of the supported types
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const extension = (ext !== null && ext !== undefined && typeof ext === "string" && ext.length > 0) ? ext : "none";
  throw new Error(
    `[DataAsset] Cannot detect file type: Unsupported file extension. ` +
    `Filename: "${filename}", extension: ${extension}, ` +
    `supported extensions: json, csv, tsv, mgjson. ` +
    `File extension must match one of the supported data file types. ` +
    `Wrap in try/catch if "unsupported format" is an expected state.`
  );
}

// ═══════════════════════════════════════════════════════════════════════════
//                                           // expression // context // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Data available in expression context
 */
export interface DataExpressionContext {
  /**
   * Access data footage by name
   */
  footage: (name: string) => FootageDataAccessor | null;
}
