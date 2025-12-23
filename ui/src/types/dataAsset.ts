/**
 * Data Asset Types
 *
 * Type definitions for data-driven animation support.
 * Supports JSON, CSV, and TSV data files imported as footage items.
 */

// ============================================================================
// DATA ASSET TYPES
// ============================================================================

/**
 * Type of data file
 */
export type DataFileType = 'json' | 'csv' | 'tsv' | 'mgjson';

/**
 * Base interface for all data assets
 */
export interface DataAssetBase {
  id: string;
  name: string;
  type: DataFileType;
  filePath?: string;          // Original file path (if imported from file)
  lastModified: number;       // Timestamp of last modification
  rawContent: string;         // Original raw file content
}

/**
 * JSON Data Asset
 *
 * Stores parsed JSON data accessible via sourceData property.
 */
export interface JSONDataAsset extends DataAssetBase {
  type: 'json' | 'mgjson';
  sourceData: any;            // Parsed JSON object
}

/**
 * CSV/TSV Data Asset
 *
 * Stores parsed tabular data accessible via dataValue() method.
 */
export interface CSVDataAsset extends DataAssetBase {
  type: 'csv' | 'tsv';
  headers: string[];          // Column headers (first row)
  rows: string[][];           // Data rows (excluding header)
  numRows: number;            // Total rows including header
  numColumns: number;         // Number of columns
}

/**
 * Union type for all data assets
 */
export type DataAsset = JSONDataAsset | CSVDataAsset;

// ============================================================================
// DATA ACCESSOR INTERFACES (for expressions)
// ============================================================================

/**
 * JSON Data Accessor
 *
 * Returned by footage().sourceData for JSON files.
 * Provides access to parsed JSON structure.
 */
export interface JSONDataAccessor {
  sourceData: any;
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
 */
export type CSVSourceData = Record<string, any>[];

// ============================================================================
// FOOTAGE ACCESSOR (Combined interface for expressions)
// ============================================================================

/**
 * Footage Data Accessor
 *
 * Returned by footage("filename") in expressions.
 * Type depends on whether file is JSON or CSV.
 */
export interface FootageDataAccessor {
  // For JSON files
  sourceData?: any;

  // For CSV files
  dataValue?: (coords: [number, number | string]) => string | number;
  numRows?: () => number;
  numColumns?: () => number;
  headers?: () => string[];

  // Metadata
  name: string;
  type: DataFileType;
}

// ============================================================================
// IMPORT/PARSE RESULTS
// ============================================================================

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
  delimiter?: string;         // Default: ',' for CSV, '\t' for TSV
  hasHeaders?: boolean;       // Default: true
  trimWhitespace?: boolean;   // Default: true
  skipEmptyRows?: boolean;    // Default: true
}

/**
 * Options for JSON parsing
 */
export interface JSONParseOptions {
  allowComments?: boolean;    // Strip // and /* */ comments
  strict?: boolean;           // Strict JSON parsing
}

// ============================================================================
// CHART DATA HELPERS
// ============================================================================

/**
 * Common chart data structure
 */
export interface ChartDataPoint {
  label: string;
  value: number;
  [key: string]: any;         // Additional properties
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
    valueKey: string
  ): ChartDataPoint[];

  /**
   * Extract multiple series from data
   */
  extractMultiSeries(
    data: DataAsset,
    labelKey: string,
    valueKeys: string[]
  ): ChartSeries[];
}

// ============================================================================
// TYPE GUARDS
// ============================================================================

/**
 * Check if asset is JSON type
 */
export function isJSONAsset(asset: DataAsset): asset is JSONDataAsset {
  return asset.type === 'json' || asset.type === 'mgjson';
}

/**
 * Check if asset is CSV/TSV type
 */
export function isCSVAsset(asset: DataAsset): asset is CSVDataAsset {
  return asset.type === 'csv' || asset.type === 'tsv';
}

/**
 * Check if file extension is supported data type
 */
export function isSupportedDataFile(filename: string): boolean {
  const ext = filename.toLowerCase().split('.').pop();
  return ['json', 'csv', 'tsv', 'mgjson'].includes(ext || '');
}

/**
 * Get data file type from filename
 */
export function getDataFileType(filename: string): DataFileType | null {
  const ext = filename.toLowerCase().split('.').pop();
  if (ext === 'json') return 'json';
  if (ext === 'csv') return 'csv';
  if (ext === 'tsv') return 'tsv';
  if (ext === 'mgjson') return 'mgjson';
  return null;
}

// ============================================================================
// EXPRESSION CONTEXT TYPES
// ============================================================================

/**
 * Data available in expression context
 */
export interface DataExpressionContext {
  /**
   * Access data footage by name
   */
  footage: (name: string) => FootageDataAccessor | null;
}
