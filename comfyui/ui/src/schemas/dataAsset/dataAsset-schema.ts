/**
 * Data Asset Schemas
 *
 * Zod schemas for validating data asset types (JSON, CSV, TSV, MGJSON).
 * Used for data-driven animation support and expression context.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  boundedArray,
  entityId,
  jsonSerializable,
  MAX_PATH_LENGTH,
  MAX_NAME_LENGTH,
  MAX_STRING_LENGTH,
  MAX_ARRAY_LENGTH,
} from "../shared-validation";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const nonNegativeInt = z.number().int().nonnegative();
const positiveInt = z.number().int().positive();

// ═══════════════════════════════════════════════════════════════════════════
// Data File Type Schema
// ═══════════════════════════════════════════════════════════════════════════

export const DataFileTypeSchema = z.enum(["json", "csv", "tsv", "mgjson"]);

export type DataFileType = z.infer<typeof DataFileTypeSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Data Asset Base Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Base schema for data assets (without refinements for union support)
 */
const DataAssetBaseSchemaInner = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: DataFileTypeSchema,
  filePath: z.string().max(MAX_PATH_LENGTH).trim().optional(),
  lastModified: z.number().int().nonnegative().max(2147483647000), // Max timestamp (year 2038)
  rawContent: z.string().max(50 * 1024 * 1024), // Max 50MB raw content (security limit)
}).strict();

/**
 * Data Asset Base (exported with refinements)
 */
export const DataAssetBaseSchema = DataAssetBaseSchemaInner;

export type DataAssetBase = z.infer<typeof DataAssetBaseSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// JSON Data Asset Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * JSON Data Asset Base (for union)
 */
const JSONDataAssetBaseSchema = DataAssetBaseSchemaInner.extend({
  type: z.union([z.literal("json"), z.literal("mgjson")]),
  sourceData: jsonSerializable,
}).strict();

/**
 * JSON Data Asset
 * Stores parsed JSON data accessible via sourceData property.
 * Note: sourceData is `any` in TypeScript but we validate it's a valid JSON structure.
 */
export const JSONDataAssetSchema = JSONDataAssetBaseSchema.refine(
  (data) => {
    // Validate sourceData is JSON-serializable (basic check)
    try {
      JSON.stringify(data.sourceData);
      return true;
    } catch {
      return false;
    }
  },
  { message: "sourceData must be JSON-serializable", path: ["sourceData"] }
);

export type JSONDataAsset = z.infer<typeof JSONDataAssetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// CSV Data Asset Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * CSV Data Asset Base (for union)
 */
const CSVDataAssetBaseSchema = DataAssetBaseSchemaInner.extend({
  type: z.union([z.literal("csv"), z.literal("tsv")]),
  headers: boundedArray(z.string().max(200).trim(), 10000), // Max 10k headers
  rows: boundedArray(boundedArray(z.string().max(MAX_STRING_LENGTH), 10000), MAX_ARRAY_LENGTH), // Max rows and columns
  numRows: positiveInt.max(MAX_ARRAY_LENGTH), // Total rows including header
  numColumns: positiveInt.max(10000), // Number of columns
}).strict();

/**
 * CSV/TSV Data Asset
 * Stores parsed tabular data with headers and rows.
 */
export const CSVDataAssetSchema = CSVDataAssetBaseSchema.refine(
  (data) => {
    // numRows should match rows.length + 1 (header)
    return data.numRows === data.rows.length + 1;
  },
  { message: "numRows must equal rows.length + 1 (including header)", path: ["numRows"] }
).refine(
  (data) => {
    // numColumns should match headers.length
    return data.numColumns === data.headers.length;
  },
  { message: "numColumns must match headers.length", path: ["numColumns"] }
).refine(
  (data) => {
    // All rows should have same length as headers
    return data.rows.every((row) => row.length === data.headers.length);
  },
  { message: "All rows must have same length as headers", path: ["rows"] }
);

export type CSVDataAsset = z.infer<typeof CSVDataAssetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Data Asset Union Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Union type for all data assets
 * Uses base schemas (without refinements) for discriminated union
 */
export const DataAssetSchema = z.discriminatedUnion("type", [
  JSONDataAssetBaseSchema,
  CSVDataAssetBaseSchema,
]);

export type DataAsset = z.infer<typeof DataAssetSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// CSV Source Data Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * CSV data represented as JSON-like structure
 * Allows array-style access: data[0].columnName
 */
export const CSVSourceDataSchema = boundedArray(
  z.record(z.string().max(200), z.union([z.string(), z.number(), z.boolean(), z.null()])),
  MAX_ARRAY_LENGTH
);

export type CSVSourceData = z.infer<typeof CSVSourceDataSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Data Parse Result Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Result of parsing a data file
 */
export const DataParseResultSchema = z.object({
  success: z.boolean(),
  asset: DataAssetSchema.optional(),
  error: z.string().max(MAX_STRING_LENGTH).trim().optional(),
  warnings: boundedArray(z.string().max(MAX_STRING_LENGTH).trim(), 100), // Max 100 warnings
}).strict().refine(
  (data) => {
    // If success is true, asset should be present
    if (data.success && !data.asset) {
      return false;
    }
    // If success is false, error should be present
    if (!data.success && !data.error) {
      return false;
    }
    return true;
  },
  { message: "success=true requires asset, success=false requires error", path: ["success"] }
);

export type DataParseResult = z.infer<typeof DataParseResultSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// CSV Parse Options Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Options for CSV parsing
 */
export const CSVParseOptionsSchema = z.object({
  delimiter: z.string().max(10).trim().optional(), // Max 10 char delimiter
  hasHeaders: z.boolean().optional(),
  trimWhitespace: z.boolean().optional(),
  skipEmptyRows: z.boolean().optional(),
}).strict();

export type CSVParseOptions = z.infer<typeof CSVParseOptionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// JSON Parse Options Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Options for JSON parsing
 */
export const JSONParseOptionsSchema = z.object({
  allowComments: z.boolean().optional(), // Strip // and /* */ comments
  strict: z.boolean().optional(), // Strict JSON parsing
}).strict();

export type JSONParseOptions = z.infer<typeof JSONParseOptionsSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Chart Data Point Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Common chart data structure
 */
export const ChartDataPointSchema = z.object({
  label: z.string().min(1).max(200).trim(),
  value: finiteNumber,
}).strict().passthrough(); // Allow additional properties

export type ChartDataPoint = z.infer<typeof ChartDataPointSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Chart Series Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Chart data series
 */
export const ChartSeriesSchema = z.object({
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  data: boundedArray(ChartDataPointSchema, 100000), // Max 100k data points per series
}).strict();

export type ChartSeries = z.infer<typeof ChartSeriesSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Footage Data Accessor Schema (for validation only)
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Footage Data Accessor
 * Returned by footage("filename") in expressions.
 * Note: This is a runtime interface, not a serializable type.
 * Schema is for validation of data passed to expressions.
 */
export const FootageDataAccessorSchema = z.object({
  sourceData: jsonSerializable.optional(), // For JSON files
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  type: DataFileTypeSchema,
}).strict().passthrough(); // Allow method properties (dataValue, numRows, etc.)

export type FootageDataAccessor = z.infer<typeof FootageDataAccessorSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Validate JSON data asset
 */
export function validateJSONDataAsset(data: unknown): JSONDataAsset {
  return JSONDataAssetSchema.parse(data);
}

/**
 * Safe validate JSON data asset
 */
export function safeValidateJSONDataAsset(data: unknown) {
  return JSONDataAssetSchema.safeParse(data);
}

/**
 * Validate CSV data asset
 */
export function validateCSVDataAsset(data: unknown): CSVDataAsset {
  return CSVDataAssetSchema.parse(data);
}

/**
 * Safe validate CSV data asset
 */
export function safeValidateCSVDataAsset(data: unknown) {
  return CSVDataAssetSchema.safeParse(data);
}

/**
 * Validate data asset (any type)
 */
export function validateDataAsset(data: unknown): DataAsset {
  return DataAssetSchema.parse(data);
}

/**
 * Safe validate data asset
 */
export function safeValidateDataAsset(data: unknown) {
  return DataAssetSchema.safeParse(data);
}

/**
 * Validate data parse result
 */
export function validateDataParseResult(data: unknown): DataParseResult {
  return DataParseResultSchema.parse(data);
}

/**
 * Safe validate data parse result
 */
export function safeValidateDataParseResult(data: unknown) {
  return DataParseResultSchema.safeParse(data);
}
