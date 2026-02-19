/**
 * Template Builder Schemas
 *
 * Zod schemas for template builder system (Essential Graphics panel).
 * All numeric values use .finite() to reject NaN/Infinity.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import { finiteNumber, nonNegativeFinite, frameNumber, positiveFinite } from "../layers/primitives-schema";
import { AnimatablePropertySchema } from "../layers/animation-schema";
import { RGBAColorSchema } from "../layers/primitives-schema";
import { CompositionSchema } from "../project-schema";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Validation Constants
// ═══════════════════════════════════════════════════════════════════════════

const MAX_NAME_LENGTH = 200;
const MAX_DESCRIPTION_LENGTH = 2000;
const MAX_COMMENT_LENGTH = 5000;
const MAX_TAG_LENGTH = 50;
const MAX_TAGS_COUNT = 50;
const MAX_PATH_LENGTH = 500;
const MAX_ID_LENGTH = 200;
const MAX_MIME_TYPE_LENGTH = 100;
const MAX_FONT_FAMILY_LENGTH = 200;
const MAX_FONT_STYLE_LENGTH = 100;
const MAX_URL_LENGTH = 2048;
const MAX_BASE64_LENGTH = 50 * 1024 * 1024; // 50MB max base64 data

// Supported template format versions
const SUPPORTED_FORMAT_VERSIONS = ["1.0.0", "1.0"];

// ═══════════════════════════════════════════════════════════════════════════
// Helper Schemas
// ═══════════════════════════════════════════════════════════════════════════

/** Non-empty string with max length */
const nonEmptyString = (maxLength: number) =>
  z.string().min(1).max(maxLength).trim();

/** ISO 8601 datetime string */
const iso8601DateTime = z.string().datetime();

/** Base64 or data URL string */
const base64OrDataUrl = z.string().refine(
  (val) => {
    if (val.length > MAX_BASE64_LENGTH) return false;
    // Data URL format: data:[<mediatype>][;base64],<data>
    if (val.startsWith("data:")) {
      const commaIndex = val.indexOf(",");
      if (commaIndex === -1) return false;
      const header = val.substring(0, commaIndex);
      const data = val.substring(commaIndex + 1);
      return header.includes("base64") || data.length > 0;
    }
    // Base64 format: only base64 characters
    return /^[A-Za-z0-9+/=]+$/.test(val);
  },
  { message: "Must be valid base64 or data URL" }
);

/** Valid MIME type */
const mimeType = z.string()
  .max(MAX_MIME_TYPE_LENGTH)
  .refine(
    (val) => /^[a-z][a-z0-9]*\/[a-z0-9][a-z0-9._-]*$/i.test(val),
    { message: "Must be valid MIME type (e.g., 'image/png', 'video/mp4')" }
  );

/** Hex color string (#RRGGBB or #RRGGBBAA) */
const hexColor = z.string().regex(
  /^#([0-9A-Fa-f]{6}|[0-9A-Fa-f]{8})$/,
  { message: "Must be valid hex color (#RRGGBB or #RRGGBBAA)" }
);

/** Template ID format - must be non-empty, alphanumeric with underscores/hyphens */
const templateId = z.string()
  .min(1)
  .max(MAX_ID_LENGTH)
  .regex(
    /^[a-zA-Z0-9_-]+$/,
    { message: "Must be valid ID format (alphanumeric, underscores, hyphens only)" }
  );

/** Property path (e.g., "data.text", "transform.position.x") */
const propertyPath = z.string()
  .max(MAX_PATH_LENGTH)
  .regex(
    /^[a-zA-Z_$][a-zA-Z0-9_$.]*(\.[a-zA-Z_$][a-zA-Z0-9_$.]*)*$/,
    { message: "Must be valid property path (e.g., 'data.text', 'transform.position.x')" }
  );

// ═══════════════════════════════════════════════════════════════════════════
// Expression Control Types
// ═══════════════════════════════════════════════════════════════════════════

export const ExpressionControlTypeSchema = z.enum([
  "slider",
  "checkbox",
  "dropdown",
  "color",
  "point",
  "angle",
]);

export type ExpressionControlType = z.infer<typeof ExpressionControlTypeSchema>;

export const DropdownOptionSchema = z.object({
  label: nonEmptyString(200),
  value: z.union([z.string().max(500), finiteNumber]),
}).strict();

export type DropdownOption = z.infer<typeof DropdownOptionSchema>;

export const ExpressionControlConfigSchema = z.object({
  min: finiteNumber.optional(),
  max: finiteNumber.optional(),
  step: positiveFinite.optional(),
  options: z.array(DropdownOptionSchema).min(1).optional(),
  includeAlpha: z.boolean().optional(),
  is3D: z.boolean().optional(),
  displayUnit: z.enum(["degrees", "radians", "rotations"]).optional(),
}).strict().refine(
  (data) => {
    if (data.min !== undefined && data.max !== undefined && data.min > data.max) {
      return false;
    }
    return true;
  },
  { message: "min must be <= max when both are present", path: ["min"] }
).refine(
  (data) => {
    if (data.step !== undefined && data.step <= 0) {
      return false;
    }
    return true;
  },
  { message: "step must be positive", path: ["step"] }
);

export type ExpressionControlConfig = z.infer<typeof ExpressionControlConfigSchema>;

export const ExpressionControlSchema = z.object({
  id: templateId,
  name: nonEmptyString(MAX_NAME_LENGTH),
  type: ExpressionControlTypeSchema,
  value: AnimatablePropertySchema,
  config: ExpressionControlConfigSchema,
  expanded: z.boolean().optional(),
}).strict();

export type ExpressionControl = z.infer<typeof ExpressionControlSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Exposed Property Types
// ═══════════════════════════════════════════════════════════════════════════

export const ExposedPropertyTypeSchema = z.enum([
  "sourceText",
  "color",
  "number",
  "checkbox",
  "dropdown",
  "point",
  "media",
  "font",
  "layer",
]);

export type ExposedPropertyType = z.infer<typeof ExposedPropertyTypeSchema>;

const DefaultValueSchema = z.union([
  z.string().max(10000), // Text values
  finiteNumber,
  z.boolean(),
  z.object({
    r: z.number().int().min(0).max(255),
    g: z.number().int().min(0).max(255),
    b: z.number().int().min(0).max(255),
    a: z.number().min(0).max(1),
  }).strict(),
  z.object({
    x: finiteNumber,
    y: finiteNumber,
  }).strict(),
]);

export const ExposedPropertyConfigSchema = z.object({
  min: finiteNumber.optional(),
  max: finiteNumber.optional(),
  step: positiveFinite.optional(),
  options: z.array(DropdownOptionSchema).min(1).optional(),
  maxLength: z.number().int().nonnegative().max(100000).optional(),
  multiline: z.boolean().optional(),
  acceptedTypes: z.array(z.enum(["image", "video"])).min(1).optional(),
  aspectRatio: positiveFinite.optional(),
  allowFontChange: z.boolean().optional(),
  allowSizeChange: z.boolean().optional(),
  allowColorChange: z.boolean().optional(),
}).strict().refine(
  (data) => {
    if (data.min !== undefined && data.max !== undefined && data.min > data.max) {
      return false;
    }
    return true;
  },
  { message: "min must be <= max when both are present", path: ["min"] }
).refine(
  (data) => {
    if (data.step !== undefined && data.step <= 0) {
      return false;
    }
    return true;
  },
  { message: "step must be positive", path: ["step"] }
).refine(
  (data) => {
    if (data.aspectRatio !== undefined && data.aspectRatio <= 0) {
      return false;
    }
    return true;
  },
  { message: "aspectRatio must be positive", path: ["aspectRatio"] }
);

export type ExposedPropertyConfig = z.infer<typeof ExposedPropertyConfigSchema>;

export const ExposedPropertySchema = z.object({
  id: templateId,
  name: nonEmptyString(MAX_NAME_LENGTH),
  type: ExposedPropertyTypeSchema,
  sourceLayerId: z.string().max(MAX_ID_LENGTH),
  sourcePropertyPath: propertyPath,
  sourceControlId: z.string().max(MAX_ID_LENGTH).optional(),
  groupId: z.string().max(MAX_ID_LENGTH).optional(),
  order: z.number().int().nonnegative(),
  config: ExposedPropertyConfigSchema,
  comment: z.string().max(MAX_COMMENT_LENGTH).optional(),
  defaultValue: DefaultValueSchema.optional(),
}).strict();

export type ExposedProperty = z.infer<typeof ExposedPropertySchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Property Group
// ═══════════════════════════════════════════════════════════════════════════

export const PropertyGroupSchema = z.object({
  id: templateId,
  name: nonEmptyString(MAX_NAME_LENGTH),
  expanded: z.boolean(),
  order: z.number().int().nonnegative(),
  color: hexColor.optional(),
}).strict();

export type PropertyGroup = z.infer<typeof PropertyGroupSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Template Configuration
// ═══════════════════════════════════════════════════════════════════════════

export const TemplateCommentSchema = z.object({
  id: templateId,
  text: nonEmptyString(MAX_COMMENT_LENGTH),
  order: z.number().int().nonnegative(),
  groupId: z.string().max(MAX_ID_LENGTH).optional(),
}).strict();

export type TemplateComment = z.infer<typeof TemplateCommentSchema>;

export const TemplateExportSettingsSchema = z.object({
  includeFonts: z.boolean(),
  includeMedia: z.boolean(),
  allowDurationChange: z.boolean(),
  posterQuality: z.enum(["low", "medium", "high"]),
}).strict();

export type TemplateExportSettings = z.infer<typeof TemplateExportSettingsSchema>;

export const TemplateConfigSchema = z.object({
  name: nonEmptyString(MAX_NAME_LENGTH),
  description: z.string().max(MAX_DESCRIPTION_LENGTH).optional(),
  author: z.string().max(MAX_NAME_LENGTH).optional(),
  version: z.string().max(50).optional(),
  tags: z.array(z.string().max(MAX_TAG_LENGTH).min(1)).max(MAX_TAGS_COUNT).optional(),
  masterCompositionId: z.string().max(MAX_ID_LENGTH),
  exposedProperties: z.array(ExposedPropertySchema),
  groups: z.array(PropertyGroupSchema),
  comments: z.array(TemplateCommentSchema),
  posterFrame: frameNumber,
  exportSettings: TemplateExportSettingsSchema,
  created: iso8601DateTime,
  modified: iso8601DateTime,
}).strict().refine(
  (data) => {
    // Validate group IDs referenced in exposedProperties and comments exist
    const groupIds = new Set(data.groups.map((g) => g.id));
    for (const prop of data.exposedProperties) {
      if (prop.groupId && !groupIds.has(prop.groupId)) {
        return false;
      }
    }
    for (const comment of data.comments) {
      if (comment.groupId && !groupIds.has(comment.groupId)) {
        return false;
      }
    }
    return true;
  },
  { message: "All groupId references must exist in groups array" }
).refine(
  (data) => {
    // Validate order uniqueness within groups
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const orderMap = new Map<string, Set<number>>();
    for (const prop of data.exposedProperties) {
      const key = (prop.groupId !== null && prop.groupId !== undefined && typeof prop.groupId === "string" && prop.groupId.length > 0) ? prop.groupId : "__ungrouped__";
      if (!orderMap.has(key)) orderMap.set(key, new Set());
      const orders = orderMap.get(key)!;
      if (orders.has(prop.order)) {
        return false;
      }
      orders.add(prop.order);
    }
    for (const comment of data.comments) {
      const key = (comment.groupId !== null && comment.groupId !== undefined && typeof comment.groupId === "string" && comment.groupId.length > 0) ? comment.groupId : "__ungrouped__";
      if (!orderMap.has(key)) orderMap.set(key, new Set());
      const orders = orderMap.get(key)!;
      if (orders.has(comment.order)) {
        return false;
      }
      orders.add(comment.order);
    }
    return true;
  },
  { message: "Order values must be unique within each group" }
);

export type TemplateConfig = z.infer<typeof TemplateConfigSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Template Export Types
// ═══════════════════════════════════════════════════════════════════════════

export const TemplateAssetSchema = z.object({
  id: z.string().max(MAX_ID_LENGTH),
  name: nonEmptyString(MAX_NAME_LENGTH),
  type: z.enum([
    "depth_map",
    "image",
    "video",
    "audio",
    "model",
    "pointcloud",
    "texture",
    "material",
    "hdri",
    "svg",
    "sprite",
    "spritesheet",
    "lut",
  ]),
  data: z.union([
    base64OrDataUrl,
    z.string().url().max(MAX_URL_LENGTH), // URL
  ]),
  mimeType: mimeType,
}).strict().refine(
  (data) => {
    // Validate mimeType matches asset type
    const typeMimeMap: Record<string, string[]> = {
      image: ["image/"],
      video: ["video/"],
      audio: ["audio/"],
      model: ["model/", "application/octet-stream"],
      pointcloud: ["application/", "text/plain"],
      texture: ["image/"],
      material: ["application/json", "model/mtl"],
      hdri: ["image/"],
      svg: ["image/svg+xml"],
      sprite: ["image/"],
      spritesheet: ["image/"],
      lut: ["image/", "text/x-cube", "application/octet-stream"],
      depth_map: ["image/"],
    };
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
    const prefixesRaw = typeMimeMap[data.type];
    const expectedPrefixes = (prefixesRaw !== null && prefixesRaw !== undefined && Array.isArray(prefixesRaw)) ? prefixesRaw : [];
    return expectedPrefixes.some((prefix) => data.mimeType.startsWith(prefix));
  },
  { message: "mimeType must match asset type" }
);

export type TemplateAsset = z.infer<typeof TemplateAssetSchema>;

export const TemplateFontSchema = z.object({
  family: nonEmptyString(MAX_FONT_FAMILY_LENGTH),
  style: nonEmptyString(MAX_FONT_STYLE_LENGTH),
  embedded: z.boolean(),
  data: base64OrDataUrl.optional(),
  source: z.enum(["google", "cloud", "local", "system"]).optional(),
}).strict().refine(
  (data) => {
    // If embedded is true, data must be present
    if (data.embedded && !data.data) {
      return false;
    }
    return true;
  },
  { message: "embedded fonts must have data field", path: ["data"] }
);

export type TemplateFont = z.infer<typeof TemplateFontSchema>;

export const LatticeTemplateSchema = z.object({
  formatVersion: z.enum(SUPPORTED_FORMAT_VERSIONS as [string, ...string[]]),
  templateConfig: TemplateConfigSchema,
  composition: CompositionSchema,
  assets: z.array(TemplateAssetSchema),
  fonts: z.array(TemplateFontSchema),
  posterImage: base64OrDataUrl,
}).strict();

export type LatticeTemplate = z.infer<typeof LatticeTemplateSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Panel State Types
// ═══════════════════════════════════════════════════════════════════════════

export const TemplateBuilderStateSchema = z.object({
  activeTab: z.enum(["browse", "edit"]),
  masterCompositionId: z.string().max(MAX_ID_LENGTH).nullable(),
  selectedPropertyIds: z.array(z.string().max(MAX_ID_LENGTH)),
  selectedGroupId: z.string().max(MAX_ID_LENGTH).nullable(),
  searchQuery: z.string().max(500),
  filterTags: z.array(z.string().max(MAX_TAG_LENGTH)).max(MAX_TAGS_COUNT),
  savedTemplates: z.array(
    z.object({
      id: z.string().max(MAX_ID_LENGTH),
      name: nonEmptyString(MAX_NAME_LENGTH),
      importedFrom: z.string().max(MAX_PATH_LENGTH).optional(),
      posterImage: base64OrDataUrl,
      author: z.string().max(MAX_NAME_LENGTH).optional(),
      tags: z.array(z.string().max(MAX_TAG_LENGTH)).max(MAX_TAGS_COUNT).optional(),
      importDate: iso8601DateTime,
      templateData: LatticeTemplateSchema.optional(),
    }).strict()
  ),
}).strict();

export type TemplateBuilderState = z.infer<typeof TemplateBuilderStateSchema>;

export const SavedTemplateSchema = z.object({
  id: z.string().max(MAX_ID_LENGTH),
  name: nonEmptyString(MAX_NAME_LENGTH),
  importedFrom: z.string().max(MAX_PATH_LENGTH).optional(),
  posterImage: base64OrDataUrl,
  author: z.string().max(MAX_NAME_LENGTH).optional(),
  tags: z.array(z.string().max(MAX_TAG_LENGTH)).max(MAX_TAGS_COUNT).optional(),
  importDate: iso8601DateTime,
  templateData: LatticeTemplateSchema.optional(),
}).strict();

export type SavedTemplate = z.infer<typeof SavedTemplateSchema>;
