/**
 * Export Template Schema
 *
 * Zod schemas for validating export template configurations stored in localStorage.
 * Includes comprehensive validation constraints for security and data integrity.
 */

import { z } from "zod";
import {
  entityId,
  MAX_NAME_LENGTH,
  MAX_DESCRIPTION_LENGTH,
} from "../shared-validation";
import {
  ExportTargetSchema,
  DepthMapFormatSchema,
  ControlTypeSchema,
} from "../comfyui-schema";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primitives
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = z.number().finite();
const positiveInt = z.number().int().positive();
const nonNegativeInt = z.number().int().nonnegative();
const positiveFinite = z.number().finite().positive();

// ═══════════════════════════════════════════════════════════════════════════
// Export Template Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Export Template
 * Partial ExportConfig with metadata
 */
export const ExportTemplateSchema = z.object({
  id: entityId,
  name: z.string().min(1).max(MAX_NAME_LENGTH).trim(),
  description: z.string().max(MAX_DESCRIPTION_LENGTH).trim().optional(),
  createdAt: nonNegativeInt.max(2147483647000), // Max timestamp (year 2038)
  modifiedAt: nonNegativeInt.max(2147483647000), // Max timestamp (year 2038)
  config: z.object({
    target: ExportTargetSchema.optional(),
    width: positiveInt.max(16384).optional(), // Max reasonable dimension
    height: positiveInt.max(16384).optional(), // Max reasonable dimension
    frameCount: positiveInt.max(100000).optional(), // Max 100k frames
    fps: positiveFinite.max(120).optional(), // Max 120 FPS
    startFrame: nonNegativeInt.max(100000).optional(), // Max 100k frames
    endFrame: nonNegativeInt.max(100000).optional(), // Max 100k frames
    outputDir: z.string().max(500).trim().optional(), // Max path length
    filenamePrefix: z.string().max(255).trim().optional(), // Max filename length
    exportDepthMap: z.boolean().optional(),
    exportControlImages: z.boolean().optional(),
    exportCameraData: z.boolean().optional(),
    exportReferenceFrame: z.boolean().optional(),
    exportLastFrame: z.boolean().optional(),
    depthFormat: DepthMapFormatSchema.optional(),
    controlType: ControlTypeSchema.optional(),
    prompt: z.string().max(10000).trim().optional(), // Max prompt length
    negativePrompt: z.string().max(10000).trim().optional(), // Max prompt length
    seed: z.number().int().max(2147483647).optional(), // Max 32-bit int
    steps: positiveInt.max(1000).optional(), // Max 1000 steps
    cfgScale: positiveFinite.max(30).optional(), // Max 30 CFG scale
    comfyuiServer: z.string().max(2048).url().optional(), // Max URL length
    autoQueueWorkflow: z.boolean().optional(),
    workflowTemplate: z.string().max(10000).trim().optional(), // Max template length
  }).strict().refine(
    (data) => {
      // If endFrame present, should be >= startFrame
      if (data.endFrame !== undefined && data.startFrame !== undefined) {
        return data.endFrame >= data.startFrame;
      }
      return true;
    },
    { message: "endFrame must be >= startFrame", path: ["endFrame"] }
  ),
}).strict().refine(
  (data) => {
    // modifiedAt should be >= createdAt
    return data.modifiedAt >= data.createdAt;
  },
  { message: "modifiedAt must be >= createdAt", path: ["modifiedAt"] }
);

export type ExportTemplate = z.infer<typeof ExportTemplateSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Export Template Store Schema
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Export Template Store
 * Collection of templates with last used tracking
 */
export const ExportTemplateStoreSchema = z.object({
  templates: z.array(ExportTemplateSchema).max(1000), // Max 1000 templates
  lastUsedTemplateId: entityId.optional(),
}).strict().refine(
  (data) => {
    // If lastUsedTemplateId present, should exist in templates
    if (data.lastUsedTemplateId) {
      return data.templates.some((t) => t.id === data.lastUsedTemplateId);
    }
    return true;
  },
  { message: "lastUsedTemplateId must exist in templates array", path: ["lastUsedTemplateId"] }
);

export type ExportTemplateStore = z.infer<typeof ExportTemplateStoreSchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Export Template Array Schema (for imports)
// ═══════════════════════════════════════════════════════════════════════════

export const ExportTemplateArraySchema = z.array(ExportTemplateSchema).max(1000); // Max 1000 templates

export type ExportTemplateArray = z.infer<typeof ExportTemplateArraySchema>;

// ═══════════════════════════════════════════════════════════════════════════
// Validation Helpers
// ═══════════════════════════════════════════════════════════════════════════

export function validateExportTemplate(data: unknown): ExportTemplate {
  return ExportTemplateSchema.parse(data);
}

export function safeValidateExportTemplate(data: unknown) {
  return ExportTemplateSchema.safeParse(data);
}

export function validateExportTemplateStore(data: unknown): ExportTemplateStore {
  return ExportTemplateStoreSchema.parse(data);
}

export function safeValidateExportTemplateStore(data: unknown) {
  return ExportTemplateStoreSchema.safeParse(data);
}

export function validateExportTemplateArray(data: unknown): ExportTemplateArray {
  return ExportTemplateArraySchema.parse(data);
}

export function safeValidateExportTemplateArray(data: unknown) {
  return ExportTemplateArraySchema.safeParse(data);
}
