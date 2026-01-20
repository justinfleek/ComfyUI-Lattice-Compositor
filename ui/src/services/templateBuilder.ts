/**
 * Template Builder Service
 *
 * Manages the Template Builder functionality including:
 * - Setting/clearing master composition
 * - Adding/removing exposed properties
 * - Managing property groups
 * - Generating property bindings
 * - Template export preparation (.lattice.json)
 */

import type { EffectInstance } from "../types/effects";
import type {
  AnimatableProperty,
  Composition,
  Layer,
  TextData,
  ImageLayerData,
  VideoData,
  SolidLayerData,
} from "../types/project";
import type { AssetReference, ModelFormat, PointCloudFormat } from "../types/assets";
import type {
  ExposedProperty,
  ExposedPropertyType,
  LatticeTemplate,
  PropertyGroup,
  TemplateAsset,
  TemplateFont,
  TemplateComment,
  TemplateConfig,
  TemplateExportSettings,
} from "../types/templateBuilder";
import type { AssetType } from "../types/assets";
import {
  createDefaultTemplateConfig,
  createExposedProperty,
  createPropertyGroup,
  createTemplateComment,
} from "../types/templateBuilder";

// ============================================================
// TEMPLATE CONFIGURATION MANAGEMENT
// ============================================================

/**
 * Initialize a composition as a master template
 */
export function initializeTemplate(composition: Composition): TemplateConfig {
  if (composition.templateConfig) {
    return composition.templateConfig;
  }
  return createDefaultTemplateConfig(composition.id, composition.name);
}

/**
 * Clear template configuration from a composition
 */
export function clearTemplate(composition: Composition): void {
  composition.templateConfig = undefined;
}

/**
 * Update template metadata
 */
export function updateTemplateMetadata(
  config: TemplateConfig,
  updates: Partial<
    Pick<
      TemplateConfig,
      "name" | "description" | "author" | "version" | "tags" | "posterFrame"
    >
  >,
): void {
  Object.assign(config, updates);
  config.modified = new Date().toISOString();
}

// ============================================================
// PROPERTY EXPOSURE
// ============================================================

/**
 * Property paths that can be exposed for different layer types
 */
export const EXPOSABLE_PROPERTIES: Record<string, ExposablePropertyDef[]> = {
  // Common transform properties (all layers)
  common: [
    { path: "transform.position", name: "Position", type: "point" },
    { path: "transform.position.x", name: "Position X", type: "number" },
    { path: "transform.position.y", name: "Position Y", type: "number" },
    { path: "transform.rotation", name: "Rotation", type: "number" },
    { path: "transform.scale", name: "Scale", type: "point" },
    { path: "transform.scale.x", name: "Scale X", type: "number" },
    { path: "transform.scale.y", name: "Scale Y", type: "number" },
    { path: "transform.anchor", name: "Anchor Point", type: "point" },
    { path: "transform.opacity", name: "Opacity", type: "number" },
  ],

  // Text layer specific
  text: [
    { path: "data.text", name: "Source Text", type: "sourceText" },
    { path: "data.fontSize", name: "Font Size", type: "number" },
    { path: "data.fontFamily", name: "Font", type: "font" },
    { path: "data.fill", name: "Fill Color", type: "color" },
    { path: "data.stroke", name: "Stroke Color", type: "color" },
    { path: "data.strokeWidth", name: "Stroke Width", type: "number" },
    { path: "data.letterSpacing", name: "Letter Spacing", type: "number" },
    { path: "data.lineHeight", name: "Line Height", type: "number" },
  ],

  // Solid layer
  solid: [{ path: "data.color", name: "Color", type: "color" }],

  // Image layer
  image: [{ path: "data.source", name: "Source", type: "media" }],

  // Video layer
  video: [
    { path: "data.source", name: "Source", type: "media" },
    { path: "data.volume", name: "Volume", type: "number" },
  ],

  // Shape layer
  shape: [
    { path: "data.fill.color", name: "Fill Color", type: "color" },
    { path: "data.stroke.color", name: "Stroke Color", type: "color" },
    { path: "data.stroke.width", name: "Stroke Width", type: "number" },
  ],
};

interface ExposablePropertyDef {
  path: string;
  name: string;
  type: ExposedPropertyType;
}

/**
 * Get all exposable properties for a layer
 */
export function getExposableProperties(layer: Layer): ExposablePropertyDef[] {
  const properties: ExposablePropertyDef[] = [...EXPOSABLE_PROPERTIES.common];

  // Add layer-type specific properties
  const typeProps = EXPOSABLE_PROPERTIES[layer.type];
  if (typeProps) {
    properties.push(...typeProps);
  }

  // Add effect parameters
  if (layer.effects) {
    layer.effects.forEach((effect, effectIndex) => {
      Object.entries(effect.parameters).forEach(([paramKey, param]) => {
        const paramType = getPropertyType(param);
        properties.push({
          path: `effects.${effectIndex}.parameters.${paramKey}`,
          name: `${effect.name} - ${param.name}`,
          type: paramType,
        });
      });
    });
  }

  return properties;
}

/**
 * Determine the exposed property type from an AnimatableProperty
 */
function getPropertyType(param: AnimatableProperty<any>): ExposedPropertyType {
  switch (param.type) {
    case "number":
      return "number";
    case "color":
      return "color";
    case "position":
      return "point";
    case "enum":
      return "dropdown";
    default:
      return "number";
  }
}

/**
 * Add a property to the Essential Graphics panel
 */
export function addExposedProperty(
  config: TemplateConfig,
  layerId: string,
  propertyPath: string,
  name: string,
  type: ExposedPropertyType,
): ExposedProperty {
  const order = config.exposedProperties.length;
  const exposed = createExposedProperty(
    layerId,
    propertyPath,
    name,
    type,
    order,
  );
  config.exposedProperties.push(exposed);
  config.modified = new Date().toISOString();
  return exposed;
}

/**
 * Remove an exposed property
 */
export function removeExposedProperty(
  config: TemplateConfig,
  propertyId: string,
): boolean {
  const index = config.exposedProperties.findIndex((p) => p.id === propertyId);
  if (index === -1) return false;

  config.exposedProperties.splice(index, 1);

  // Reorder remaining properties
  config.exposedProperties.forEach((p, i) => {
    p.order = i;
  });

  config.modified = new Date().toISOString();
  return true;
}

/**
 * Update an exposed property
 */
export function updateExposedProperty(
  config: TemplateConfig,
  propertyId: string,
  updates: Partial<ExposedProperty>,
): boolean {
  const property = config.exposedProperties.find((p) => p.id === propertyId);
  if (!property) return false;

  Object.assign(property, updates);
  config.modified = new Date().toISOString();
  return true;
}

/**
 * Reorder exposed properties
 */
export function reorderExposedProperties(
  config: TemplateConfig,
  propertyIds: string[],
): void {
  const reordered: ExposedProperty[] = [];

  propertyIds.forEach((id, index) => {
    const property = config.exposedProperties.find((p) => p.id === id);
    if (property) {
      property.order = index;
      reordered.push(property);
    }
  });

  // Add any properties that weren't in the reorder list
  config.exposedProperties.forEach((p) => {
    if (!reordered.includes(p)) {
      p.order = reordered.length;
      reordered.push(p);
    }
  });

  config.exposedProperties = reordered;
  config.modified = new Date().toISOString();
}

// ============================================================
// PROPERTY GROUPS
// ============================================================

/**
 * Add a property group
 */
export function addPropertyGroup(
  config: TemplateConfig,
  name: string,
): PropertyGroup {
  const order = config.groups.length;
  const group = createPropertyGroup(name, order);
  config.groups.push(group);
  config.modified = new Date().toISOString();
  return group;
}

/**
 * Remove a property group
 */
export function removePropertyGroup(
  config: TemplateConfig,
  groupId: string,
): boolean {
  const index = config.groups.findIndex((g) => g.id === groupId);
  if (index === -1) return false;

  // Remove group from properties
  config.exposedProperties.forEach((p) => {
    if (p.groupId === groupId) {
      p.groupId = undefined;
    }
  });

  config.groups.splice(index, 1);
  config.modified = new Date().toISOString();
  return true;
}

/**
 * Move a property into a group
 */
export function movePropertyToGroup(
  config: TemplateConfig,
  propertyId: string,
  groupId: string | undefined,
): boolean {
  const property = config.exposedProperties.find((p) => p.id === propertyId);
  if (!property) return false;

  property.groupId = groupId;
  config.modified = new Date().toISOString();
  return true;
}

/**
 * Reorder groups
 */
export function reorderGroups(
  config: TemplateConfig,
  groupIds: string[],
): void {
  groupIds.forEach((id, index) => {
    const group = config.groups.find((g) => g.id === id);
    if (group) {
      group.order = index;
    }
  });

  config.groups.sort((a, b) => a.order - b.order);
  config.modified = new Date().toISOString();
}

// ============================================================
// COMMENTS
// ============================================================

/**
 * Add a comment/instruction
 */
export function addComment(
  config: TemplateConfig,
  text: string,
): TemplateComment {
  const order = config.comments.length + config.exposedProperties.length;
  const comment = createTemplateComment(text, order);
  config.comments.push(comment);
  config.modified = new Date().toISOString();
  return comment;
}

/**
 * Update a comment
 */
export function updateComment(
  config: TemplateConfig,
  commentId: string,
  text: string,
): boolean {
  const comment = config.comments.find((c) => c.id === commentId);
  if (!comment) return false;

  comment.text = text;
  config.modified = new Date().toISOString();
  return true;
}

/**
 * Remove a comment
 */
export function removeComment(
  config: TemplateConfig,
  commentId: string,
): boolean {
  const index = config.comments.findIndex((c) => c.id === commentId);
  if (index === -1) return false;

  config.comments.splice(index, 1);
  config.modified = new Date().toISOString();
  return true;
}

// ============================================================
// PROPERTY VALUE ACCESS
// ============================================================

type PropertyValue =
  | string
  | number
  | boolean
  | { x: number; y: number }
  | string[]
  | number[]
  | AnimatableProperty<number>
  | AnimatableProperty<{ x: number; y: number }>
  | Record<string, string | number | boolean | { x: number; y: number } | string[] | number[]>
  | (string | number | boolean | { x: number; y: number })[];

/**
 * Get the value of a property at a path
 */
export function getPropertyValue(
  layer: Layer,
  propertyPath: string,
): PropertyValue | undefined {
  const parts = propertyPath.split(".");
  let current: PropertyValue | Layer | Record<string, PropertyValue> = layer;

  for (const part of parts) {
    if (current === undefined || current === null) return undefined;

    const arrayMatch = part.match(/^(\d+)$/);
    if (arrayMatch && Array.isArray(current)) {
      current = current[parseInt(arrayMatch[1], 10)] as PropertyValue;
    } else if (typeof current === "object" && current !== null && !Array.isArray(current)) {
      current = (current as Record<string, PropertyValue>)[part];
    } else {
      return undefined;
    }
  }

  if (current && typeof current === "object" && !Array.isArray(current) && "value" in current) {
    return (current as AnimatableProperty<number>).value as PropertyValue;
  }

  return current as PropertyValue | undefined;
}

/**
 * Set the value of a property at a path
 */
export function setPropertyValue(
  layer: Layer,
  propertyPath: string,
  value: PropertyValue,
): boolean {
  const parts = propertyPath.split(".");
  let current: PropertyValue | Layer | Record<string, PropertyValue> = layer;

  for (let i = 0; i < parts.length - 1; i++) {
    const part = parts[i];
    if (current === undefined || current === null) return false;

    const arrayMatch = part.match(/^(\d+)$/);
    if (arrayMatch && Array.isArray(current)) {
      current = current[parseInt(arrayMatch[1], 10)] as PropertyValue | Record<string, PropertyValue>;
    } else if (typeof current === "object" && current !== null && !Array.isArray(current)) {
      current = (current as Record<string, PropertyValue>)[part];
    } else {
      return false;
    }
  }

  if (current === undefined || current === null) return false;
  if (typeof current !== "object" || Array.isArray(current)) return false;

  const lastPart = parts[parts.length - 1];
  const target = (current as Record<string, PropertyValue>)[lastPart];

  if (
    target &&
    typeof target === "object" &&
    !Array.isArray(target) &&
    "value" in target
  ) {
    (target as AnimatableProperty<number>).value = value as number;
  } else {
    (current as Record<string, PropertyValue>)[lastPart] = value;
  }

  return true;
}

// ============================================================
// EXPRESSION CONTROL ACCESS
// ============================================================

/**
 * Get the value of an expression control effect on a layer
 * This enables expressions like: effect("Slider Control")("Slider")
 */
type EffectParameterValue = string | number | boolean | { x: number; y: number };

export function getEffectControlValue(
  layer: Layer,
  effectName: string,
  parameterName: string,
): EffectParameterValue | null {
  if (!layer.effects) return null;

  // Find effect by name
  const effect = layer.effects.find((e) => e.name === effectName);
  if (!effect) return null;

  // Find parameter by name
  const paramKey = parameterName.toLowerCase().replace(/\s+/g, "_");
  const param = effect.parameters[paramKey];
  if (!param) return null;

  return param.value;
}

/**
 * Get all expression control effects on a layer
 */
export function getExpressionControls(layer: Layer): EffectInstance[] {
  if (!layer.effects) return [];

  return layer.effects.filter(
    (e) =>
      e.effectKey === "slider-control" ||
      e.effectKey === "checkbox-control" ||
      e.effectKey === "dropdown-menu-control" ||
      e.effectKey === "color-control" ||
      e.effectKey === "point-control" ||
      e.effectKey === "angle-control" ||
      e.effectKey === "layer-control",
  );
}

// ============================================================
// TEMPLATE EXPORT
// ============================================================

/**
 * Prepare Lattice Template for export (.lattice.json)
 */
export function prepareTemplateExport(
  composition: Composition,
  assets: Record<string, AssetReference>,
  posterImageData: string,
): LatticeTemplate | null {
  if (!composition.templateConfig) {
    console.error(
      "[TemplateBuilder] Cannot export - no template configuration",
    );
    return null;
  }

  const config = composition.templateConfig;

  // Validate all exposed properties exist
  const validProperties: ExposedProperty[] = [];
  for (const prop of config.exposedProperties) {
    const layer = composition.layers.find((l) => l.id === prop.sourceLayerId);
    if (!layer) {
      console.warn(
        `[TemplateBuilder] Skipping property "${prop.name}" - layer not found`,
      );
      continue;
    }

    const value = getPropertyValue(layer, prop.sourcePropertyPath);
    if (value === undefined) {
      console.warn(
        `[TemplateBuilder] Skipping property "${prop.name}" - property not found`,
      );
      continue;
    }

    validProperties.push(prop);
  }

  // Build template
  const template: LatticeTemplate = {
    formatVersion: "1.0.0",
    templateConfig: {
      ...config,
      exposedProperties: validProperties,
    },
    composition: serializeComposition(composition),
    assets: collectAssets(composition, assets, config.exportSettings),
    fonts: collectFonts(composition, config.exportSettings),
    posterImage: posterImageData,
  };

  return template;
}

import type { SerializedComposition } from "@/types/templateBuilder";

/**
 * Serialize composition for template export
 */
function serializeComposition(composition: Composition): SerializedComposition {
  // Create serialized composition with proper types
  const serialized: SerializedComposition = {
    id: composition.id,
    name: composition.name,
    settings: composition.settings,
    layers: composition.layers,
    currentFrame: composition.currentFrame,
    isNestedComp: composition.isNestedComp,
    parentCompositionId: composition.parentCompositionId,
    workflowId: composition.workflowId,
    workflowInputs: composition.workflowInputs,
    workflowOutputs: composition.workflowOutputs,
    // Exclude templateConfig from serialized version (it's stored separately in templateConfig)
    globalLight: composition.globalLight,
    markers: composition.markers,
  };

  return serialized;
}

/**
 * Collect assets referenced by the composition
 */
function collectAssets(
  composition: Composition,
  assets: Record<string, AssetReference>,
  settings: TemplateExportSettings,
): TemplateAsset[] {
  if (!settings.includeMedia) return [];

  const usedAssetIds = new Set<string>();

  // Find all asset references in layers
  composition.layers.forEach((layer) => {
    if (layer.data && typeof layer.data === "object") {
      const data = layer.data as TextData | ImageLayerData | VideoData | SolidLayerData;
      if ("source" in data && typeof data.source === "string") {
        usedAssetIds.add(data.source);
      }
      if ("assetId" in data && typeof data.assetId === "string") {
        usedAssetIds.add(data.assetId);
      }
    }
  });

  const MODEL_FORMAT_MIME_TYPES: Record<ModelFormat, string> = {
    gltf: "model/gltf+json",
    glb: "model/gltf-binary",
    obj: "model/obj",
    fbx: "application/octet-stream",
    usd: "model/usd",
    usda: "model/usd",
    usdc: "model/usd",
    usdz: "model/usd",
  };

  const POINT_CLOUD_FORMAT_MIME_TYPES: Record<PointCloudFormat, string> = {
    ply: "application/ply",
    pcd: "application/pcd",
    las: "application/octet-stream",
    laz: "application/octet-stream",
    xyz: "text/plain",
    pts: "text/plain",
  };

  const VIDEO_EXTENSION_MIME_TYPES: Record<string, string> = {
    ".mp4": "video/mp4",
    ".webm": "video/webm",
    ".mov": "video/quicktime",
  };

  const AUDIO_EXTENSION_MIME_TYPES: Record<string, string> = {
    ".mp3": "audio/mpeg",
    ".wav": "audio/wav",
    ".ogg": "audio/ogg",
    ".m4a": "audio/mp4",
  };

  const IMAGE_EXTENSION_MIME_TYPES: Record<string, string> = {
    ".png": "image/png",
    ".jpg": "image/jpeg",
    ".jpeg": "image/jpeg",
    ".webp": "image/webp",
    ".exr": "image/x-exr",
    ".hdr": "image/vnd.radiance",
    ".gif": "image/gif",
  };

  const MATERIAL_EXTENSION_MIME_TYPES: Record<string, string> = {
    ".json": "application/json",
    ".mtl": "model/mtl",
  };

  const LUT_EXTENSION_MIME_TYPES: Record<string, string> = {
    ".cube": "text/x-cube",
    ".3dl": "application/octet-stream",
  };

  function getFileExtension(filename: string): string {
    const lastDot = filename.lastIndexOf(".");
    return lastDot >= 0 ? filename.substring(lastDot).toLowerCase() : "";
  }

  function getMimeTypeForAsset(asset: AssetReference): string {
    if (asset.type === "model" && asset.modelFormat) {
      return MODEL_FORMAT_MIME_TYPES[asset.modelFormat];
    }

    if (asset.type === "pointcloud" && asset.pointCloudFormat) {
      return POINT_CLOUD_FORMAT_MIME_TYPES[asset.pointCloudFormat];
    }

    if (asset.type === "svg") {
      return "image/svg+xml";
    }

    const extension = asset.filename ? getFileExtension(asset.filename) : "";

    if (asset.type === "video") {
      return VIDEO_EXTENSION_MIME_TYPES[extension] || "video/mp4";
    }

    if (asset.type === "audio") {
      return AUDIO_EXTENSION_MIME_TYPES[extension] || "audio/mpeg";
    }

    if (asset.type === "material") {
      return MATERIAL_EXTENSION_MIME_TYPES[extension] || "application/json";
    }

    if (asset.type === "lut") {
      return LUT_EXTENSION_MIME_TYPES[extension] || "image/png";
    }

    if (
      asset.type === "texture" ||
      asset.type === "depth_map" ||
      asset.type === "sprite" ||
      asset.type === "spritesheet" ||
      asset.type === "hdri" ||
      asset.type === "image"
    ) {
      return IMAGE_EXTENSION_MIME_TYPES[extension] || "image/png";
    }

    return "application/octet-stream";
  }

  const collectedAssets: TemplateAsset[] = [];
  usedAssetIds.forEach((assetId) => {
    const asset = assets[assetId];
    if (asset) {
      collectedAssets.push({
        id: assetId,
        name: asset.filename || assetId,
        type: asset.type,
        data: asset.data,
        mimeType: getMimeTypeForAsset(asset),
      });
    }
  });

  return collectedAssets;
}

/**
 * Collect fonts used in the composition
 */
function collectFonts(
  composition: Composition,
  settings: TemplateExportSettings,
): TemplateFont[] {
  const fonts: TemplateFont[] = [];
  const fontFamilies = new Set<string>();

  // Find all font references in text layers
  composition.layers.forEach((layer) => {
    if (layer.type === "text" && layer.data) {
      const data = layer.data as TextData;
      if (data.fontFamily) {
        fontFamilies.add(data.fontFamily);
      }
    }
  });

  // Build font references
  fontFamilies.forEach((family) => {
    fonts.push({
      family,
      style: "normal",
      embedded: settings.includeFonts,
      source: "google", // Assume Google Fonts for now
    });
  });

  return fonts;
}

/**
 * Export template as downloadable .lattice.json file
 */
export async function exportTemplate(
  composition: Composition,
  assets: Record<string, AssetReference>,
  posterImageData: string,
): Promise<Blob | null> {
  const template = prepareTemplateExport(composition, assets, posterImageData);
  if (!template) return null;

  // Create JSON blob
  const json = JSON.stringify(template, null, 2);
  return new Blob([json], { type: "application/json" });
}

// ============================================================
// TEMPLATE VALIDATION
// ============================================================

/**
 * Validate template configuration
 */
export function validateTemplate(
  config: TemplateConfig,
  composition: Composition,
): TemplateValidationResult {
  const errors: string[] = [];
  const warnings: string[] = [];

  // Check template name
  if (!config.name || config.name.trim() === "") {
    errors.push("Template name is required");
  }

  // Check exposed properties
  if (config.exposedProperties.length === 0) {
    warnings.push(
      "No properties exposed - template will have no editable controls",
    );
  }

  // Validate each exposed property
  config.exposedProperties.forEach((prop) => {
    const layer = composition.layers.find((l) => l.id === prop.sourceLayerId);
    if (!layer) {
      errors.push(`Property "${prop.name}" references missing layer`);
      return;
    }

    const value = getPropertyValue(layer, prop.sourcePropertyPath);
    if (value === undefined) {
      errors.push(
        `Property "${prop.name}" path not found: ${prop.sourcePropertyPath}`,
      );
    }
  });

  // Check groups
  config.groups.forEach((group) => {
    const propsInGroup = config.exposedProperties.filter(
      (p) => p.groupId === group.id,
    );
    if (propsInGroup.length === 0) {
      warnings.push(`Group "${group.name}" is empty`);
    }
  });

  return {
    valid: errors.length === 0,
    errors,
    warnings,
  };
}

export interface TemplateValidationResult {
  valid: boolean;
  errors: string[];
  warnings: string[];
}

// ============================================================
// UTILITY FUNCTIONS
// ============================================================

/**
 * Get organized properties grouped by their groups
 */
export function getOrganizedProperties(
  config: TemplateConfig,
): OrganizedProperties {
  const ungrouped: (ExposedProperty | TemplateComment)[] = [];
  const groups: Map<string, (ExposedProperty | TemplateComment)[]> = new Map();

  // Initialize groups
  config.groups.forEach((group) => {
    groups.set(group.id, []);
  });

  // Organize properties
  config.exposedProperties.forEach((prop) => {
    if (prop.groupId && groups.has(prop.groupId)) {
      groups.get(prop.groupId)?.push(prop);
    } else {
      ungrouped.push(prop);
    }
  });

  // Organize comments
  config.comments.forEach((comment) => {
    if (comment.groupId && groups.has(comment.groupId)) {
      groups.get(comment.groupId)?.push(comment);
    } else {
      ungrouped.push(comment);
    }
  });

  // Sort by order
  ungrouped.sort((a, b) => a.order - b.order);
  groups.forEach((items) => {
    items.sort((a, b) => a.order - b.order);
  });

  return {
    ungrouped,
    groups: config.groups.map((group) => ({
      group,
      items: groups.get(group.id) || [],
    })),
  };
}

export interface OrganizedProperties {
  ungrouped: (ExposedProperty | TemplateComment)[];
  groups: Array<{
    group: PropertyGroup;
    items: (ExposedProperty | TemplateComment)[];
  }>;
}

/**
 * Check if an item is an ExposedProperty
 */
export function isExposedProperty(
  item: ExposedProperty | TemplateComment,
): item is ExposedProperty {
  return "sourceLayerId" in item;
}

/**
 * Check if an item is a TemplateComment
 */
export function isTemplateComment(
  item: ExposedProperty | TemplateComment,
): item is TemplateComment {
  return "text" in item && !("sourceLayerId" in item);
}
