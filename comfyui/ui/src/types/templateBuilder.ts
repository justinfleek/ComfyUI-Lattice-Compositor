/**
 * Template Builder System Types
 *
 * This module defines types for the Template Builder, which allows
 * designers to expose controllable parameters from compositions for template
 * users (like video editors in Premiere Pro).
 *
 * Key concepts:
 * - TemplateConfig: Configuration for a composition as a template
 * - ExposedProperty: A layer property exposed in the Template Builder panel
 * - PropertyGroup: Organizational grouping for exposed properties
 * - ExpressionControl: Special controls (Slider, Checkbox, Dropdown) that provide values
 * - SavedTemplate: A template that has been imported and saved for reuse
 * - TemplateExportSettings: Template export configuration
 */

import type { AnimatableProperty } from "./project";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                           // expression // control // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Types of expression controls available
 * These are special "effects" that don't process pixels but provide
 * animatable values accessible to expressions
 */
export type ExpressionControlType =
  | "slider" // Numeric value with range
  | "checkbox" // Boolean toggle
  | "dropdown" // Predefined options
  | "color" // Color picker
  | "point" // 2D coordinate
  | "angle"; // Rotation dial

/**
 * Expression Control - A controllable value attached to a layer
 *
 * These controls provide values that can be:
 * 1. Animated with keyframes
 * 2. Exposed in Essential Graphics panel
 * 3. Referenced in expressions via effect("Control Name")("Slider")
 */
export interface ExpressionControl {
  id: string;
  name: string; // Display name (e.g., "Animation Speed")
  type: ExpressionControlType;

  // The animatable value
  value: AnimatableProperty<any>;

  // Configuration based on type
  config: ExpressionControlConfig;

  // UI state
  expanded?: boolean;
}

/**
 * Configuration for different expression control types
 */
export interface ExpressionControlConfig {
  // For slider
  min?: number;
  max?: number;
  step?: number;

  // For dropdown
  options?: DropdownOption[];

  // For color
  includeAlpha?: boolean;

  // For point
  is3D?: boolean;

  // For angle
  displayUnit?: "degrees" | "radians" | "rotations";
}

export interface DropdownOption {
  label: string;
  value: string | number;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                             // exposed // property // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Types of properties that can be exposed in Essential Graphics
 */
export type ExposedPropertyType =
  | "sourceText" // Editable text content
  | "color" // Color picker
  | "number" // Numeric value (from slider, position, etc.)
  | "checkbox" // Boolean toggle
  | "dropdown" // Predefined options
  | "point" // 2D position
  | "media" // Replaceable image/video
  | "font" // Font selector
  | "layer"; // Layer reference picker (for Layer Control effect)

/**
 * An exposed property in the Essential Graphics panel
 *
 * This represents a property from any layer that has been "added"
 * to the Essential Graphics panel for template customization.
 */
export interface ExposedProperty {
  id: string;

  // Display configuration
  name: string; // User-friendly name shown in panel
  type: ExposedPropertyType;

  // Source binding
  sourceLayerId: string; // Layer containing the property
  sourcePropertyPath: string; // Path to property (e.g., "data.text", "transform.position.x")

  // For expression control sources
  sourceControlId?: string; // If from an expression control

  // Organization
  groupId?: string; // Parent group ID
  order: number; // Display order

  // Configuration
  config: ExposedPropertyConfig;

  // Optional comment/instructions
  comment?: string;

  // Value snapshot for template export/import
  // Type depends on ExposedPropertyType: string | number | boolean | { r: number; g: number; b: number; a: number } | { x: number; y: number }
  defaultValue?: string | number | boolean | { r: number; g: number; b: number; a: number } | { x: number; y: number };
}

/**
 * Configuration for exposed properties
 */
export interface ExposedPropertyConfig {
  // For numeric properties
  min?: number;
  max?: number;
  step?: number;

  // For dropdown properties
  options?: DropdownOption[];

  // For text properties
  maxLength?: number;
  multiline?: boolean;

  // For media properties
  acceptedTypes?: ("image" | "video")[];
  aspectRatio?: number;

  // For font properties
  allowFontChange?: boolean;
  allowSizeChange?: boolean;
  allowColorChange?: boolean;
}

// ═══════════════════════════════════════════════════════════════════════════
//                                               // property // group // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * A group/folder in the Essential Graphics panel
 * Used to organize exposed properties
 */
export interface PropertyGroup {
  id: string;
  name: string;
  expanded: boolean;
  order: number;
  color?: string; // Optional accent color
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                // template // configuration
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Template configuration for a composition
 *
 * When a composition is set as a "master composition", this
 * config stores all the Essential Graphics panel settings.
 */
export interface TemplateConfig {
  // Template metadata
  name: string; // Template name shown in browse panel
  description?: string; // Template description
  author?: string;
  version?: string;
  tags?: string[]; // For search/filtering

  // Master composition reference
  masterCompositionId: string;

  // Exposed properties and organization
  exposedProperties: ExposedProperty[];
  groups: PropertyGroup[];

  // Comments/instructions (not attached to specific properties)
  comments: TemplateComment[];

  // Poster frame for thumbnail
  posterFrame: number; // Frame number for preview thumbnail

  // Export settings
  exportSettings: TemplateExportSettings;

  // Created/modified timestamps
  created: string; // ISO 8601
  modified: string; // ISO 8601
}

/**
 * A standalone comment/instruction in the Essential Graphics panel
 */
export interface TemplateComment {
  id: string;
  text: string;
  order: number;
  groupId?: string; // Can be placed in a group
}

// ═══════════════════════════════════════════════════════════════════════════
//                                              // template // export // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Settings for template export (.lattice.json)
 */
export interface TemplateExportSettings {
  // Asset embedding
  includeFonts: boolean;
  includeMedia: boolean;

  // Responsive settings
  allowDurationChange: boolean;

  // Quality settings
  posterQuality: "low" | "medium" | "high";
}

/**
 * Lattice Template file structure (.lattice.json)
 * Exported templates that can be shared and imported
 */
import type { Composition } from "./project";

/**
 * Serialized composition data for templates
 * This is a JSON-serializable subset of Composition that excludes
 * runtime-only properties and circular references
 */
export interface SerializedComposition {
  id: string;
  name: string;
  settings: Composition["settings"];
  layers: Composition["layers"];
  currentFrame: number;
  isNestedComp: boolean;
  parentCompositionId?: string;
  workflowId?: string;
  workflowInputs?: Composition["workflowInputs"];
  workflowOutputs?: Composition["workflowOutputs"];
  templateConfig?: Composition["templateConfig"];
  globalLight?: Composition["globalLight"];
  markers?: Composition["markers"];
}

export interface LatticeTemplate {
  // Metadata
  formatVersion: string; // Template format version
  templateConfig: TemplateConfig;

  // Composition data (serialized LatticeProject subset)
  composition: SerializedComposition;

  // Embedded assets
  assets: TemplateAsset[];

  // Font references
  fonts: TemplateFont[];

  // Preview
  posterImage: string; // Base64 encoded poster frame
}

export interface TemplateAsset {
  id: string;
  name: string;
  type: "depth_map" | "image" | "video" | "audio" | "model" | "pointcloud" | "texture" | "material" | "hdri" | "svg" | "sprite" | "spritesheet" | "lut";
  data: string; // Base64 encoded or URL
  mimeType: string;
}

export interface TemplateFont {
  family: string;
  style: string;
  embedded: boolean;
  data?: string; // Base64 encoded font file if embedded
  source?: "google" | "cloud" | "local" | "system";
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                  // panel // state // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Template Builder panel UI state
 */
export interface TemplateBuilderState {
  // Current tab
  activeTab: "browse" | "edit";

  // Edit mode state
  masterCompositionId: string | null;
  selectedPropertyIds: string[];
  selectedGroupId: string | null;

  // Browse mode state
  searchQuery: string;
  filterTags: string[];
  savedTemplates: SavedTemplate[];
}

/**
 * A saved template in the browse panel
 * Templates can be imported from .lattice.json files and saved for reuse
 */
export interface SavedTemplate {
  id: string;
  name: string;
  importedFrom?: string; // Original file location (if imported from file)
  posterImage: string; // Thumbnail
  author?: string;
  tags?: string[];
  importDate: string; // When the template was imported/saved
  templateData?: LatticeTemplate; // Full template data
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Create a default template config for a composition
 */
export function createDefaultTemplateConfig(
  compositionId: string,
  compositionName: string,
): TemplateConfig {
  return {
    name: compositionName,
    masterCompositionId: compositionId,
    exposedProperties: [],
    groups: [],
    comments: [],
    posterFrame: 0,
    exportSettings: {
      includeFonts: true,
      includeMedia: true,
      allowDurationChange: false,
      posterQuality: "high",
    },
    created: new Date().toISOString(),
    modified: new Date().toISOString(),
  };
}

/**
 * Create a default expression control
 */
export function createExpressionControl(
  type: ExpressionControlType,
  name: string,
): ExpressionControl {
  const id = `ctrl_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

  let defaultValue: number | boolean | { r: number; g: number; b: number; a: number } | { x: number; y: number };
  let config: ExpressionControlConfig = {};

  switch (type) {
    case "slider":
      defaultValue = 0;
      config = { min: 0, max: 100, step: 1 };
      break;
    case "checkbox":
      defaultValue = false;
      break;
    case "dropdown":
      defaultValue = 0;
      config = {
        options: [
          { label: "Option 1", value: 0 },
          { label: "Option 2", value: 1 },
        ],
      };
      break;
    case "color":
      defaultValue = { r: 1, g: 1, b: 1, a: 1 };
      config = { includeAlpha: true };
      break;
    case "point":
      defaultValue = { x: 0, y: 0 };
      config = { is3D: false };
      break;
    case "angle":
      defaultValue = 0;
      config = { displayUnit: "degrees" };
      break;
  }

  return {
    id,
    name,
    type,
    value: {
      id: `${id}_value`,
      name: "Value",
      type:
        type === "color" ? "color" : type === "point" ? "position" : "number",
      value: defaultValue,
      animated: false,
      keyframes: [],
    },
    config,
    expanded: true,
  };
}

/**
 * Create an exposed property from a layer property
 */
export function createExposedProperty(
  layerId: string,
  propertyPath: string,
  name: string,
  type: ExposedPropertyType,
  order: number,
): ExposedProperty {
  return {
    id: `exp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name,
    type,
    sourceLayerId: layerId,
    sourcePropertyPath: propertyPath,
    order,
    config: {},
  };
}

/**
 * Create a property group
 */
export function createPropertyGroup(
  name: string,
  order: number,
): PropertyGroup {
  return {
    id: `grp_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name,
    expanded: true,
    order,
  };
}

/**
 * Create a template comment
 */
export function createTemplateComment(
  text: string,
  order: number,
): TemplateComment {
  return {
    id: `cmt_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    text,
    order,
  };
}
