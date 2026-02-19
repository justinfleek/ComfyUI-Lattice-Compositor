/**
 * Schema Index
 *
 * Re-exports all Zod schemas for the Lattice Compositor.
 * Namespaced to avoid conflicts between similar schemas in different contexts.
 */

// Import schemas (camera tracking, camera import)
export * as ImportSchemas from "./imports";

// Export schemas (ATI, WanMove, camera export, depth export)
export * as ExportSchemas from "./exports";

// Layer schemas (primitives, animation, transform, layer data, layer)
export * as LayerSchemas from "./layers";

// Project schema (full project file validation)
export * from "./project-schema";
export * as ProjectExportSchemas from "./project";

// ComfyUI schemas (workflow, export config, progress)
export * as ComfyUISchemas from "./comfyui-schema";

// Asset schemas (AssetReference, AssetType, etc.)
export * as AssetSchemas from "./assets";

// Effect schemas (EffectInstance, EffectParameter, etc.)
export * as EffectSchemas from "./effects";

// Physics schemas (RigidBodyConfig, PhysicsVec2, etc.)
export * as PhysicsSchemas from "./physics";

// Mask schemas (LayerMask, MaskPath, etc.)
export * as MaskSchemas from "./masks";

// Layer Styles schemas (LayerStyles, DropShadowStyle, etc.)
export * as LayerStyleSchemas from "./layerStyles";

// Mesh Warp schemas (WarpPin, WarpMesh, etc.)
export * as MeshWarpSchemas from "./meshWarp";

// Preset schemas (PresetMetadata, ParticlePreset, etc.)
export * as PresetSchemas from "./presets";

// Template Builder schemas (TemplateConfig, ExposedProperty, etc.)
export * as TemplateBuilderSchemas from "./templateBuilder";

// Data Asset schemas (DataAsset, JSONDataAsset, CSVDataAsset, etc.)
export * as DataAssetSchemas from "./dataAsset";

// Settings schemas (UserSettings, RecentProjects, ExportTemplates, RateLimits)
export * as SettingsSchemas from "./settings";

// Drag-Drop schemas (ProjectItem for drag-drop operations)
export * as DragDropSchemas from "./dragdrop";

//                                                                        // ai
export * as AISchemas from "./ai";
