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

// ComfyUI schemas (workflow, export config, progress)
export * as ComfyUISchemas from "./comfyui-schema";
