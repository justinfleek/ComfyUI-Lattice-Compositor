/**
 * Layer Actions Module - Barrel Export
 *
 * This module organizes layer-related actions into logical submodules:
 * - splineActions: Spline control point operations, animation, simplification
 * - layerDefaults: Default data configurations for each layer type
 *
 * Import from '@/stores/actions/layer' for all layer actions.
 */

// Layer defaults
export * from "./layerDefaults";
// Spline operations
export * from "./splineActions";
