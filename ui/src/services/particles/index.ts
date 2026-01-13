/**
 * Particles Module - Barrel Export
 *
 * This module organizes particle system functionality into logical submodules:
 * - particleTypes: All interfaces and type definitions
 * - particleDefaults: Factory functions for default configs
 * - SeededRandom: Deterministic RNG for reproducible simulation
 * - particleRenderer: Canvas rendering functions
 *
 * Import from '@/services/particles' for all particle utilities.
 */

// Default factory functions
export * from "./particleDefaults";
// Rendering functions
export * from "./particleRenderer";
// Type definitions
export * from "./particleTypes";
// Seeded random number generator
export { SeededRandom } from "./SeededRandom";
