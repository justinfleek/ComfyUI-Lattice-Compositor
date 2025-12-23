/**
 * Particles Module - Barrel Export
 *
 * This module organizes particle system functionality into logical submodules:
 * - particleTypes: All interfaces and type definitions
 * - particleDefaults: Factory functions for default configs
 * - SeededRandom: Deterministic RNG for reproducible simulation
 *
 * Import from '@/services/particles' for all particle utilities.
 */

// Type definitions
export * from './particleTypes';

// Default factory functions
export * from './particleDefaults';

// Seeded random number generator
export { SeededRandom } from './SeededRandom';
