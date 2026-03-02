/**
 * Shape Module - Barrel Export
 *
 * This module organizes shape operations into logical submodules:
 * - pathModifiers: Path effect modifiers (wiggle, zigzag, roughen, wave, twist, pucker/bloat)
 *
 * Import from '@/services/shape' for all shape utilities.
 */

// Path modifier effects
export {
  puckerBloat,
  roughenPath,
  twistPath,
  type WaveType,
  wavePath,
  wigglePath,
  zigZagPath,
} from "./pathModifiers";
