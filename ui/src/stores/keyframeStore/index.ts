/**
 * Keyframe Store
 *
 * Domain store for keyframe CRUD operations, interpolation, expressions, and clipboard.
 *
 * MODULE STRUCTURE:
 * - types.ts: Type definitions and interfaces
 * - helpers.ts: Utility functions (findPropertyByPath, safeFrame)
 * - crud.ts: Add, remove, clear, move, update keyframes
 * - interpolation.ts: Interpolation, handles, control mode
 * - property.ts: Property value/animated state
 * - query.ts: Query utilities (getKeyframesAtFrame, etc.)
 * - timing.ts: Scale, reverse, insert, roving
 * - clipboard.ts: Copy/paste keyframes
 * - velocity.ts: Velocity application
 * - dimensions.ts: Separate/link dimensions
 * - expressions.ts: Expression operations
 * - autoBezier.ts: Auto bezier tangent calculation
 */

import { defineStore } from "pinia";

// ============================================================================
// MODULE IMPORTS
// ============================================================================

// Types (re-export for consumers)
export type {
  VelocitySettings,
  KeyframeSelection,
  KeyframeState,
  KeyframeStoreAccess,
} from "./types";

// Helpers (re-export for consumers)
export { findPropertyByPath, safeFrame } from "./helpers";

// CRUD operations
import {
  addKeyframe as addKeyframeImpl,
  removeKeyframe as removeKeyframeImpl,
  clearKeyframes as clearKeyframesImpl,
  updateLayerProperty as updateLayerPropertyImpl,
  moveKeyframe as moveKeyframeImpl,
  moveKeyframes as moveKeyframesImpl,
  setKeyframeValue as setKeyframeValueImpl,
  updateKeyframe as updateKeyframeImpl,
} from "./crud";

// Interpolation operations
import {
  setKeyframeInterpolation as setKeyframeInterpolationImpl,
  setKeyframeHandle as setKeyframeHandleImpl,
  setKeyframeControlMode as setKeyframeControlModeImpl,
  setKeyframeHandleWithMode as setKeyframeHandleWithModeImpl,
} from "./interpolation";

// Property operations
import {
  setPropertyValue as setPropertyValueImpl,
  setPropertyAnimated as setPropertyAnimatedImpl,
} from "./property";

// Query operations
import {
  getKeyframesAtFrame as getKeyframesAtFrameImpl,
  getAllKeyframeFrames as getAllKeyframeFramesImpl,
  findNextKeyframeFrame as findNextKeyframeFrameImpl,
  findPrevKeyframeFrame as findPrevKeyframeFrameImpl,
  findSurroundingKeyframes as findSurroundingKeyframesImpl,
} from "./query";
// Re-export for direct usage
export { findSurroundingKeyframes } from "./query";

// Timing operations
import {
  scaleKeyframeTiming as scaleKeyframeTimingImpl,
  timeReverseKeyframes as timeReverseKeyframesImpl,
  insertKeyframeOnPath as insertKeyframeOnPathImpl,
  applyRovingToPosition as applyRovingToPositionImpl,
  checkRovingImpact as checkRovingImpactImpl,
} from "./timing";

// Clipboard operations
import {
  copyKeyframes as copyKeyframesImpl,
  pasteKeyframes as pasteKeyframesImpl,
  hasKeyframesInClipboard as hasKeyframesInClipboardImpl,
} from "./clipboard";

// Velocity operations
import {
  applyKeyframeVelocity as applyKeyframeVelocityImpl,
  getKeyframeVelocity as getKeyframeVelocityImpl,
} from "./velocity";

// Dimensions operations
import {
  separatePositionDimensionsAction as separatePositionDimensionsActionImpl,
  linkPositionDimensionsAction as linkPositionDimensionsActionImpl,
  separateScaleDimensionsAction as separateScaleDimensionsActionImpl,
  linkScaleDimensionsAction as linkScaleDimensionsActionImpl,
  hasPositionSeparated as hasPositionSeparatedImpl,
  hasScaleSeparated as hasScaleSeparatedImpl,
} from "./dimensions";

// Expression operations
import {
  setPropertyExpression as setPropertyExpressionImpl,
  enablePropertyExpression as enablePropertyExpressionImpl,
  disablePropertyExpression as disablePropertyExpressionImpl,
  togglePropertyExpression as togglePropertyExpressionImpl,
  removePropertyExpression as removePropertyExpressionImpl,
  getPropertyExpression as getPropertyExpressionImpl,
  hasPropertyExpression as hasPropertyExpressionImpl,
  updateExpressionParams as updateExpressionParamsImpl,
  convertExpressionToKeyframes as convertExpressionToKeyframesImpl,
  canBakeExpression as canBakeExpressionImpl,
} from "./expressions";

// Auto bezier operations
import {
  autoCalculateBezierTangents as autoCalculateBezierTangentsImpl,
  autoCalculateAllBezierTangents as autoCalculateAllBezierTangentsImpl,
} from "./autoBezier";

// Property evaluation operations
import {
  getPropertyValueAtFrame as getPropertyValueAtFrameImpl,
  evaluatePropertyAtFrame as evaluatePropertyAtFrameImpl,
  getInterpolatedValue as getInterpolatedValueImpl,
} from "./evaluation";

// Types for internal use
import type {
  KeyframeState,
  VelocitySettings,
} from "./types";
import type {
  AnimatableProperty,
  BezierHandle,
  ClipboardKeyframe,
  InterpolationType,
  Keyframe,
  PropertyExpression,
  PropertyValue,
} from "@/types/project";

// ============================================================================
// STORE DEFINITION
// ============================================================================

export const useKeyframeStore = defineStore("keyframe", {
  state: (): KeyframeState => ({
    clipboard: {
      keyframes: [],
    },
  }),

  getters: {
    /** Check if clipboard has keyframes */
    hasKeyframesInClipboard: (state) => hasKeyframesInClipboardImpl(state),
  },

  actions: {
    // ========================================================================
    // KEYFRAME CRUD
    // ========================================================================

    addKeyframe<T>(
      layerId: string,
      propertyPath: string,
      value: T,
      atFrame?: number,
    ): Keyframe<T> | null {
      return addKeyframeImpl(layerId, propertyPath, value, atFrame);
    },

    removeKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): void {
      removeKeyframeImpl(layerId, propertyPath, keyframeId);
    },

    clearKeyframes(
      layerId: string,
      propertyPath: string,
    ): void {
      clearKeyframesImpl(layerId, propertyPath);
    },

    updateLayerProperty(
      layerId: string,
      propertyPath: string,
      propertyData: Partial<AnimatableProperty<PropertyValue>>,
    ): boolean {
      return updateLayerPropertyImpl(layerId, propertyPath, propertyData);
    },

    moveKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newFrame: number,
    ): void {
      moveKeyframeImpl(layerId, propertyPath, keyframeId, newFrame);
    },

    moveKeyframes(
      keyframes: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
      frameDelta: number,
    ): void {
      moveKeyframesImpl(keyframes, frameDelta);
    },

    setKeyframeValue(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newValue: PropertyValue,
    ): void {
      setKeyframeValueImpl(layerId, propertyPath, keyframeId, newValue);
    },

    updateKeyframe(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      updates: { frame?: number; value?: PropertyValue },
    ): void {
      updateKeyframeImpl(layerId, propertyPath, keyframeId, updates);
    },

    // ========================================================================
    // INTERPOLATION
    // ========================================================================

    setKeyframeInterpolation(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      interpolation: InterpolationType,
    ): void {
      setKeyframeInterpolationImpl(layerId, propertyPath, keyframeId, interpolation);
    },

    setKeyframeHandle(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
    ): void {
      setKeyframeHandleImpl(layerId, propertyPath, keyframeId, handleType, handle);
    },

    setKeyframeControlMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      controlMode: "smooth" | "corner" | "symmetric",
    ): void {
      setKeyframeControlModeImpl(layerId, propertyPath, keyframeId, controlMode);
    },

    setKeyframeHandleWithMode(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
      breakHandle: boolean = false,
    ): void {
      setKeyframeHandleWithModeImpl(
        layerId,
        propertyPath,
        keyframeId,
        handleType,
        handle,
        breakHandle,
      );
    },

    // ========================================================================
    // PROPERTY STATE
    // ========================================================================

    setPropertyValue(
      layerId: string,
      propertyPath: string,
      value: PropertyValue,
    ): void {
      setPropertyValueImpl(layerId, propertyPath, value);
    },

    setPropertyAnimated(
      layerId: string,
      propertyPath: string,
      animated: boolean,
      addKeyframeCallback?: () => void,
    ): void {
      setPropertyAnimatedImpl(layerId, propertyPath, animated, addKeyframeCallback);
    },

    // ========================================================================
    // QUERY UTILITIES
    // ========================================================================

    getKeyframesAtFrame(
      layerId: string,
      frame: number,
    ): Array<{ propertyPath: string; keyframe: Keyframe<PropertyValue> }> {
      return getKeyframesAtFrameImpl(layerId, frame);
    },

    getAllKeyframeFrames(
      layerId: string,
    ): number[] {
      return getAllKeyframeFramesImpl(layerId);
    },

    findNextKeyframeFrame(
      currentFrame: number,
      layerIds: string[],
    ): number | null {
      return findNextKeyframeFrameImpl(currentFrame, layerIds);
    },

    findPrevKeyframeFrame(
      currentFrame: number,
      layerIds: string[],
    ): number | null {
      return findPrevKeyframeFrameImpl(currentFrame, layerIds);
    },

    // ========================================================================
    // TIMING
    // ========================================================================

    scaleKeyframeTiming(
      layerId: string,
      propertyPath: string | undefined,
      scaleFactor: number,
      anchorFrame: number = 0,
    ): number {
      return scaleKeyframeTimingImpl(layerId, propertyPath, scaleFactor, anchorFrame);
    },

    timeReverseKeyframes(
      layerId: string,
      propertyPath?: string,
    ): number {
      return timeReverseKeyframesImpl(layerId, propertyPath);
    },

    insertKeyframeOnPath(
      layerId: string,
      frame: number,
    ): string | null {
      return insertKeyframeOnPathImpl(layerId, frame);
    },

    applyRovingToPosition(
      layerId: string,
    ): boolean {
      return applyRovingToPositionImpl(layerId);
    },

    checkRovingImpact(
      layerId: string,
    ): boolean {
      return checkRovingImpactImpl(layerId);
    },

    // ========================================================================
    // CLIPBOARD
    // ========================================================================

    copyKeyframes(
      keyframeSelections: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
    ): number {
      return copyKeyframesImpl(keyframeSelections);
    },

    pasteKeyframes(
      targetLayerId: string,
      targetPropertyPath?: string,
    ): Keyframe<PropertyValue>[] {
      return pasteKeyframesImpl(targetLayerId, targetPropertyPath);
    },

    // ========================================================================
    // VELOCITY
    // ========================================================================

    applyKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      settings: VelocitySettings,
    ): boolean {
      return applyKeyframeVelocityImpl(layerId, propertyPath, keyframeId, settings);
    },

    getKeyframeVelocity(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): VelocitySettings | null {
      return getKeyframeVelocityImpl(layerId, propertyPath, keyframeId);
    },

    // ========================================================================
    // DIMENSIONS
    // ========================================================================

    separatePositionDimensionsAction(
      layerId: string,
    ): boolean {
      return separatePositionDimensionsActionImpl(layerId);
    },

    linkPositionDimensionsAction(
      layerId: string,
    ): boolean {
      return linkPositionDimensionsActionImpl(layerId);
    },

    separateScaleDimensionsAction(
      layerId: string,
    ): boolean {
      return separateScaleDimensionsActionImpl(layerId);
    },

    linkScaleDimensionsAction(
      layerId: string,
    ): boolean {
      return linkScaleDimensionsActionImpl(layerId);
    },

    hasPositionSeparated(
      layerId: string,
    ): boolean {
      return hasPositionSeparatedImpl(layerId);
    },

    hasScaleSeparated(
      layerId: string,
    ): boolean {
      return hasScaleSeparatedImpl(layerId);
    },

    // ========================================================================
    // AUTO BEZIER
    // ========================================================================

    autoCalculateBezierTangents(
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): boolean {
      return autoCalculateBezierTangentsImpl(layerId, propertyPath, keyframeId);
    },

    autoCalculateAllBezierTangents(
      layerId: string,
      propertyPath: string,
    ): number {
      return autoCalculateAllBezierTangentsImpl(layerId, propertyPath);
    },

    // ========================================================================
    // EXPRESSIONS
    // ========================================================================

    setPropertyExpression(
      layerId: string,
      propertyPath: string,
      expression: PropertyExpression,
    ): boolean {
      return setPropertyExpressionImpl(layerId, propertyPath, expression);
    },

    enablePropertyExpression(
      layerId: string,
      propertyPath: string,
      expressionName: string = "custom",
      params: Record<string, number | string | boolean> = {},
    ): boolean {
      return enablePropertyExpressionImpl(layerId, propertyPath, expressionName, params);
    },

    disablePropertyExpression(
      layerId: string,
      propertyPath: string,
    ): boolean {
      return disablePropertyExpressionImpl(layerId, propertyPath);
    },

    togglePropertyExpression(
      layerId: string,
      propertyPath: string,
    ): boolean {
      return togglePropertyExpressionImpl(layerId, propertyPath);
    },

    removePropertyExpression(
      layerId: string,
      propertyPath: string,
    ): boolean {
      return removePropertyExpressionImpl(layerId, propertyPath);
    },

    getPropertyExpression(
      layerId: string,
      propertyPath: string,
    ): PropertyExpression | undefined {
      return getPropertyExpressionImpl(layerId, propertyPath);
    },

    hasPropertyExpression(
      layerId: string,
      propertyPath: string,
    ): boolean {
      return hasPropertyExpressionImpl(layerId, propertyPath);
    },

    updateExpressionParams(
      layerId: string,
      propertyPath: string,
      params: Record<string, number | string | boolean>,
    ): boolean {
      return updateExpressionParamsImpl(layerId, propertyPath, params);
    },

    convertExpressionToKeyframes(
      layerId: string,
      propertyPath: string,
      startFrame?: number,
      endFrame?: number,
      sampleRate: number = 1,
    ): number {
      return convertExpressionToKeyframesImpl(
        layerId,
        propertyPath,
        startFrame,
        endFrame,
        sampleRate,
      );
    },

    canBakeExpression(
      layerId: string,
      propertyPath: string,
    ): boolean {
      return canBakeExpressionImpl(layerId, propertyPath);
    },

    // ========================================================================
    // PROPERTY EVALUATION
    // ========================================================================

    /**
     * Get a single scalar property value at a specific frame.
     * Returns null if layer not found or property unsupported.
     */
    getPropertyValueAtFrame(
      layerId: string,
      propertyPath: string,
      frame: number,
    ): number | null {
      return getPropertyValueAtFrameImpl(
        layerId,
        propertyPath,
        frame,
      );
    },

    /**
     * Evaluate a property at a specific frame and return the full value.
     * Returns array for vector properties, number for scalars, null if not found.
     */
    evaluatePropertyAtFrame(
      layerId: string,
      propertyPath: string,
      frame: number,
    ): number[] | number | null {
      return evaluatePropertyAtFrameImpl(
        layerId,
        propertyPath,
        frame,
      );
    },

    /**
     * Get interpolated value for any animatable property at current frame.
     * Convenience method that passes fps and duration from composition settings.
     */
    getInterpolatedValue<T>(
      property: AnimatableProperty<T>,
    ): T {
      return getInterpolatedValueImpl(property);
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type KeyframeStoreType = ReturnType<typeof useKeyframeStore>;
