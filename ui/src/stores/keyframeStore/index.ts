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
  KeyframeStoreAccess,
  RovingKeyframeStoreAccess,
  ClipboardKeyframeStoreAccess,
  VelocityStoreAccess,
  BakeExpressionStoreAccess,
  VelocitySettings,
  KeyframeSelection,
  KeyframeState,
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

// Types for internal use
import type {
  KeyframeState,
  KeyframeStoreAccess,
  VelocityStoreAccess,
  ClipboardKeyframeStoreAccess,
  RovingKeyframeStoreAccess,
  BakeExpressionStoreAccess,
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
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      value: T,
      atFrame?: number,
    ): Keyframe<T> | null {
      return addKeyframeImpl(compositorStore, layerId, propertyPath, value, atFrame);
    },

    removeKeyframe(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): void {
      removeKeyframeImpl(compositorStore, layerId, propertyPath, keyframeId);
    },

    clearKeyframes(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): void {
      clearKeyframesImpl(compositorStore, layerId, propertyPath);
    },

    updateLayerProperty(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      propertyData: Partial<AnimatableProperty<any>>,
    ): boolean {
      return updateLayerPropertyImpl(compositorStore, layerId, propertyPath, propertyData);
    },

    moveKeyframe(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newFrame: number,
    ): void {
      moveKeyframeImpl(compositorStore, layerId, propertyPath, keyframeId, newFrame);
    },

    moveKeyframes(
      compositorStore: KeyframeStoreAccess,
      keyframes: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
      frameDelta: number,
    ): void {
      moveKeyframesImpl(compositorStore, keyframes, frameDelta);
    },

    setKeyframeValue(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      newValue: any,
    ): void {
      setKeyframeValueImpl(compositorStore, layerId, propertyPath, keyframeId, newValue);
    },

    updateKeyframe(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      updates: { frame?: number; value?: any },
    ): void {
      updateKeyframeImpl(compositorStore, layerId, propertyPath, keyframeId, updates);
    },

    // ========================================================================
    // INTERPOLATION
    // ========================================================================

    setKeyframeInterpolation(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      interpolation: InterpolationType,
    ): void {
      setKeyframeInterpolationImpl(compositorStore, layerId, propertyPath, keyframeId, interpolation);
    },

    setKeyframeHandle(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
    ): void {
      setKeyframeHandleImpl(compositorStore, layerId, propertyPath, keyframeId, handleType, handle);
    },

    setKeyframeControlMode(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      controlMode: "smooth" | "corner" | "symmetric",
    ): void {
      setKeyframeControlModeImpl(compositorStore, layerId, propertyPath, keyframeId, controlMode);
    },

    setKeyframeHandleWithMode(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      handleType: "in" | "out",
      handle: BezierHandle,
      breakHandle: boolean = false,
    ): void {
      setKeyframeHandleWithModeImpl(
        compositorStore,
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
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      value: any,
    ): void {
      setPropertyValueImpl(compositorStore, layerId, propertyPath, value);
    },

    setPropertyAnimated(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      animated: boolean,
      addKeyframeCallback?: () => void,
    ): void {
      setPropertyAnimatedImpl(compositorStore, layerId, propertyPath, animated, addKeyframeCallback);
    },

    // ========================================================================
    // QUERY UTILITIES
    // ========================================================================

    getKeyframesAtFrame(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      frame: number,
    ): Array<{ propertyPath: string; keyframe: Keyframe<any> }> {
      return getKeyframesAtFrameImpl(compositorStore, layerId, frame);
    },

    getAllKeyframeFrames(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): number[] {
      return getAllKeyframeFramesImpl(compositorStore, layerId);
    },

    findNextKeyframeFrame(
      compositorStore: KeyframeStoreAccess,
      currentFrame: number,
      layerIds: string[],
    ): number | null {
      return findNextKeyframeFrameImpl(compositorStore, currentFrame, layerIds);
    },

    findPrevKeyframeFrame(
      compositorStore: KeyframeStoreAccess,
      currentFrame: number,
      layerIds: string[],
    ): number | null {
      return findPrevKeyframeFrameImpl(compositorStore, currentFrame, layerIds);
    },

    // ========================================================================
    // TIMING
    // ========================================================================

    scaleKeyframeTiming(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string | undefined,
      scaleFactor: number,
      anchorFrame: number = 0,
    ): number {
      return scaleKeyframeTimingImpl(compositorStore, layerId, propertyPath, scaleFactor, anchorFrame);
    },

    timeReverseKeyframes(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath?: string,
    ): number {
      return timeReverseKeyframesImpl(compositorStore, layerId, propertyPath);
    },

    insertKeyframeOnPath(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      frame: number,
    ): string | null {
      return insertKeyframeOnPathImpl(compositorStore, layerId, frame);
    },

    applyRovingToPosition(
      compositorStore: RovingKeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return applyRovingToPositionImpl(compositorStore, layerId);
    },

    checkRovingImpact(
      compositorStore: RovingKeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return checkRovingImpactImpl(compositorStore, layerId);
    },

    // ========================================================================
    // CLIPBOARD
    // ========================================================================

    copyKeyframes(
      compositorStore: ClipboardKeyframeStoreAccess,
      keyframeSelections: Array<{
        layerId: string;
        propertyPath: string;
        keyframeId: string;
      }>,
    ): number {
      return copyKeyframesImpl(compositorStore, keyframeSelections);
    },

    pasteKeyframes(
      compositorStore: ClipboardKeyframeStoreAccess,
      targetLayerId: string,
      targetPropertyPath?: string,
    ): Keyframe<PropertyValue>[] {
      return pasteKeyframesImpl(compositorStore, targetLayerId, targetPropertyPath);
    },

    // ========================================================================
    // VELOCITY
    // ========================================================================

    applyKeyframeVelocity(
      compositorStore: VelocityStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
      settings: VelocitySettings,
    ): boolean {
      return applyKeyframeVelocityImpl(compositorStore, layerId, propertyPath, keyframeId, settings);
    },

    getKeyframeVelocity(
      compositorStore: VelocityStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): VelocitySettings | null {
      return getKeyframeVelocityImpl(compositorStore, layerId, propertyPath, keyframeId);
    },

    // ========================================================================
    // DIMENSIONS
    // ========================================================================

    separatePositionDimensionsAction(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return separatePositionDimensionsActionImpl(compositorStore, layerId);
    },

    linkPositionDimensionsAction(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return linkPositionDimensionsActionImpl(compositorStore, layerId);
    },

    separateScaleDimensionsAction(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return separateScaleDimensionsActionImpl(compositorStore, layerId);
    },

    linkScaleDimensionsAction(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return linkScaleDimensionsActionImpl(compositorStore, layerId);
    },

    hasPositionSeparated(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return hasPositionSeparatedImpl(compositorStore, layerId);
    },

    hasScaleSeparated(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
    ): boolean {
      return hasScaleSeparatedImpl(compositorStore, layerId);
    },

    // ========================================================================
    // AUTO BEZIER
    // ========================================================================

    autoCalculateBezierTangents(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      keyframeId: string,
    ): boolean {
      return autoCalculateBezierTangentsImpl(compositorStore, layerId, propertyPath, keyframeId);
    },

    autoCalculateAllBezierTangents(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): number {
      return autoCalculateAllBezierTangentsImpl(compositorStore, layerId, propertyPath);
    },

    // ========================================================================
    // EXPRESSIONS
    // ========================================================================

    setPropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      expression: PropertyExpression,
    ): boolean {
      return setPropertyExpressionImpl(compositorStore, layerId, propertyPath, expression);
    },

    enablePropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      expressionName: string = "custom",
      params: Record<string, number | string | boolean> = {},
    ): boolean {
      return enablePropertyExpressionImpl(compositorStore, layerId, propertyPath, expressionName, params);
    },

    disablePropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return disablePropertyExpressionImpl(compositorStore, layerId, propertyPath);
    },

    togglePropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return togglePropertyExpressionImpl(compositorStore, layerId, propertyPath);
    },

    removePropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return removePropertyExpressionImpl(compositorStore, layerId, propertyPath);
    },

    getPropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): PropertyExpression | undefined {
      return getPropertyExpressionImpl(compositorStore, layerId, propertyPath);
    },

    hasPropertyExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return hasPropertyExpressionImpl(compositorStore, layerId, propertyPath);
    },

    updateExpressionParams(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
      params: Record<string, number | string | boolean>,
    ): boolean {
      return updateExpressionParamsImpl(compositorStore, layerId, propertyPath, params);
    },

    convertExpressionToKeyframes(
      compositorStore: BakeExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
      startFrame?: number,
      endFrame?: number,
      sampleRate: number = 1,
    ): number {
      return convertExpressionToKeyframesImpl(
        compositorStore,
        layerId,
        propertyPath,
        startFrame,
        endFrame,
        sampleRate,
      );
    },

    canBakeExpression(
      compositorStore: KeyframeStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return canBakeExpressionImpl(compositorStore, layerId, propertyPath);
    },
  },
});

// ============================================================================
// TYPE EXPORTS
// ============================================================================

export type KeyframeStoreType = ReturnType<typeof useKeyframeStore>;
