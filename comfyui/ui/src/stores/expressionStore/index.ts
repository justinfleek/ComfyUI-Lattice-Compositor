/**
 * Expression Store
 *
 * Domain store for expressions and property drivers.
 *
 * MODULE STRUCTURE:
 * - types.ts: Type definitions and interfaces
 * - expressions.ts: Expression CRUD (delegates to keyframeStore)
 * - drivers.ts: Property driver operations
 *
 * NOTE: Expressions are stored on keyframe data (in keyframeStore).
 * Property drivers are stored in this store's state (propertyDrivers).
 * Property driver system instance is also stored here (propertyDriverSystem).
 */

import { defineStore } from "pinia";
import type { PropertyExpression } from "@/types/animation";
import type { PropertyDriver, PropertyPath } from "@/services/propertyDriver";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                        // module // imports
// ═══════════════════════════════════════════════════════════════════════════

// Types (re-export for consumers)
export type { ExpressionStoreAccess, ExpressionState } from "./types";

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
  canBakeExpression as canBakeExpressionImpl,
  convertExpressionToKeyframes as convertExpressionToKeyframesImpl,
} from "./expressions";

// Driver operations
import {
  initializePropertyDriverSystem as initializePropertyDriverSystemImpl,
  getEvaluatedLayerProperties as getEvaluatedLayerPropertiesImpl,
  addPropertyDriver as addPropertyDriverImpl,
  createAudioPropertyDriver as createAudioPropertyDriverImpl,
  createPropertyLinkDriver as createPropertyLinkDriverImpl,
  removePropertyDriver as removePropertyDriverImpl,
  updatePropertyDriver as updatePropertyDriverImpl,
  getDriversForLayer as getDriversForLayerImpl,
  togglePropertyDriver as togglePropertyDriverImpl,
} from "./drivers";

// Types for internal use
import type { ExpressionStoreAccess, ExpressionState } from "./types";

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // store // definition
// ═══════════════════════════════════════════════════════════════════════════

export const useExpressionStore = defineStore("expression", {
  state: (): ExpressionState => ({
    propertyDriverSystem: null,
    propertyDrivers: [],
  }),

  actions: {
    // ═══════════════════════════════════════════════════════════════════════════
    //                                                       // expression // crud
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Set a property expression
     */
    setPropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
      expression: PropertyExpression,
    ): boolean {
      return setPropertyExpressionImpl(store, layerId, propertyPath, expression);
    },

    /**
     * Enable expression on a property
     */
    enablePropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
      expressionName: string = "custom",
      params: Record<string, number | string | boolean> = {},
    ): boolean {
      return enablePropertyExpressionImpl(
        store,
        layerId,
        propertyPath,
        expressionName,
        params,
      );
    },

    /**
     * Disable expression on a property
     */
    disablePropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return disablePropertyExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Toggle expression enabled state
     */
    togglePropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return togglePropertyExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Remove expression from property
     */
    removePropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return removePropertyExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Get expression for a property
     */
    getPropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): PropertyExpression | undefined {
      return getPropertyExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Check if property has an expression
     */
    hasPropertyExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return hasPropertyExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Update expression parameters
     */
    updateExpressionParams(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
      params: Record<string, number | string | boolean>,
    ): boolean {
      return updateExpressionParamsImpl(store, layerId, propertyPath, params);
    },

    /**
     * Check if a property has a bakeable expression
     */
    canBakeExpression(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
    ): boolean {
      return canBakeExpressionImpl(store, layerId, propertyPath);
    },

    /**
     * Convert expression to keyframes (bake expression)
     * Cross-domain: calls keyframeStore to create keyframes
     */
    convertExpressionToKeyframes(
      store: ExpressionStoreAccess,
      layerId: string,
      propertyPath: string,
      startFrame?: number,
      endFrame?: number,
      sampleRate?: number,
    ): number {
      return convertExpressionToKeyframesImpl(
        store,
        layerId,
        propertyPath,
        startFrame,
        endFrame,
        sampleRate,
      );
    },

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                      // property // drivers
    // ═══════════════════════════════════════════════════════════════════════════

    /**
     * Initialize the property driver system
     */
    initializePropertyDriverSystem(store: ExpressionStoreAccess): void {
      initializePropertyDriverSystemImpl(store);
    },

    /**
     * Get evaluated property values for a layer with drivers applied
     */
    getEvaluatedLayerProperties(
      store: ExpressionStoreAccess,
      layerId: string,
      frame: number,
    ): Map<PropertyPath, number> {
      return getEvaluatedLayerPropertiesImpl(store, layerId, frame);
    },

    /**
     * Add a property driver
     * Returns false if adding would create a circular dependency
     */
    addPropertyDriver(
      store: ExpressionStoreAccess,
      driver: PropertyDriver,
    ): boolean {
      return addPropertyDriverImpl(store, driver);
    },

    /**
     * Create and add an audio-driven property driver
     */
    createAudioPropertyDriver(
      store: ExpressionStoreAccess,
      targetLayerId: string,
      targetProperty: PropertyPath,
      audioFeature: "amplitude" | "bass" | "mid" | "high" | "rms",
      options: {
        threshold?: number;
        scale?: number;
        offset?: number;
        smoothing?: number;
      } = {},
    ): PropertyDriver {
      return createAudioPropertyDriverImpl(
        store,
        targetLayerId,
        targetProperty,
        audioFeature,
        options,
      );
    },

    /**
     * Create and add a property-to-property link
     * Returns null if creating would cause a circular dependency
     */
    createPropertyLinkDriver(
      store: ExpressionStoreAccess,
      targetLayerId: string,
      targetProperty: PropertyPath,
      sourceLayerId: string,
      sourceProperty: PropertyPath,
      options: {
        scale?: number;
        offset?: number;
        blendMode?: "replace" | "add" | "multiply";
      } = {},
    ): PropertyDriver | null {
      return createPropertyLinkDriverImpl(
        store,
        targetLayerId,
        targetProperty,
        sourceLayerId,
        sourceProperty,
        options,
      );
    },

    /**
     * Remove a property driver
     */
    removePropertyDriver(store: ExpressionStoreAccess, driverId: string): void {
      removePropertyDriverImpl(store, driverId);
    },

    /**
     * Update a property driver
     */
    updatePropertyDriver(
      store: ExpressionStoreAccess,
      driverId: string,
      updates: Partial<PropertyDriver>,
    ): void {
      updatePropertyDriverImpl(store, driverId, updates);
    },

    /**
     * Get all drivers for a layer
     */
    getDriversForLayer(
      store: ExpressionStoreAccess,
      layerId: string,
    ): PropertyDriver[] {
      return getDriversForLayerImpl(store, layerId);
    },

    /**
     * Toggle driver enabled state
     */
    togglePropertyDriver(
      store: ExpressionStoreAccess,
      driverId: string,
    ): void {
      togglePropertyDriverImpl(store, driverId);
    },
  },
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // type // exports
// ═══════════════════════════════════════════════════════════════════════════

export type ExpressionStoreType = ReturnType<typeof useExpressionStore>;
