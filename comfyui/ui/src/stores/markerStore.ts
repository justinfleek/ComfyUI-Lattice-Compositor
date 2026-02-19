/**
 * Marker Store
 *
 * Domain store for timeline marker management.
 * Markers are visual indicators on the timeline used for navigation,
 * beat synchronization, and annotation.
 *
 * @see docs/MASTER_REFACTOR_PLAN.md
 */

import { defineStore } from "pinia";
import type { Composition, Marker } from "@/types/project";
import { storeLogger } from "@/utils/logger";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                       // helper // functions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Compare two frame values safely, handling NaN.
 * Returns false if either value is not finite.
 */
function framesEqual(a: number, b: number): boolean {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return false;
  return a === b;
}

// ════════════════════════════════════════════════════════════════════════════
//                                      // store // interface // for // actions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Interface for stores that need to access marker operations.
 */
export interface MarkerStoreAccess {
  project: {
    compositions: Record<string, Composition>;
    meta: { modified: string };
  };
  activeCompositionId: string;
  currentFrame: number;
  getActiveComp(): Composition | null;
  setFrame(frame: number): void;
  pushHistory(): void;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                            // pinia // store
// ════════════════════════════════════════════════════════════════════════════

export const useMarkerStore = defineStore("marker", {
  state: () => ({}),

  getters: {},

  actions: {
    // ════════════════════════════════════════════════════════════════════════════
    //                                                                 // crud // o
    // ════════════════════════════════════════════════════════════════════════════

    /**
     * Add a marker to the active composition.
     *
     * @param store - Compositor store access
     * @param marker - Marker data (frame, label, color required; id auto-generated if not provided)
     * @returns The created marker or null if failed
     */
    addMarker(
      store: MarkerStoreAccess,
      marker: Omit<Marker, "id"> & { id?: string },
    ): Marker {
      const comp = store.getActiveComp();
      if (!comp) {
        throw new Error("[MarkerStore] Cannot add marker: No active composition found");
      }

      // Initialize markers array if needed
      if (!comp.markers) {
        comp.markers = [];
      }

      // Generate ID if not provided
      const newMarker: Marker = {
        id:
          marker.id ||
          `marker_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
        frame: marker.frame,
        label: marker.label,
        color: marker.color,
        duration: marker.duration,
        comment: marker.comment,
      };

      // Check for existing marker at same frame
      const existingIndex = comp.markers.findIndex((m) =>
        framesEqual(m.frame, marker.frame),
      );
      if (existingIndex >= 0) {
        comp.markers[existingIndex] = newMarker;
        storeLogger.debug("addMarker: Replaced marker at frame", marker.frame);
      } else {
        comp.markers.push(newMarker);
        comp.markers.sort((a, b) => a.frame - b.frame);
        storeLogger.debug("addMarker: Added marker at frame", marker.frame);
      }

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      return newMarker;
    },

    /**
     * Add multiple markers at once (e.g., from beat detection).
     *
     * @param store - Compositor store access
     * @param markers - Array of marker data
     * @returns Array of created markers
     */
    addMarkers(
      store: MarkerStoreAccess,
      markers: Array<Omit<Marker, "id">>,
    ): Marker[] {
      const comp = store.getActiveComp();
      if (!comp) return [];

      if (!comp.markers) {
        comp.markers = [];
      }

      const newMarkers: Marker[] = [];

      for (const markerData of markers) {
        const newMarker: Marker = {
          id: `marker_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
          frame: markerData.frame,
          label: markerData.label,
          color: markerData.color,
          duration: markerData.duration,
          comment: markerData.comment,
        };

        const existingIndex = comp.markers.findIndex((m) =>
          framesEqual(m.frame, markerData.frame),
        );
        if (existingIndex >= 0) {
          comp.markers[existingIndex] = newMarker;
        } else {
          comp.markers.push(newMarker);
        }

        newMarkers.push(newMarker);
      }

      comp.markers.sort((a, b) => a.frame - b.frame);

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.debug("addMarkers: Added", newMarkers.length, "markers");
      return newMarkers;
    },

    /**
     * Remove a marker by ID.
     *
     * @param store - Compositor store access
     * @param markerId - ID of marker to remove
     * @returns true if marker was removed, false otherwise
     */
    removeMarker(store: MarkerStoreAccess, markerId: string): boolean {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) return false;

      const index = comp.markers.findIndex((m) => m.id === markerId);
      if (index < 0) return false;

      comp.markers.splice(index, 1);
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.debug("removeMarker: Removed marker", markerId);
      return true;
    },

    /**
     * Remove marker at a specific frame.
     *
     * @param store - Compositor store access
     * @param frame - Frame number to remove marker from
     * @returns true if marker was removed, false otherwise
     */
    removeMarkerAtFrame(store: MarkerStoreAccess, frame: number): boolean {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) return false;

      const index = comp.markers.findIndex((m) => framesEqual(m.frame, frame));
      if (index < 0) return false;

      comp.markers.splice(index, 1);
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.debug("removeMarkerAtFrame: Removed marker at frame", frame);
      return true;
    },

    /**
     * Remove all markers with a specific color.
     * Useful for removing all beat markers.
     *
     * @param store - Compositor store access
     * @param color - Color to filter by
     * @returns Number of markers removed
     */
    removeMarkersByColor(store: MarkerStoreAccess, color: string): number {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) return 0;

      const originalLength = comp.markers.length;
      comp.markers = comp.markers.filter((m) => m.color !== color);
      const removedCount = originalLength - comp.markers.length;

      if (removedCount > 0) {
        store.project.meta.modified = new Date().toISOString();
        store.pushHistory();
        storeLogger.debug(
          "removeMarkersByColor: Removed",
          removedCount,
          "markers with color",
          color,
        );
      }

      return removedCount;
    },

    /**
     * Update a marker's properties.
     *
     * @param store - Compositor store access
     * @param markerId - ID of marker to update
     * @param updates - Partial marker properties to update
     * @returns true if marker was updated, false otherwise
     */
    updateMarker(
      store: MarkerStoreAccess,
      markerId: string,
      updates: Partial<Omit<Marker, "id">>,
    ): boolean {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) return false;

      const marker = comp.markers.find((m) => m.id === markerId);
      if (!marker) return false;

      // Apply updates (validate frame to prevent NaN)
      if (updates.frame !== undefined && Number.isFinite(updates.frame)) {
        marker.frame = updates.frame;
      }
      if (updates.label !== undefined) marker.label = updates.label;
      if (updates.color !== undefined) marker.color = updates.color;
      if (updates.duration !== undefined) marker.duration = updates.duration;
      if (updates.comment !== undefined) marker.comment = updates.comment;

      // Re-sort if frame changed
      if (updates.frame !== undefined) {
        comp.markers.sort((a, b) => a.frame - b.frame);
      }

      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.debug("updateMarker: Updated marker", markerId);
      return true;
    },

    /**
     * Clear all markers from the active composition.
     *
     * @param store - Compositor store access
     */
    clearMarkers(store: MarkerStoreAccess): void {
      const comp = store.getActiveComp();
      if (!comp) return;

      comp.markers = [];
      store.project.meta.modified = new Date().toISOString();
      store.pushHistory();

      storeLogger.debug("clearMarkers: Cleared all markers");
    },

    // ════════════════════════════════════════════════════════════════════════════
    // Query Operations
    // ════════════════════════════════════════════════════════════════════════════

    /**
     * Get all markers from the active composition.
     *
     * @param store - Compositor store access
     * @returns Array of markers, sorted by frame
     */
    getMarkers(store: MarkerStoreAccess): Marker[] {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const markers = (comp !== null && comp !== undefined && typeof comp === "object" && "markers" in comp) ? comp.markers : undefined;
      return (markers !== null && markers !== undefined && Array.isArray(markers)) ? markers : [];
    },

    /**
     * Get a marker by ID.
     *
     * @param store - Compositor store access
     * @param markerId - ID of marker to find
     * @returns The marker or null if not found
     */
    getMarker(store: MarkerStoreAccess, markerId: string): Marker | null {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const markers = (comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers)) ? comp.markers : undefined;
      const marker = (markers != null && typeof markers.find === "function") ? markers.find((m) => m.id === markerId) : undefined;
      return marker || null;
    },

    /**
     * Get marker at a specific frame.
     *
     * @param store - Compositor store access
     * @param frame - Frame number to check
     * @returns The marker or null if not found
     */
    getMarkerAtFrame(store: MarkerStoreAccess, frame: number): Marker | null {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const markers = (comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers)) ? comp.markers : undefined;
      const marker = (markers != null && typeof markers.find === "function") ? markers.find((m) => m.frame === frame) : undefined;
      return marker || null;
    },

    /**
     * Get all markers within a frame range.
     *
     * @param store - Compositor store access
     * @param startFrame - Start of range (inclusive)
     * @param endFrame - End of range (inclusive)
     * @returns Array of markers in range
     */
    getMarkersInRange(
      store: MarkerStoreAccess,
      startFrame: number,
      endFrame: number,
    ): Marker[] {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) return [];

      return comp.markers.filter(
        (m) => m.frame >= startFrame && m.frame <= endFrame,
      );
    },

    /**
     * Get the next marker after a given frame.
     *
     * @param store - Compositor store access
     * @param frame - Current frame
     * @returns The next marker or null if none
     */
    getNextMarker(store: MarkerStoreAccess, frame: number): Marker {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) {
        throw new Error("[MarkerStore] Cannot get next marker: No active composition or markers array");
      }

      const marker = comp.markers.find((m) => m.frame > frame);
      if (!marker) {
        throw new Error(`[MarkerStore] No marker found after frame ${frame}`);
      }
      return marker;
    },

    /**
     * Get the previous marker before a given frame.
     *
     * @param store - Compositor store access
     * @param frame - Current frame
     * @returns The previous marker or null if none
     */
    getPreviousMarker(store: MarkerStoreAccess, frame: number): Marker {
      const comp = store.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      if (!comp || !(comp != null && typeof comp === "object" && "markers" in comp && comp.markers != null && Array.isArray(comp.markers))) {
        throw new Error("[MarkerStore] Cannot get previous marker: No active composition or markers array");
      }

      const previousMarkers = comp.markers.filter((m) => m.frame < frame);
      if (previousMarkers.length > 0) {
        return previousMarkers[previousMarkers.length - 1];
      }
      throw new Error(`[MarkerStore] No marker found before frame ${frame}`);
    },

    // ════════════════════════════════════════════════════════════════════════════
    // Navigation Operations
    // ════════════════════════════════════════════════════════════════════════════

    /**
     * Jump to the next marker from current frame.
     * Updates the store's current frame if a marker is found.
     *
     * @param store - Compositor store access
     */
    jumpToNextMarker(store: MarkerStoreAccess): void {
      const nextMarker = this.getNextMarker(store, store.currentFrame);
      if (nextMarker) {
        store.setFrame(nextMarker.frame);
      }
    },

    /**
     * Jump to the previous marker from current frame.
     * Updates the store's current frame if a marker is found.
     *
     * @param store - Compositor store access
     */
    jumpToPreviousMarker(store: MarkerStoreAccess): void {
      const prevMarker = this.getPreviousMarker(store, store.currentFrame);
      if (prevMarker) {
        store.setFrame(prevMarker.frame);
      }
    },
  },
});
