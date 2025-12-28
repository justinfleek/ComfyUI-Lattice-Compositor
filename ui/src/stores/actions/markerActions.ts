/**
 * Marker Actions
 *
 * Timeline marker management: add, remove, update, and query markers.
 * Markers are visual indicators on the timeline used for navigation,
 * beat synchronization, and annotation.
 */

import { storeLogger } from '@/utils/logger';
import type { Marker, Composition } from '@/types/project';

/**
 * Compare two frame values safely, handling NaN
 */
function framesEqual(a: number, b: number): boolean {
  if (!Number.isFinite(a) || !Number.isFinite(b)) return false;
  return a === b;
}

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface MarkerStore {
  project: {
    compositions: Record<string, Composition>;
    meta: { modified: string };
  };
  activeCompositionId: string;
  getActiveComp(): Composition | null;
  pushHistory(): void;
}

// ============================================================================
// MARKER CRUD OPERATIONS
// ============================================================================

/**
 * Add a marker to the active composition
 * @param store - The compositor store
 * @param marker - Marker data (frame, label, color required; id auto-generated if not provided)
 * @returns The created marker or null if failed
 */
export function addMarker(
  store: MarkerStore,
  marker: Omit<Marker, 'id'> & { id?: string }
): Marker | null {
  const comp = store.getActiveComp();
  if (!comp) {
    storeLogger.warn('addMarker: No active composition');
    return null;
  }

  // Initialize markers array if needed
  if (!comp.markers) {
    comp.markers = [];
  }

  // Generate ID if not provided
  const newMarker: Marker = {
    id: marker.id || `marker_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    frame: marker.frame,
    label: marker.label,
    color: marker.color,
    duration: marker.duration,
    comment: marker.comment
  };

  // Check for existing marker at same frame (use framesEqual to handle NaN)
  const existingIndex = comp.markers.findIndex(m => framesEqual(m.frame, marker.frame));
  if (existingIndex >= 0) {
    // Replace existing marker at same frame
    comp.markers[existingIndex] = newMarker;
    storeLogger.debug('addMarker: Replaced marker at frame', marker.frame);
  } else {
    // Add new marker and sort by frame
    comp.markers.push(newMarker);
    comp.markers.sort((a, b) => a.frame - b.frame);
    storeLogger.debug('addMarker: Added marker at frame', marker.frame);
  }

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  return newMarker;
}

/**
 * Remove a marker by ID
 */
export function removeMarker(store: MarkerStore, markerId: string): boolean {
  const comp = store.getActiveComp();
  if (!comp?.markers) return false;

  const index = comp.markers.findIndex(m => m.id === markerId);
  if (index < 0) return false;

  comp.markers.splice(index, 1);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug('removeMarker: Removed marker', markerId);
  return true;
}

/**
 * Remove a marker at a specific frame
 */
export function removeMarkerAtFrame(store: MarkerStore, frame: number): boolean {
  const comp = store.getActiveComp();
  if (!comp?.markers) return false;

  const index = comp.markers.findIndex(m => framesEqual(m.frame, frame));
  if (index < 0) return false;

  comp.markers.splice(index, 1);
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug('removeMarkerAtFrame: Removed marker at frame', frame);
  return true;
}

/**
 * Update a marker's properties
 */
export function updateMarker(
  store: MarkerStore,
  markerId: string,
  updates: Partial<Omit<Marker, 'id'>>
): boolean {
  const comp = store.getActiveComp();
  if (!comp?.markers) return false;

  const marker = comp.markers.find(m => m.id === markerId);
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

  storeLogger.debug('updateMarker: Updated marker', markerId);
  return true;
}

/**
 * Clear all markers from the active composition
 */
export function clearMarkers(store: MarkerStore): void {
  const comp = store.getActiveComp();
  if (!comp) return;

  comp.markers = [];
  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug('clearMarkers: Cleared all markers');
}

// ============================================================================
// MARKER QUERIES
// ============================================================================

/**
 * Get all markers from the active composition
 */
export function getMarkers(store: MarkerStore): Marker[] {
  const comp = store.getActiveComp();
  return comp?.markers || [];
}

/**
 * Get a marker by ID
 */
export function getMarker(store: MarkerStore, markerId: string): Marker | null {
  const comp = store.getActiveComp();
  return comp?.markers?.find(m => m.id === markerId) || null;
}

/**
 * Get marker at a specific frame
 */
export function getMarkerAtFrame(store: MarkerStore, frame: number): Marker | null {
  const comp = store.getActiveComp();
  return comp?.markers?.find(m => m.frame === frame) || null;
}

/**
 * Get markers within a frame range
 */
export function getMarkersInRange(
  store: MarkerStore,
  startFrame: number,
  endFrame: number
): Marker[] {
  const comp = store.getActiveComp();
  if (!comp?.markers) return [];

  return comp.markers.filter(m => m.frame >= startFrame && m.frame <= endFrame);
}

/**
 * Get the next marker after a given frame
 */
export function getNextMarker(store: MarkerStore, frame: number): Marker | null {
  const comp = store.getActiveComp();
  if (!comp?.markers) return null;

  return comp.markers.find(m => m.frame > frame) || null;
}

/**
 * Get the previous marker before a given frame
 */
export function getPreviousMarker(store: MarkerStore, frame: number): Marker | null {
  const comp = store.getActiveComp();
  if (!comp?.markers) return null;

  // Find all markers before the frame and return the last one
  const previousMarkers = comp.markers.filter(m => m.frame < frame);
  return previousMarkers.length > 0 ? previousMarkers[previousMarkers.length - 1] : null;
}

// ============================================================================
// MARKER NAVIGATION
// ============================================================================

/**
 * Jump to the next marker
 * @returns The frame number of the next marker, or null if none
 */
export function jumpToNextMarker(store: MarkerStore, currentFrame: number): number | null {
  const nextMarker = getNextMarker(store, currentFrame);
  return nextMarker?.frame ?? null;
}

/**
 * Jump to the previous marker
 * @returns The frame number of the previous marker, or null if none
 */
export function jumpToPreviousMarker(store: MarkerStore, currentFrame: number): number | null {
  const prevMarker = getPreviousMarker(store, currentFrame);
  return prevMarker?.frame ?? null;
}

// ============================================================================
// BATCH MARKER OPERATIONS
// ============================================================================

/**
 * Add multiple markers at once (e.g., from beat detection)
 */
export function addMarkers(
  store: MarkerStore,
  markers: Array<Omit<Marker, 'id'>>
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
      comment: markerData.comment
    };

    // Check for existing marker at same frame (use framesEqual to handle NaN)
    const existingIndex = comp.markers.findIndex(m => framesEqual(m.frame, markerData.frame));
    if (existingIndex >= 0) {
      comp.markers[existingIndex] = newMarker;
    } else {
      comp.markers.push(newMarker);
    }

    newMarkers.push(newMarker);
  }

  // Sort all markers by frame
  comp.markers.sort((a, b) => a.frame - b.frame);

  store.project.meta.modified = new Date().toISOString();
  store.pushHistory();

  storeLogger.debug('addMarkers: Added', newMarkers.length, 'markers');
  return newMarkers;
}

/**
 * Remove markers by color (useful for removing all beat markers)
 */
export function removeMarkersByColor(store: MarkerStore, color: string): number {
  const comp = store.getActiveComp();
  if (!comp?.markers) return 0;

  const originalLength = comp.markers.length;
  comp.markers = comp.markers.filter(m => m.color !== color);
  const removedCount = originalLength - comp.markers.length;

  if (removedCount > 0) {
    store.project.meta.modified = new Date().toISOString();
    store.pushHistory();
    storeLogger.debug('removeMarkersByColor: Removed', removedCount, 'markers with color', color);
  }

  return removedCount;
}
