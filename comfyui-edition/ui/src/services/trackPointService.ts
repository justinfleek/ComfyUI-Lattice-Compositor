/**
 * Track Point Service
 *
 * Provides 2D track point management for camera tracking workflows.
 * This service handles manual track point creation, editing, and visualization.
 *
 * For automatic tracking, external tools like COLMAP, OpenSfM, or Blender
 * should be used and the results imported via cameraTrackingImport.ts
 */

import { computed, reactive } from "vue";
import { isNonEmptyString } from "@/utils/typeGuards";
import type {
  GroundPlane,
  TrackPoint2D,
  TrackPoint3D,
} from "@/types/cameraTracking";

/**
 * A track that follows a point across multiple frames
 */
export interface Track {
  /** Unique identifier */
  id: string;

  /** Human-readable name */
  name: string;

  /** Track color for visualization */
  color: string;

  /** 2D positions per frame (keyed by frame number) */
  positions: Map<number, { x: number; y: number; confidence: number }>;

  /** 3D position if solved (null until camera solve) */
  position3D: { x: number; y: number; z: number } | null;

  /** Whether this track is selected */
  selected: boolean;

  /** Whether this track is locked (no editing) */
  locked: boolean;

  /** Track type */
  type: "feature" | "manual" | "imported";
}

/**
 * Track point manager state
 */
interface TrackPointState {
  tracks: Map<string, Track>;
  selectedTrackIds: Set<string>;
  activeTrackId: string | null;
  groundPlane: GroundPlane | null;
  origin3D: { x: number; y: number; z: number } | null;
}

// Reactive state
const state = reactive<TrackPointState>({
  tracks: new Map(),
  selectedTrackIds: new Set(),
  activeTrackId: null,
  groundPlane: null,
  origin3D: null,
});

// Computed properties
const tracks = computed(() => Array.from(state.tracks.values()));
const selectedTracks = computed(() =>
  tracks.value.filter((t) => state.selectedTrackIds.has(t.id)),
);
const activeTrack = computed(() =>
  state.activeTrackId ? state.tracks.get(state.activeTrackId) : null,
);

/**
 * Generate a unique track ID
 */
function generateTrackId(): string {
  return `track_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;
}

/**
 * Generate a random color for new tracks
 */
function generateTrackColor(): string {
  const colors = [
    "#FF6B6B",
    "#4ECDC4",
    "#45B7D1",
    "#96CEB4",
    "#FFEAA7",
    "#DDA0DD",
    "#98D8C8",
    "#F7DC6F",
    "#BB8FCE",
    "#85C1E9",
  ];
  return colors[Math.floor(Math.random() * colors.length)];
}

/**
 * Create a new track
 */
export function createTrack(
  options: {
    name?: string;
    color?: string;
    type?: "feature" | "manual" | "imported";
  } = {},
): Track {
  // Type proof: name ∈ string | undefined → string
  const name = isNonEmptyString(options.name)
    ? options.name
    : `Track ${state.tracks.size + 1}`;
  // Type proof: color ∈ string | undefined → string
  const color = isNonEmptyString(options.color)
    ? options.color
    : generateTrackColor();
  // Type proof: type ∈ "feature" | "manual" | "imported" | undefined → "feature" | "manual" | "imported"
  const type = typeof options.type === "string" &&
    (options.type === "feature" ||
      options.type === "manual" ||
      options.type === "imported")
    ? options.type
    : "manual";

  const track: Track = {
    id: generateTrackId(),
    name,
    color,
    positions: new Map(),
    position3D: null,
    selected: false,
    locked: false,
    type,
  };

  state.tracks.set(track.id, track);
  return track;
}

/**
 * Delete a track
 */
export function deleteTrack(trackId: string): boolean {
  state.selectedTrackIds.delete(trackId);
  if (state.activeTrackId === trackId) {
    state.activeTrackId = null;
  }
  return state.tracks.delete(trackId);
}

/**
 * Delete selected tracks
 */
export function deleteSelectedTracks(): void {
  for (const trackId of state.selectedTrackIds) {
    state.tracks.delete(trackId);
  }
  state.selectedTrackIds.clear();
  state.activeTrackId = null;
}

/**
 * Set track position at a specific frame
 */
export function setTrackPosition(
  trackId: string,
  frame: number,
  x: number,
  y: number,
  confidence: number = 1.0,
): void {
  const track = state.tracks.get(trackId);
  if (track && !track.locked) {
    track.positions.set(frame, { x, y, confidence });
  }
}

/**
 * Get track position at a specific frame
 * @throws Error if track not found or position not available at frame
 */
export function getTrackPosition(
  trackId: string,
  frame: number,
): { x: number; y: number; confidence: number } {
  const track = state.tracks.get(trackId);
  if (!track) {
    throw new Error(`[TrackPointService] Cannot get track position: Track "${trackId}" not found`);
  }
  const position = track.positions.get(frame);
  if (!position) {
    throw new Error(`[TrackPointService] Cannot get track position: Track "${trackId}" has no position at frame ${frame}`);
  }
  return position;
}

/**
 * Remove track position at a specific frame
 */
export function removeTrackPosition(trackId: string, frame: number): void {
  const track = state.tracks.get(trackId);
  if (track && !track.locked) {
    track.positions.delete(frame);
  }
}

/**
 * Get all positions for a track (for visualization)
 */
export function getTrackPositions(trackId: string): TrackPoint2D[] {
  const track = state.tracks.get(trackId);
  if (!track) return [];

  const points: TrackPoint2D[] = [];
  for (const [frame, pos] of track.positions) {
    points.push({
      id: `${trackId}_${frame}`,
      frame,
      x: pos.x,
      y: pos.y,
      confidence: pos.confidence,
      color: track.color,
    });
  }

  return points.sort((a, b) => a.frame - b.frame);
}

/**
 * Get all track points at a specific frame (for visualization)
 */
export function getPointsAtFrame(frame: number): Array<{
  trackId: string;
  trackName: string;
  x: number;
  y: number;
  confidence: number;
  color: string;
  selected: boolean;
}> {
  const points: Array<{
    trackId: string;
    trackName: string;
    x: number;
    y: number;
    confidence: number;
    color: string;
    selected: boolean;
  }> = [];

  for (const track of state.tracks.values()) {
    const pos = track.positions.get(frame);
    if (pos) {
      points.push({
        trackId: track.id,
        trackName: track.name,
        x: pos.x,
        y: pos.y,
        confidence: pos.confidence,
        color: track.color,
        selected: state.selectedTrackIds.has(track.id),
      });
    }
  }

  return points;
}

/**
 * Select a track
 */
export function selectTrack(trackId: string, additive: boolean = false): void {
  if (!additive) {
    state.selectedTrackIds.clear();
  }
  state.selectedTrackIds.add(trackId);
  state.activeTrackId = trackId;

  const track = state.tracks.get(trackId);
  if (track) {
    track.selected = true;
  }
}

/**
 * Deselect a track
 */
export function deselectTrack(trackId: string): void {
  state.selectedTrackIds.delete(trackId);
  if (state.activeTrackId === trackId) {
    state.activeTrackId = null;
  }

  const track = state.tracks.get(trackId);
  if (track) {
    track.selected = false;
  }
}

/**
 * Clear all track selections
 */
export function clearSelection(): void {
  for (const track of state.tracks.values()) {
    track.selected = false;
  }
  state.selectedTrackIds.clear();
  state.activeTrackId = null;
}

/**
 * Set active track (for editing)
 */
export function setActiveTrack(trackId: string | null): void {
  state.activeTrackId = trackId;
}

/**
 * Lock/unlock a track
 */
export function setTrackLocked(trackId: string, locked: boolean): void {
  const track = state.tracks.get(trackId);
  if (track) {
    track.locked = locked;
  }
}

/**
 * Rename a track
 */
export function renameTrack(trackId: string, name: string): void {
  const track = state.tracks.get(trackId);
  if (track) {
    track.name = name;
  }
}

/**
 * Set track color
 */
export function setTrackColor(trackId: string, color: string): void {
  const track = state.tracks.get(trackId);
  if (track) {
    track.color = color;
  }
}

/**
 * Set ground plane for 3D alignment
 */
export function setGroundPlane(plane: GroundPlane | null): void {
  state.groundPlane = plane;
}

/**
 * Define ground plane from three track points
 */
export function defineGroundPlaneFromPoints(
  trackId1: string,
  trackId2: string,
  trackId3: string,
): GroundPlane {
  const track1 = state.tracks.get(trackId1);
  const track2 = state.tracks.get(trackId2);
  const track3 = state.tracks.get(trackId3);

  if (!track1) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId1}" not found`);
  }
  if (!track2) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId2}" not found`);
  }
  if (!track3) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId3}" not found`);
  }
  if (!track1.position3D) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId1}" has no 3D position`);
  }
  if (!track2.position3D) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId2}" has no 3D position`);
  }
  if (!track3.position3D) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Track "${trackId3}" has no 3D position`);
  }

  const p1 = track1.position3D;
  const p2 = track2.position3D;
  const p3 = track3.position3D;

  // Calculate two edge vectors
  const v1 = { x: p2.x - p1.x, y: p2.y - p1.y, z: p2.z - p1.z };
  const v2 = { x: p3.x - p1.x, y: p3.y - p1.y, z: p3.z - p1.z };

  // Cross product for normal
  const normal = {
    x: v1.y * v2.z - v1.z * v2.y,
    y: v1.z * v2.x - v1.x * v2.z,
    z: v1.x * v2.y - v1.y * v2.x,
  };

  // Normalize
  const len = Math.sqrt(normal.x ** 2 + normal.y ** 2 + normal.z ** 2);
  if (len < 0.0001) {
    throw new Error(`[TrackPointService] Cannot define ground plane: Points from tracks "${trackId1}", "${trackId2}", and "${trackId3}" are collinear (normal vector length: ${len})`);
  }

  normal.x /= len;
  normal.y /= len;
  normal.z /= len;

  const plane: GroundPlane = {
    normal,
    origin: p1,
    up: { x: 0, y: 1, z: 0 }, // Default up, can be adjusted
    scale: 1,
  };

  state.groundPlane = plane;
  return plane;
}

/**
 * Set 3D origin point
 */
export function setOrigin3D(trackId: string): boolean {
  const track = state.tracks.get(trackId);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const trackPosition3D = (track != null && typeof track === "object" && "position3D" in track && track.position3D != null && typeof track.position3D === "object") ? track.position3D : undefined;
  if (trackPosition3D == null) {
    console.warn("Cannot set origin: track must have 3D position");
    return false;
  }

  state.origin3D = { ...trackPosition3D };
  return true;
}

/**
 * Import tracks from TrackPoint2D array (from camera tracking import)
 */
export function importTrackPoints2D(points: TrackPoint2D[]): void {
  // Group points by track ID prefix
  const trackGroups = new Map<string, TrackPoint2D[]>();

  for (const point of points) {
    // Extract base track ID (without frame suffix)
    const trackId = point.id.split("_").slice(0, -1).join("_") || point.id;

    if (!trackGroups.has(trackId)) {
      trackGroups.set(trackId, []);
    }
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const trackGroup = trackGroups.get(trackId);
    if (trackGroup != null && Array.isArray(trackGroup)) {
      trackGroup.push(point);
    }
  }

  // Create tracks from groups
  for (const [baseId, trackPoints] of trackGroups) {
    // Type proof: trackPoints[0]?.color ∈ string | undefined → string
    const firstPointColor = trackPoints.length > 0 &&
      isNonEmptyString(trackPoints[0].color)
      ? trackPoints[0].color
      : generateTrackColor();
    const track = createTrack({
      name: `Imported ${baseId}`,
      type: "imported",
      color: firstPointColor,
    });

    for (const point of trackPoints) {
      track.positions.set(point.frame, {
        x: point.x,
        y: point.y,
        confidence: point.confidence,
      });
    }
  }
}

/**
 * Import 3D track points (from camera tracking import)
 */
export function importTrackPoints3D(points: TrackPoint3D[]): void {
  for (const point of points) {
    const track = createTrack({
      name: point.id,
      type: "imported",
    });

    track.position3D = { ...point.position };
  }
}

/**
 * Clear all tracks
 */
export function clearAllTracks(): void {
  state.tracks.clear();
  state.selectedTrackIds.clear();
  state.activeTrackId = null;
  state.groundPlane = null;
  state.origin3D = null;
}

/**
 * Export tracks to TrackPoint2D array
 */
export function exportTrackPoints2D(): TrackPoint2D[] {
  const points: TrackPoint2D[] = [];

  for (const track of state.tracks.values()) {
    for (const [frame, pos] of track.positions) {
      points.push({
        id: `${track.id}_${frame}`,
        frame,
        x: pos.x,
        y: pos.y,
        confidence: pos.confidence,
        color: track.color,
      });
    }
  }

  return points;
}

/**
 * Get statistics about tracks
 */
export function getTrackStats(): {
  totalTracks: number;
  totalPoints: number;
  tracksWithPositions: number;
  frameRange: { min: number; max: number } | null;
} {
  let totalPoints = 0;
  let tracksWithPositions = 0;
  let minFrame = Infinity;
  let maxFrame = -Infinity;

  for (const track of state.tracks.values()) {
    const pointCount = track.positions.size;
    totalPoints += pointCount;

    if (pointCount > 0) {
      tracksWithPositions++;

      for (const frame of track.positions.keys()) {
        minFrame = Math.min(minFrame, frame);
        maxFrame = Math.max(maxFrame, frame);
      }
    }
  }

  return {
    totalTracks: state.tracks.size,
    totalPoints,
    tracksWithPositions,
    frameRange: minFrame <= maxFrame ? { min: minFrame, max: maxFrame } : null,
  };
}

// Export reactive state for components
export const trackPointState = {
  tracks,
  selectedTracks,
  activeTrack,
  groundPlane: computed(() => state.groundPlane),
  origin3D: computed(() => state.origin3D),
};

// Export for use in composables
export function useTrackPoints() {
  return {
    // State
    ...trackPointState,

    // Track management
    createTrack,
    deleteTrack,
    deleteSelectedTracks,
    renameTrack,
    setTrackColor,
    setTrackLocked,

    // Position management
    setTrackPosition,
    getTrackPosition,
    removeTrackPosition,
    getTrackPositions,
    getPointsAtFrame,

    // Selection
    selectTrack,
    deselectTrack,
    clearSelection,
    setActiveTrack,

    // 3D alignment
    setGroundPlane,
    defineGroundPlaneFromPoints,
    setOrigin3D,

    // Import/export
    importTrackPoints2D,
    importTrackPoints3D,
    exportTrackPoints2D,
    clearAllTracks,

    // Stats
    getTrackStats,
  };
}
