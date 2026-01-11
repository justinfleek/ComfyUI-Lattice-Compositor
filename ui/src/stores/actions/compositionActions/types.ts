/**
 * Composition Actions - Types
 *
 * Store interface for composition actions.
 */

import type { Composition, CompositionSettings } from "@/types/project";

// ============================================================================
// STORE INTERFACE
// ============================================================================

export interface CompositionStore {
  project: {
    compositions: Record<string, Composition>;
    mainCompositionId: string;
    composition: CompositionSettings; // Legacy alias
    meta: { modified: string };
  };
  activeCompositionId: string;
  openCompositionIds: string[];
  compositionBreadcrumbs: string[];
  selectedLayerIds: string[];

  // Methods the actions need to call
  getActiveComp(): Composition | null;
  switchComposition(compId: string): void;
  pushHistory(): void;
}
