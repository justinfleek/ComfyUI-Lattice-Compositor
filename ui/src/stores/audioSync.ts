/**
 * Audio State Synchronization
 *
 * PROBLEM: Audio state exists in BOTH compositorStore AND audioStore.
 * This creates potential for state drift where one is updated but not the other.
 *
 * SOLUTION: This module establishes audioStore as the SOURCE OF TRUTH for:
 * - audioBuffer
 * - audioFile
 * - audioAnalysis
 *
 * compositorStore still owns:
 * - audioMappings (for project persistence)
 *
 * This sync function copies state FROM audioStore TO compositorStore
 * and should be called after any audio operation.
 */

import type { AudioAnalysis } from "@/services/audioFeatures";
import { useAudioStore } from "./audioStore";

/**
 * Interface for the target store that receives synced audio state.
 * This allows testing without full Pinia context.
 */
export interface AudioSyncTarget {
  audioBuffer: AudioBuffer | null;
  audioFile: File | null;
  audioAnalysis: AudioAnalysis | null;
  audioLoadingState: "idle" | "decoding" | "analyzing" | "complete" | "error";
  audioLoadingProgress: number;
  audioLoadingPhase: string;
  audioLoadingError: string | null;
}

/**
 * Sync audio state from audioStore to compositorStore.
 * Call this after any audio operation in audioStore.
 *
 * @param target - The target store to sync to (usually compositorStore)
 * @param source - Optional source store (defaults to audioStore via Pinia)
 */
export function syncAudioState(
  target: AudioSyncTarget,
  source?: {
    audioBuffer: AudioBuffer | null;
    audioFile: File | null;
    audioAnalysis: AudioAnalysis | null;
    loadingState: "idle" | "decoding" | "analyzing" | "complete" | "error";
    loadingProgress: number;
    loadingPhase: string;
    loadingError: string | null;
  },
): void {
  // If no source provided, get from audioStore (requires Pinia context)
  const audioSource = source ?? useAudioStore();

  target.audioBuffer = audioSource.audioBuffer;
  target.audioFile = audioSource.audioFile;
  target.audioAnalysis = audioSource.audioAnalysis;
  target.audioLoadingState = audioSource.loadingState;
  target.audioLoadingProgress = audioSource.loadingProgress;
  target.audioLoadingPhase = audioSource.loadingPhase;
  target.audioLoadingError = audioSource.loadingError;
}

/**
 * Check if two audio states are in sync.
 * Returns true if they are identical, false if there's drift.
 */
export function checkAudioStateSync(
  a: { audioBuffer: AudioBuffer | null; audioFile: File | null },
  b: { audioBuffer: AudioBuffer | null; audioFile: File | null },
): boolean {
  // Compare by reference for buffers (they should be the same object)
  if (a.audioBuffer !== b.audioBuffer) return false;
  if (a.audioFile !== b.audioFile) return false;
  return true;
}

/**
 * Create a sync validator that can be used in tests.
 * Returns a function that checks if stores are in sync.
 */
export function createSyncValidator(
  storeA: { audioBuffer: AudioBuffer | null; audioFile: File | null },
  storeB: { audioBuffer: AudioBuffer | null; audioFile: File | null },
): () => { inSync: boolean; drift: string[] } {
  return () => {
    const drift: string[] = [];

    if (storeA.audioBuffer !== storeB.audioBuffer) {
      drift.push("audioBuffer");
    }
    if (storeA.audioFile !== storeB.audioFile) {
      drift.push("audioFile");
    }

    return {
      inSync: drift.length === 0,
      drift,
    };
  };
}
