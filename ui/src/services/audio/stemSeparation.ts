/**
 * Audio Stem Separation Service
 *
 * Frontend service for calling the Demucs-based stem separation backend.
 *
 * Attribution:
 * - filliptm's ComfyUI_Fill-Nodes: https://github.com/filliptm/ComfyUI_Fill-Nodes
 * - Facebook Research's Demucs: https://github.com/facebookresearch/demucs
 *
 * @module services/audio/stemSeparation
 */

// ============================================================================
// Types
// ============================================================================

/**
 * Available stem types from Demucs separation
 */
export type StemType = 'vocals' | 'drums' | 'bass' | 'other' | 'guitar' | 'piano';

/**
 * Demucs model variants
 */
export type DemucsModel = 'htdemucs' | 'htdemucs_ft' | 'htdemucs_6s' | 'mdx_extra';

/**
 * Model information from backend
 */
export interface StemModel {
  id: DemucsModel;
  name: string;
  description: string;
  stems: StemType[];
  sample_rate: number;
  recommended: boolean;
}

/**
 * Separated stems result
 */
export interface StemSeparationResult {
  status: 'success' | 'error';
  message?: string;
  stems?: Record<StemType, string>; // stem name -> base64 WAV
  available_stems?: StemType[];
  sample_rate?: number;
  duration?: number;
  model?: string;
  attribution?: Record<string, unknown>;
}

/**
 * Stem isolation result (single stem + everything else)
 */
export interface StemIsolationResult {
  status: 'success' | 'error';
  message?: string;
  isolated?: string; // base64 WAV of isolated stem
  removed?: string;  // base64 WAV of everything else mixed
  stem?: StemType;
  sample_rate?: number;
  duration?: number;
  model?: string;
}

/**
 * Progress callback
 */
export type StemProgressCallback = (progress: number, message: string) => void;

// ============================================================================
// API Communication
// ============================================================================

const API_BASE = '/weyl/audio/stems';

/**
 * Get available stem separation models
 */
export async function getStemModels(): Promise<StemModel[]> {
  try {
    const response = await fetch(`${API_BASE}/models`);
    const data = await response.json();

    if (data.status === 'success') {
      return data.models;
    }

    console.warn('Failed to get stem models:', data.message);
    return getDefaultModels();
  } catch (error) {
    console.warn('Stem separation backend not available:', error);
    return getDefaultModels();
  }
}

/**
 * Default models when backend is unavailable
 */
function getDefaultModels(): StemModel[] {
  return [
    {
      id: 'htdemucs',
      name: 'HT-Demucs',
      description: 'Hybrid Transformer Demucs - Best quality, slower',
      stems: ['drums', 'bass', 'other', 'vocals'],
      sample_rate: 44100,
      recommended: true
    },
    {
      id: 'htdemucs_ft',
      name: 'HT-Demucs Fine-tuned',
      description: 'Fine-tuned on MusDB-HQ - Highest quality',
      stems: ['drums', 'bass', 'other', 'vocals'],
      sample_rate: 44100,
      recommended: false
    },
    {
      id: 'mdx_extra',
      name: 'MDX Extra',
      description: 'Fast and accurate - Good balance',
      stems: ['drums', 'bass', 'other', 'vocals'],
      sample_rate: 44100,
      recommended: false
    }
  ];
}

/**
 * Separate audio into individual stems
 *
 * @param audioData - Audio file as ArrayBuffer, Blob, or base64 string
 * @param options - Separation options
 * @returns Separated stems as base64 WAV strings
 *
 * @example
 * ```typescript
 * const result = await separateStems(audioBuffer, {
 *   model: 'htdemucs',
 *   stems: ['vocals', 'drums']
 * });
 *
 * if (result.status === 'success') {
 *   const vocalsBlob = base64ToBlob(result.stems.vocals, 'audio/wav');
 *   const drumsBlob = base64ToBlob(result.stems.drums, 'audio/wav');
 * }
 * ```
 */
export async function separateStems(
  audioData: ArrayBuffer | Blob | string,
  options: {
    model?: DemucsModel;
    stems?: StemType[];
  } = {}
): Promise<StemSeparationResult> {
  try {
    // Convert audio to base64
    let audioBase64: string;

    if (typeof audioData === 'string') {
      // Already base64
      audioBase64 = audioData.includes(',') ? audioData.split(',')[1] : audioData;
    } else if (audioData instanceof Blob) {
      audioBase64 = await blobToBase64(audioData);
    } else {
      // ArrayBuffer
      audioBase64 = arrayBufferToBase64(audioData);
    }

    const response = await fetch(`${API_BASE}/separate`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        audio: audioBase64,
        model: options.model || 'htdemucs',
        stems: options.stems
      })
    });

    const result = await response.json();

    if (!response.ok) {
      return {
        status: 'error',
        message: result.message || `HTTP ${response.status}`
      };
    }

    return result;
  } catch (error) {
    console.error('Stem separation failed:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error'
    };
  }
}

/**
 * Isolate a single stem from audio
 *
 * Returns both the isolated stem and everything else mixed together.
 * Useful for karaoke (remove vocals) or drum practice (isolate drums).
 *
 * @param audioData - Audio file
 * @param stem - Stem to isolate
 * @param model - Demucs model to use
 * @returns Isolated stem and "removed" mix
 *
 * @example
 * ```typescript
 * // Remove vocals for karaoke
 * const result = await isolateStem(audioBuffer, 'vocals');
 * if (result.status === 'success') {
 *   // result.isolated = vocals only
 *   // result.removed = instrumental (drums + bass + other)
 *   playAudio(result.removed); // Karaoke track
 * }
 * ```
 */
export async function isolateStem(
  audioData: ArrayBuffer | Blob | string,
  stem: StemType,
  model: DemucsModel = 'htdemucs'
): Promise<StemIsolationResult> {
  try {
    let audioBase64: string;

    if (typeof audioData === 'string') {
      audioBase64 = audioData.includes(',') ? audioData.split(',')[1] : audioData;
    } else if (audioData instanceof Blob) {
      audioBase64 = await blobToBase64(audioData);
    } else {
      audioBase64 = arrayBufferToBase64(audioData);
    }

    const response = await fetch(`${API_BASE}/isolate`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        audio: audioBase64,
        stem,
        model
      })
    });

    const result = await response.json();

    if (!response.ok) {
      return {
        status: 'error',
        message: result.message || `HTTP ${response.status}`
      };
    }

    return result;
  } catch (error) {
    console.error('Stem isolation failed:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error'
    };
  }
}

// ============================================================================
// Audio Reactive Integration
// ============================================================================

/**
 * Separate stems and create audio buffers for audio reactivity
 *
 * This integrates with the Weyl audio reactivity system, allowing
 * different stems to drive different properties.
 *
 * @example
 * ```typescript
 * const stems = await separateStemsForReactivity(audioFile);
 *
 * // Use drums for scale pulse
 * audioStore.setAudioSource('drums', stems.drums);
 * audioStore.addMapping({
 *   sourceFeature: 'amplitude',
 *   sourceAudioId: 'drums',
 *   targetPropertyPath: 'transform.scale.x',
 *   ...
 * });
 *
 * // Use bass for color shift
 * audioStore.setAudioSource('bass', stems.bass);
 * audioStore.addMapping({
 *   sourceFeature: 'bass',
 *   sourceAudioId: 'bass',
 *   targetPropertyPath: 'layer.hue',
 *   ...
 * });
 * ```
 */
export async function separateStemsForReactivity(
  audioData: ArrayBuffer | Blob | string,
  audioContext: AudioContext,
  model: DemucsModel = 'htdemucs'
): Promise<Record<StemType, AudioBuffer> | null> {
  const result = await separateStems(audioData, { model });

  if (result.status !== 'success' || !result.stems) {
    console.error('Failed to separate stems:', result.message);
    return null;
  }

  const audioBuffers: Record<string, AudioBuffer> = {};

  for (const [stemName, stemBase64] of Object.entries(result.stems)) {
    try {
      const audioBytes = base64ToArrayBuffer(stemBase64);
      const audioBuffer = await audioContext.decodeAudioData(audioBytes);
      audioBuffers[stemName] = audioBuffer;
    } catch (error) {
      console.error(`Failed to decode ${stemName} stem:`, error);
    }
  }

  return audioBuffers as Record<StemType, AudioBuffer>;
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Convert ArrayBuffer to base64 string
 */
function arrayBufferToBase64(buffer: ArrayBuffer): string {
  const bytes = new Uint8Array(buffer);
  let binary = '';
  for (let i = 0; i < bytes.byteLength; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

/**
 * Convert base64 string to ArrayBuffer
 */
function base64ToArrayBuffer(base64: string): ArrayBuffer {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes.buffer;
}

/**
 * Convert Blob to base64 string
 */
async function blobToBase64(blob: Blob): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onloadend = () => {
      const result = reader.result as string;
      // Remove data URL prefix
      const base64 = result.split(',')[1];
      resolve(base64);
    };
    reader.onerror = reject;
    reader.readAsDataURL(blob);
  });
}

/**
 * Convert base64 string to Blob
 */
export function base64ToBlob(base64: string, mimeType: string = 'audio/wav'): Blob {
  const bytes = base64ToArrayBuffer(base64);
  return new Blob([bytes], { type: mimeType });
}

/**
 * Create a download link for a stem
 */
export function downloadStem(base64: string, filename: string): void {
  const blob = base64ToBlob(base64, 'audio/wav');
  const url = URL.createObjectURL(blob);

  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  a.click();

  URL.revokeObjectURL(url);
}

/**
 * Create an audio element for playback
 */
export function createAudioElement(base64: string): HTMLAudioElement {
  const blob = base64ToBlob(base64, 'audio/wav');
  const url = URL.createObjectURL(blob);

  const audio = new Audio(url);

  // Clean up URL when audio is loaded
  audio.addEventListener('loadeddata', () => {
    URL.revokeObjectURL(url);
  }, { once: true });

  return audio;
}

// ============================================================================
// Presets for Common Use Cases
// ============================================================================

/**
 * Preset configurations for common stem separation tasks
 */
export const STEM_PRESETS = {
  /**
   * Karaoke mode - remove vocals, keep instrumental
   */
  karaoke: {
    description: 'Remove vocals for karaoke',
    stem: 'vocals' as StemType,
    useRemoved: true, // Use the "removed" output (instrumental)
  },

  /**
   * Vocal isolation - extract vocals only
   */
  vocals: {
    description: 'Extract vocals only',
    stem: 'vocals' as StemType,
    useRemoved: false,
  },

  /**
   * Drum isolation - for drum practice or analysis
   */
  drums: {
    description: 'Extract drums for practice',
    stem: 'drums' as StemType,
    useRemoved: false,
  },

  /**
   * Bass isolation - for bass practice or mixing
   */
  bass: {
    description: 'Extract bass for practice',
    stem: 'bass' as StemType,
    useRemoved: false,
  },

  /**
   * Accompaniment - everything except melody instruments
   */
  accompaniment: {
    description: 'Keep drums and bass only',
    stems: ['drums', 'bass'] as StemType[],
  },
} as const;

/**
 * Check if stem separation backend is available
 */
export async function isStemSeparationAvailable(): Promise<boolean> {
  try {
    const response = await fetch(`${API_BASE}/models`, {
      method: 'GET',
      signal: AbortSignal.timeout(3000) // 3 second timeout
    });
    return response.ok;
  } catch {
    return false;
  }
}
