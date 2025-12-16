/**
 * Audio Worker Client
 *
 * Main thread interface for the audio analysis Web Worker.
 * Handles worker lifecycle, message passing, and progress callbacks.
 */
import type { AudioAnalysis } from './audioFeatures';

// ============================================================================
// Types
// ============================================================================

export interface AudioAnalysisProgress {
  phase: 'decoding' | 'amplitude' | 'rms' | 'frequency' | 'spectral' | 'onsets' | 'bpm';
  progress: number;  // 0-1
  message: string;
}

export interface AnalyzeOptions {
  onProgress?: (progress: AudioAnalysisProgress) => void;
}

// Worker message types
interface ProgressMessage {
  type: 'progress';
  payload: {
    phase: string;
    progress: number;
    message: string;
  };
}

interface CompleteMessage {
  type: 'complete';
  payload: AudioAnalysis;
}

interface ErrorMessage {
  type: 'error';
  payload: { message: string };
}

type WorkerResponse = ProgressMessage | CompleteMessage | ErrorMessage;

// ============================================================================
// Worker Client
// ============================================================================

let worker: Worker | null = null;
let currentResolve: ((analysis: AudioAnalysis) => void) | null = null;
let currentReject: ((error: Error) => void) | null = null;
let currentOnProgress: ((progress: AudioAnalysisProgress) => void) | null = null;

/**
 * Initialize the worker if not already running
 */
function ensureWorker(): Worker {
  if (!worker) {
    // Create worker from the audioWorker.ts file
    // Vite handles the worker bundling with this syntax
    worker = new Worker(
      new URL('../workers/audioWorker.ts', import.meta.url),
      { type: 'module' }
    );

    worker.onmessage = (event: MessageEvent<WorkerResponse>) => {
      const message = event.data;

      switch (message.type) {
        case 'progress':
          if (currentOnProgress) {
            currentOnProgress({
              phase: message.payload.phase as AudioAnalysisProgress['phase'],
              progress: message.payload.progress,
              message: message.payload.message
            });
          }
          break;

        case 'complete':
          if (currentResolve) {
            currentResolve(message.payload);
            cleanup();
          }
          break;

        case 'error':
          if (currentReject) {
            currentReject(new Error(message.payload.message));
            cleanup();
          }
          break;
      }
    };

    worker.onerror = (error) => {
      // Use console.error directly as this is in a worker context
      console.error('[AudioWorker] Worker error:', error);
      if (currentReject) {
        currentReject(new Error(`Worker error: ${error.message}`));
        cleanup();
      }
    };
  }

  return worker;
}

/**
 * Clean up after analysis completes or fails
 */
function cleanup() {
  currentResolve = null;
  currentReject = null;
  currentOnProgress = null;
}

/**
 * Terminate the worker (call when no longer needed)
 */
export function terminateWorker(): void {
  if (worker) {
    worker.terminate();
    worker = null;
    cleanup();
  }
}

/**
 * Cancel the current analysis
 */
export function cancelAnalysis(): void {
  if (worker) {
    worker.postMessage({ type: 'cancel' });
  }
}

/**
 * Analyze audio using the Web Worker
 *
 * @param audioBuffer - The decoded AudioBuffer to analyze
 * @param fps - Frames per second for the composition
 * @param options - Optional callbacks for progress reporting
 * @returns Promise that resolves with the analysis results
 */
export async function analyzeAudioInWorker(
  audioBuffer: AudioBuffer,
  fps: number,
  options: AnalyzeOptions = {}
): Promise<AudioAnalysis> {
  const w = ensureWorker();

  // Check if an analysis is already in progress
  if (currentResolve) {
    throw new Error('Analysis already in progress. Cancel it first.');
  }

  // Get channel data (use first channel)
  const channelData = audioBuffer.getChannelData(0);

  // Create a copy for transfer (original buffer stays with AudioBuffer)
  const channelDataCopy = new Float32Array(channelData);

  return new Promise((resolve, reject) => {
    currentResolve = resolve;
    currentReject = reject;
    currentOnProgress = options.onProgress || null;

    // Send to worker with transferable
    w.postMessage(
      {
        type: 'analyze',
        payload: {
          channelData: channelDataCopy,
          sampleRate: audioBuffer.sampleRate,
          fps
        }
      },
      [channelDataCopy.buffer]  // Transfer the buffer for performance
    );
  });
}

/**
 * Load and analyze an audio file in one call
 *
 * @param file - The audio file to load
 * @param fps - Frames per second for the composition
 * @param options - Optional callbacks for progress reporting
 * @returns Promise with both the AudioBuffer and analysis
 */
export async function loadAndAnalyzeAudio(
  file: File,
  fps: number,
  options: AnalyzeOptions = {}
): Promise<{ buffer: AudioBuffer; analysis: AudioAnalysis }> {
  // Report decoding progress
  if (options.onProgress) {
    options.onProgress({
      phase: 'decoding',
      progress: 0,
      message: 'Decoding audio file...'
    });
  }

  // Decode audio on main thread (this is fast, uses native decoder)
  const arrayBuffer = await file.arrayBuffer();
  const audioContext = new AudioContext();

  let buffer: AudioBuffer;
  try {
    buffer = await audioContext.decodeAudioData(arrayBuffer);
  } finally {
    await audioContext.close();
  }

  if (options.onProgress) {
    options.onProgress({
      phase: 'decoding',
      progress: 1,
      message: 'Audio decoded successfully'
    });
  }

  // Analyze in worker
  const analysis = await analyzeAudioInWorker(buffer, fps, options);

  return { buffer, analysis };
}

export default {
  analyzeAudioInWorker,
  loadAndAnalyzeAudio,
  cancelAnalysis,
  terminateWorker
};
