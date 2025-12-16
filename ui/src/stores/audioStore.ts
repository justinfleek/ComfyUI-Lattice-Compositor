/**
 * Audio Store
 *
 * Manages audio state including loading, analysis, and reactive mappings.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from 'pinia';
import { storeLogger } from '@/utils/logger';
import type { AudioAnalysis, PeakData, PeakDetectionConfig } from '@/services/audioFeatures';
import { getFeatureAtFrame, detectPeaks, isBeatAtFrame } from '@/services/audioFeatures';
import { loadAndAnalyzeAudio, cancelAnalysis } from '@/services/audioWorkerClient';
import type { AudioMapping, TargetParameter } from '@/services/audioReactiveMapping';
import { AudioReactiveMapper } from '@/services/audioReactiveMapping';
import type { AudioParticleMapping } from '@/types/project';

interface AudioState {
  // Audio buffer and analysis
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;

  // Loading state
  loadingState: 'idle' | 'decoding' | 'analyzing' | 'complete' | 'error';
  loadingProgress: number;
  loadingPhase: string;
  loadingError: string | null;

  // Peak detection
  peakData: PeakData | null;

  // Legacy audio-particle mappings
  legacyMappings: Map<string, AudioParticleMapping[]>;

  // New audio reactive system
  reactiveMappings: AudioMapping[];
  reactiveMapper: AudioReactiveMapper | null;
}

export const useAudioStore = defineStore('audio', {
  state: (): AudioState => ({
    audioBuffer: null,
    audioAnalysis: null,
    audioFile: null,
    loadingState: 'idle',
    loadingProgress: 0,
    loadingPhase: '',
    loadingError: null,
    peakData: null,
    legacyMappings: new Map(),
    reactiveMappings: [],
    reactiveMapper: null,
  }),

  getters: {
    isLoaded: (state) => state.audioAnalysis !== null,
    isLoading: (state) => state.loadingState === 'decoding' || state.loadingState === 'analyzing',
    hasError: (state) => state.loadingState === 'error',
    duration: (state) => state.audioBuffer?.duration ?? 0,
    bpm: (state) => state.audioAnalysis?.bpm ?? 0,
    frameCount: (state) => state.audioAnalysis?.frameCount ?? 0,
  },

  actions: {
    /**
     * Load audio file using Web Worker (non-blocking)
     */
    async loadAudio(file: File, fps: number): Promise<void> {
      // Reset state
      this.audioFile = file;
      this.audioBuffer = null;
      this.audioAnalysis = null;
      this.loadingState = 'decoding';
      this.loadingProgress = 0;
      this.loadingPhase = 'Preparing...';
      this.loadingError = null;

      try {
        const result = await loadAndAnalyzeAudio(
          file,
          fps,
          {
            onProgress: (progress) => {
              if (progress.phase === 'decoding') {
                this.loadingState = 'decoding';
              } else {
                this.loadingState = 'analyzing';
              }
              this.loadingProgress = progress.progress;
              this.loadingPhase = progress.message;
            }
          }
        );

        this.audioBuffer = result.buffer;
        this.audioAnalysis = result.analysis;
        this.loadingState = 'complete';
        this.loadingProgress = 1;
        this.loadingPhase = 'Complete';

        // Initialize the audio reactive mapper
        this.initializeReactiveMapper();

        storeLogger.debug('Audio loaded:', {
          duration: this.audioBuffer.duration,
          bpm: this.audioAnalysis.bpm,
          frameCount: this.audioAnalysis.frameCount
        });
      } catch (error) {
        storeLogger.error('Failed to load audio:', error);
        this.audioFile = null;
        this.audioBuffer = null;
        this.audioAnalysis = null;
        this.reactiveMapper = null;
        this.loadingState = 'error';
        this.loadingError = (error as Error).message;
      }
    },

    /**
     * Cancel ongoing audio analysis
     */
    cancelLoad(): void {
      cancelAnalysis();
      this.loadingState = 'idle';
      this.loadingProgress = 0;
      this.loadingPhase = '';
      this.loadingError = null;
    },

    /**
     * Clear loaded audio
     */
    clear(): void {
      this.cancelLoad();
      this.audioFile = null;
      this.audioBuffer = null;
      this.audioAnalysis = null;
      this.legacyMappings.clear();
      this.reactiveMappings = [];
      this.reactiveMapper = null;
      this.peakData = null;
    },

    /**
     * Initialize the audio reactive mapper
     */
    initializeReactiveMapper(): void {
      if (!this.audioAnalysis) return;

      this.reactiveMapper = new AudioReactiveMapper(this.audioAnalysis);

      // Re-add any existing mappings
      for (const mapping of this.reactiveMappings) {
        this.reactiveMapper.addMapping(mapping);
      }

      // Re-add peak data if available
      if (this.peakData) {
        this.reactiveMapper.setPeakData(this.peakData);
      }
    },

    /**
     * Get audio feature value at frame
     */
    getFeatureAtFrame(feature: string, frame: number): number {
      if (!this.audioAnalysis) return 0;
      return getFeatureAtFrame(this.audioAnalysis, feature, frame);
    },

    /**
     * Check if frame is on a beat
     */
    isBeatAtFrame(frame: number): boolean {
      if (!this.audioAnalysis) return false;
      return isBeatAtFrame(this.audioAnalysis, frame);
    },

    // ============================================================
    // PEAK DETECTION
    // ============================================================

    /**
     * Set peak data
     */
    setPeakData(peakData: PeakData): void {
      this.peakData = peakData;
      if (this.reactiveMapper) {
        this.reactiveMapper.setPeakData(peakData);
      }
    },

    /**
     * Detect peaks with config
     */
    detectPeaks(config: PeakDetectionConfig): PeakData | null {
      if (!this.audioAnalysis) return null;

      const weights = this.audioAnalysis.amplitudeEnvelope;
      const peakData = detectPeaks(weights, config);
      this.peakData = peakData;

      if (this.reactiveMapper) {
        this.reactiveMapper.setPeakData(peakData);
      }

      return peakData;
    },

    // ============================================================
    // LEGACY AUDIO MAPPINGS
    // ============================================================

    /**
     * Apply audio reactivity mapping to particle layer (legacy)
     */
    addLegacyMapping(layerId: string, mapping: AudioParticleMapping): void {
      const existing = this.legacyMappings.get(layerId) || [];
      existing.push(mapping);
      this.legacyMappings.set(layerId, existing);
    },

    /**
     * Remove legacy audio mapping
     */
    removeLegacyMapping(layerId: string, index: number): void {
      const mappings = this.legacyMappings.get(layerId);
      if (mappings) {
        mappings.splice(index, 1);
        if (mappings.length === 0) {
          this.legacyMappings.delete(layerId);
        }
      }
    },

    /**
     * Get legacy mappings for a layer
     */
    getLegacyMappings(layerId: string): AudioParticleMapping[] {
      return this.legacyMappings.get(layerId) || [];
    },

    // ============================================================
    // NEW AUDIO REACTIVE SYSTEM
    // ============================================================

    /**
     * Add new audio mapping
     */
    addMapping(mapping: AudioMapping): void {
      this.reactiveMappings.push(mapping);

      if (this.reactiveMapper) {
        this.reactiveMapper.addMapping(mapping);
      }
    },

    /**
     * Remove audio mapping by ID
     */
    removeMapping(mappingId: string): void {
      const index = this.reactiveMappings.findIndex(m => m.id === mappingId);
      if (index >= 0) {
        this.reactiveMappings.splice(index, 1);
      }

      if (this.reactiveMapper) {
        this.reactiveMapper.removeMapping(mappingId);
      }
    },

    /**
     * Update audio mapping
     */
    updateMapping(mappingId: string, updates: Partial<AudioMapping>): void {
      const mapping = this.reactiveMappings.find(m => m.id === mappingId);
      if (mapping) {
        Object.assign(mapping, updates);
      }

      if (this.reactiveMapper) {
        this.reactiveMapper.updateMapping(mappingId, updates);
      }
    },

    /**
     * Get all audio mappings
     */
    getMappings(): AudioMapping[] {
      return this.reactiveMappings;
    },

    /**
     * Get mapped value at frame
     */
    getMappedValueAtFrame(mappingId: string, frame: number): number {
      if (!this.reactiveMapper) return 0;
      return this.reactiveMapper.getValueAtFrame(mappingId, frame);
    },

    /**
     * Get all mapped values at frame
     */
    getAllMappedValuesAtFrame(frame: number): Map<TargetParameter, number> {
      if (!this.reactiveMapper) return new Map();
      return this.reactiveMapper.getAllValuesAtFrame(frame);
    },

    /**
     * Get active mappings for a specific layer
     */
    getActiveMappingsForLayer(layerId: string): AudioMapping[] {
      return this.reactiveMappings.filter(
        m => m.enabled && (m.targetLayerId === layerId || m.targetLayerId === undefined)
      );
    },

    /**
     * Get audio reactive values for a specific layer at a specific frame
     * This is called by the engine during frame evaluation
     */
    getValuesForLayerAtFrame(layerId: string, frame: number): Map<TargetParameter, number> {
      if (!this.reactiveMapper) return new Map();
      return this.reactiveMapper.getValuesForLayerAtFrame(layerId, frame);
    },
  },
});

export type AudioStore = ReturnType<typeof useAudioStore>;
