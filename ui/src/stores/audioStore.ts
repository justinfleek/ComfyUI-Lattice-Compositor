/**
 * Audio Store
 *
 * Manages audio state including loading, analysis, and reactive mappings.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { defineStore } from "pinia";
import type {
  AudioAnalysis,
  PeakData,
  PeakDetectionConfig,
} from "@/services/audioFeatures";
import {
  detectPeaks,
  getFeatureAtFrame,
  isBeatAtFrame,
} from "@/services/audioFeatures";
import type {
  AudioMapping,
  TargetParameter,
} from "@/services/audioReactiveMapping";
import { AudioReactiveMapper } from "@/services/audioReactiveMapping";
import {
  cancelAnalysis,
  loadAndAnalyzeAudio,
} from "@/services/audioWorkerClient";
import type { AudioParticleMapping } from "@/types/project";
import { storeLogger } from "@/utils/logger";

interface StemData {
  buffer: AudioBuffer;
  analysis: AudioAnalysis;
}

interface AudioState {
  // Audio buffer and analysis
  audioBuffer: AudioBuffer | null;
  audioAnalysis: AudioAnalysis | null;
  audioFile: File | null;

  // Loading state
  loadingState: "idle" | "decoding" | "analyzing" | "complete" | "error";
  loadingProgress: number;
  loadingPhase: string;
  loadingError: string | null;

  // Playback state
  audioContext: AudioContext | null;
  audioSource: AudioBufferSourceNode | null;
  isPlayingAudio: boolean;
  audioStartTime: number;
  audioStartOffset: number;

  // Peak detection
  peakData: PeakData | null;

  // Legacy audio-particle mappings
  legacyMappings: Map<string, AudioParticleMapping[]>;

  // New audio reactive system
  reactiveMappings: AudioMapping[];
  reactiveMapper: AudioReactiveMapper | null;

  // Stem reactivity support
  stemBuffers: Map<string, StemData>;
  activeStemName: string | null; // null = use main audio
}

export const useAudioStore = defineStore("audio", {
  state: (): AudioState => ({
    audioBuffer: null,
    audioAnalysis: null,
    audioFile: null,
    loadingState: "idle",
    loadingProgress: 0,
    loadingPhase: "",
    loadingError: null,
    audioContext: null,
    audioSource: null,
    isPlayingAudio: false,
    audioStartTime: 0,
    audioStartOffset: 0,
    peakData: null,
    legacyMappings: new Map(),
    reactiveMappings: [],
    reactiveMapper: null,
    // Stem reactivity
    stemBuffers: new Map(),
    activeStemName: null,
  }),

  getters: {
    isLoaded: (state) => state.audioAnalysis !== null,
    isLoading: (state) =>
      state.loadingState === "decoding" || state.loadingState === "analyzing",
    hasError: (state) => state.loadingState === "error",
    duration: (state) => state.audioBuffer?.duration ?? 0,
    bpm: (state) => state.audioAnalysis?.bpm ?? 0,
    frameCount: (state) => state.audioAnalysis?.frameCount ?? 0,

    // Waveform integration helpers
    /** Check if audio buffer is loaded (for waveform rendering) */
    hasAudioBuffer: (state) => (_assetId?: string) =>
      state.audioBuffer !== null,
    /** Get audio buffer for waveform generation */
    getAudioBuffer: (state) => (_assetId?: string) => state.audioBuffer,
    /** Get beat timestamps in seconds
     *  @param _assetId - Optional asset ID (unused, for API compatibility)
     *  Uses the fps from the audio analysis (derived from frameCount/duration)
     */
    getBeats:
      (state) =>
      (_assetId?: string): number[] | undefined => {
        if (!state.audioAnalysis) return undefined;
        // Calculate fps from analysis data: fps = frameCount / duration
        // This ensures we use the same fps that was used during analysis
        const fps =
          state.audioAnalysis.frameCount / state.audioAnalysis.duration;
        const beats: number[] = [];
        for (let frame = 0; frame < state.audioAnalysis.frameCount; frame++) {
          if (isBeatAtFrame(state.audioAnalysis, frame)) {
            beats.push(frame / fps);
          }
        }
        return beats.length > 0 ? beats : undefined;
      },
    /** Get BPM for audio */
    getBPM:
      (state) =>
      (_assetId?: string): number | undefined =>
        state.audioAnalysis?.bpm,

    // Stem reactivity getters
    /** Get list of available stem names */
    availableStems: (state) => Array.from(state.stemBuffers.keys()),
    /** Check if any stems are loaded */
    hasStems: (state) => state.stemBuffers.size > 0,
    /** Get the active stem name (null = main audio) */
    getActiveStemName: (state) => state.activeStemName,
    /** Get the active audio analysis (stem or main) */
    activeAnalysis: (state) => {
      if (state.activeStemName) {
        const stemData = state.stemBuffers.get(state.activeStemName);
        return stemData?.analysis ?? state.audioAnalysis;
      }
      return state.audioAnalysis;
    },
    /** Get the active audio buffer (stem or main) */
    activeBuffer: (state) => {
      if (state.activeStemName) {
        const stemData = state.stemBuffers.get(state.activeStemName);
        return stemData?.buffer ?? state.audioBuffer;
      }
      return state.audioBuffer;
    },
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
      this.loadingState = "decoding";
      this.loadingProgress = 0;
      this.loadingPhase = "Preparing...";
      this.loadingError = null;

      try {
        const result = await loadAndAnalyzeAudio(file, fps, {
          onProgress: (progress) => {
            if (progress.phase === "decoding") {
              this.loadingState = "decoding";
            } else {
              this.loadingState = "analyzing";
            }
            this.loadingProgress = progress.progress;
            this.loadingPhase = progress.message;
          },
        });

        this.audioBuffer = result.buffer;
        this.audioAnalysis = result.analysis;
        this.loadingState = "complete";
        this.loadingProgress = 1;
        this.loadingPhase = "Complete";

        // Initialize the audio reactive mapper
        this.initializeReactiveMapper();

        storeLogger.debug("Audio loaded:", {
          duration: this.audioBuffer.duration,
          bpm: this.audioAnalysis.bpm,
          frameCount: this.audioAnalysis.frameCount,
        });
      } catch (error) {
        storeLogger.error("Failed to load audio:", error);
        this.audioFile = null;
        this.audioBuffer = null;
        this.audioAnalysis = null;
        this.reactiveMapper = null;
        this.loadingState = "error";
        this.loadingError = (error as Error).message;
      }
    },

    /**
     * Cancel ongoing audio analysis
     */
    cancelLoad(): void {
      cancelAnalysis();
      this.loadingState = "idle";
      this.loadingProgress = 0;
      this.loadingPhase = "";
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
      const index = this.reactiveMappings.findIndex((m) => m.id === mappingId);
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
      const mapping = this.reactiveMappings.find((m) => m.id === mappingId);
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
        (m) =>
          m.enabled &&
          (m.targetLayerId === layerId || m.targetLayerId === undefined),
      );
    },

    /**
     * Get audio reactive values for a specific layer at a specific frame
     * This is called by the engine during frame evaluation
     */
    getValuesForLayerAtFrame(
      layerId: string,
      frame: number,
    ): Map<TargetParameter, number> {
      if (!this.reactiveMapper) return new Map();
      return this.reactiveMapper.getValuesForLayerAtFrame(layerId, frame);
    },

    // ============================================================
    // AUDIO PLAYBACK (Ctrl+. for audio-only preview)
    // ============================================================

    /**
     * Initialize audio context if needed
     */
    ensureAudioContext(): AudioContext {
      if (!this.audioContext) {
        this.audioContext = new AudioContext();
      }
      return this.audioContext;
    },

    /**
     * Play audio from a specific frame
     * @param frame - Current frame to start from
     * @param fps - Frames per second for time calculation
     */
    playAudioFromFrame(frame: number, fps: number): void {
      if (!this.audioBuffer) {
        storeLogger.debug("No audio loaded");
        return;
      }

      // Stop any existing playback
      this.stopAudio();

      const context = this.ensureAudioContext();

      // Resume context if suspended (browser autoplay policy)
      if (context.state === "suspended") {
        context.resume();
      }

      // Calculate start time in seconds
      const startTime = frame / fps;

      // Create new source
      this.audioSource = context.createBufferSource();
      this.audioSource.buffer = this.audioBuffer;
      this.audioSource.connect(context.destination);

      // Store start info for getCurrentTime calculation
      this.audioStartTime = context.currentTime;
      this.audioStartOffset = startTime;
      this.isPlayingAudio = true;

      // Start playback from offset
      this.audioSource.start(0, startTime);

      // Handle playback end
      this.audioSource.onended = () => {
        this.isPlayingAudio = false;
      };

      storeLogger.debug(
        "Audio playback started at frame",
        frame,
        "time",
        startTime,
      );
    },

    /**
     * Stop audio playback
     */
    stopAudio(): void {
      if (this.audioSource) {
        try {
          this.audioSource.stop();
        } catch {
          // Ignore error if source already stopped
        }
        this.audioSource.disconnect();
        this.audioSource = null;
      }
      this.isPlayingAudio = false;
      storeLogger.debug("Audio playback stopped");
    },

    /**
     * Toggle audio playback (Ctrl+.)
     * @param frame - Current frame
     * @param fps - Frames per second
     */
    toggleAudioPlayback(frame: number, fps: number): void {
      if (this.isPlayingAudio) {
        this.stopAudio();
      } else {
        this.playAudioFromFrame(frame, fps);
      }
    },

    /**
     * Get current audio playback time in seconds
     */
    getCurrentAudioTime(): number {
      if (!this.isPlayingAudio || !this.audioContext) return 0;
      return (
        this.audioStartOffset +
        (this.audioContext.currentTime - this.audioStartTime)
      );
    },

    /**
     * Scrub audio at a specific position (for Ctrl+drag audio scrub)
     * This plays a short snippet of audio at the given frame
     * @param frame - Frame to scrub to
     * @param fps - Frames per second
     */
    scrubAudio(frame: number, fps: number): void {
      if (!this.audioBuffer) return;

      const context = this.ensureAudioContext();

      // Resume context if suspended
      if (context.state === "suspended") {
        context.resume();
      }

      // Stop any existing scrub playback
      if (this.audioSource) {
        try {
          this.audioSource.stop();
        } catch {
          // Ignore
        }
        this.audioSource.disconnect();
      }

      // Calculate time position
      const time = frame / fps;
      const scrubDuration = 0.1; // Play 100ms of audio

      // Create and play short snippet
      this.audioSource = context.createBufferSource();
      this.audioSource.buffer = this.audioBuffer;
      this.audioSource.connect(context.destination);

      // Start at frame time, play for scrubDuration
      const endTime = Math.min(time + scrubDuration, this.audioBuffer.duration);
      this.audioSource.start(0, time, endTime - time);
    },

    // ============================================================
    // STEM REACTIVITY (Audio source separation support)
    // ============================================================

    /**
     * Load and analyze an audio stem from a data URL or Blob
     * @param stemName - Name of the stem (e.g., 'vocals', 'drums', 'bass', 'other')
     * @param audioData - Blob or data URL containing the stem audio
     * @param fps - Frames per second for analysis
     */
    async loadStem(
      stemName: string,
      audioData: Blob | string,
      fps: number,
    ): Promise<void> {
      storeLogger.debug(`Loading stem: ${stemName}`);

      try {
        // Convert data URL to Blob if needed
        let blob: Blob;
        if (typeof audioData === "string") {
          // Data URL
          const response = await fetch(audioData);
          blob = await response.blob();
        } else {
          blob = audioData;
        }

        // Create a File from the Blob for the worker
        const file = new File([blob], `${stemName}.wav`, { type: "audio/wav" });

        // Analyze the stem using the same worker
        const result = await loadAndAnalyzeAudio(file, fps, {
          onProgress: (progress) => {
            storeLogger.debug(`Stem ${stemName} analysis: ${progress.message}`);
          },
        });

        // Store the stem data
        this.stemBuffers.set(stemName, {
          buffer: result.buffer,
          analysis: result.analysis,
        });

        storeLogger.debug(`Stem ${stemName} loaded:`, {
          duration: result.buffer.duration,
          bpm: result.analysis.bpm,
          frameCount: result.analysis.frameCount,
        });
      } catch (error) {
        storeLogger.error(`Failed to load stem ${stemName}:`, error);
        throw error;
      }
    },

    /**
     * Set the active stem for audio reactivity
     * @param stemName - Name of the stem to use, or null for main audio
     */
    setActiveStem(stemName: string | null): void {
      if (stemName !== null && !this.stemBuffers.has(stemName)) {
        storeLogger.warn(`Stem ${stemName} not found, using main audio`);
        this.activeStemName = null;
        return;
      }

      this.activeStemName = stemName;
      storeLogger.debug(`Active stem set to: ${stemName ?? "main audio"}`);

      // Re-initialize the reactive mapper with the new analysis
      this.initializeReactiveMapperForActiveStem();
    },

    /**
     * Initialize reactive mapper for the currently active stem/main audio
     */
    initializeReactiveMapperForActiveStem(): void {
      const analysis = this.activeStemName
        ? this.stemBuffers.get(this.activeStemName)?.analysis
        : this.audioAnalysis;

      if (!analysis) return;

      this.reactiveMapper = new AudioReactiveMapper(analysis);

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
     * Get audio feature value at frame from the active stem or main audio
     * @param feature - Feature name (amplitude, bass, mid, high, etc.)
     * @param frame - Frame number
     */
    getActiveFeatureAtFrame(feature: string, frame: number): number {
      const analysis = this.activeStemName
        ? this.stemBuffers.get(this.activeStemName)?.analysis
        : this.audioAnalysis;

      if (!analysis) return 0;
      return getFeatureAtFrame(analysis, feature, frame);
    },

    /**
     * Get stem analysis by name
     * @param stemName - Name of the stem
     */
    getStemAnalysis(stemName: string): AudioAnalysis | null {
      return this.stemBuffers.get(stemName)?.analysis ?? null;
    },

    /**
     * Get stem buffer by name
     * @param stemName - Name of the stem
     */
    getStemBuffer(stemName: string): AudioBuffer | null {
      return this.stemBuffers.get(stemName)?.buffer ?? null;
    },

    /**
     * Check if a stem is loaded
     * @param stemName - Name of the stem
     */
    hasStem(stemName: string): boolean {
      return this.stemBuffers.has(stemName);
    },

    /**
     * Remove a specific stem
     * @param stemName - Name of the stem to remove
     */
    removeStem(stemName: string): void {
      this.stemBuffers.delete(stemName);

      // If the removed stem was active, switch back to main audio
      if (this.activeStemName === stemName) {
        this.activeStemName = null;
        this.initializeReactiveMapperForActiveStem();
      }
    },

    /**
     * Clear all loaded stems
     */
    clearStems(): void {
      this.stemBuffers.clear();
      this.activeStemName = null;

      // Re-initialize with main audio
      this.initializeReactiveMapper();
    },

    /**
     * Get all stem names and their durations
     */
    getStemInfo(): Array<{ name: string; duration: number; bpm: number }> {
      const info: Array<{ name: string; duration: number; bpm: number }> = [];

      for (const [name, data] of this.stemBuffers.entries()) {
        info.push({
          name,
          duration: data.buffer.duration,
          bpm: data.analysis.bpm,
        });
      }

      return info;
    },
  },
});

export type AudioStore = ReturnType<typeof useAudioStore>;
