/**
 * Audio Store
 *
 * Manages audio state including loading, analysis, and reactive mappings.
 * This is a focused store extracted from compositorStore for better maintainability.
 */
import { isFiniteNumber, assertDefined } from "@/utils/typeGuards";
import { defineStore } from "pinia";
import type {
  AudioAnalysis,
  PeakData,
  PeakDetectionConfig,
} from "@/services/audioFeatures";
import {
  detectPeaks,
  getFeatureAtFrame as getFeatureAtFrameService,
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
import { useExpressionStore } from "./expressionStore";

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

  // Volume control
  volume: number; // 0-100
  muted: boolean;

  // Playback state
  audioContext: AudioContext | null;
  audioSource: AudioBufferSourceNode | null;
  gainNode: GainNode | null;
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
    volume: 100,
    muted: false,
    audioContext: null,
    audioSource: null,
    gainNode: null,
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
    // Type proof: duration ∈ ℝ ∪ {undefined} → ℝ
    duration: (state) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const durationValue = (state.audioBuffer != null && typeof state.audioBuffer === "object" && "duration" in state.audioBuffer && typeof state.audioBuffer.duration === "number") ? state.audioBuffer.duration : undefined;
      return isFiniteNumber(durationValue) && durationValue >= 0 ? durationValue : 0;
    },
    // Type proof: bpm ∈ ℝ ∪ {undefined} → ℝ
    bpm: (state) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const bpmValue = (state.audioAnalysis != null && typeof state.audioAnalysis === "object" && "bpm" in state.audioAnalysis && typeof state.audioAnalysis.bpm === "number") ? state.audioAnalysis.bpm : undefined;
      return isFiniteNumber(bpmValue) && bpmValue > 0 ? bpmValue : 0;
    },
    // Type proof: frameCount ∈ ℕ ∪ {undefined} → ℕ
    frameCount: (state) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const frameCountValue = (state.audioAnalysis != null && typeof state.audioAnalysis === "object" && "frameCount" in state.audioAnalysis && typeof state.audioAnalysis.frameCount === "number") ? state.audioAnalysis.frameCount : undefined;
      return isFiniteNumber(frameCountValue) && Number.isInteger(frameCountValue) && frameCountValue >= 0 ? frameCountValue : 0;
    },

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
      (_assetId?: string): number[] => {
        if (!state.audioAnalysis) {
          throw new Error("[AudioStore] Cannot get beats: No audio analysis available");
        }
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
        return beats;
      },
    /** Get BPM for audio */
    getBPM:
      (state) =>
      (_assetId?: string): number | undefined => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        return (state.audioAnalysis != null && typeof state.audioAnalysis === "object" && "bpm" in state.audioAnalysis && typeof state.audioAnalysis.bpm === "number") ? state.audioAnalysis.bpm : undefined;
      },

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
        // Type proof: analysis ∈ AudioAnalysis | undefined → AudioAnalysis | null
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const stemAnalysis = (stemData != null && typeof stemData === "object" && "analysis" in stemData && stemData.analysis != null) ? stemData.analysis : undefined;
        return stemAnalysis !== undefined ? stemAnalysis : state.audioAnalysis;
      }
      return state.audioAnalysis;
    },
    /** Get the active audio buffer (stem or main) */
    activeBuffer: (state) => {
      if (state.activeStemName) {
        const stemData = state.stemBuffers.get(state.activeStemName);
        // Type proof: buffer ∈ AudioBuffer | undefined → AudioBuffer | null
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const stemBuffer = (stemData != null && typeof stemData === "object" && "buffer" in stemData && stemData.buffer != null) ? stemData.buffer : undefined;
        return stemBuffer !== undefined ? stemBuffer : state.audioBuffer;
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

        // Update property driver system with new audio analysis
        const expressionStore = useExpressionStore();
        if (expressionStore.propertyDriverSystem && this.audioAnalysis) {
          expressionStore.propertyDriverSystem.setAudioAnalysis(this.audioAnalysis);
        }

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
    getFeatureAtFrame(
      store: { getActiveComp(): { currentFrame: number } | null } | null,
      feature: string,
      frame?: number,
    ): number {
      if (!this.audioAnalysis) return 0;
      // Type proof: targetFrame ∈ ℕ ∪ {undefined} → ℕ
      const frameValue = frame;
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const activeComp = (store != null && typeof store === "object" && typeof store.getActiveComp === "function") ? store.getActiveComp() : undefined;
      const compCurrentFrameValue = (activeComp != null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") ? activeComp.currentFrame : undefined;
      const targetFrame = isFiniteNumber(frameValue) && Number.isInteger(frameValue) && frameValue >= 0
        ? frameValue
        : (isFiniteNumber(compCurrentFrameValue) && Number.isInteger(compCurrentFrameValue) && compCurrentFrameValue >= 0 ? compCurrentFrameValue : 0);
      return getFeatureAtFrameService(this.audioAnalysis, feature, targetFrame);
    },

    /**
     * Check if frame is on a beat
     */
    isBeatAtFrame(frame: number): boolean {
      if (!this.audioAnalysis) return false;
      return isBeatAtFrame(this.audioAnalysis, frame);
    },

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    //                                                         // peak // detection
    // ════════════════════════════════════════════════════════════════════════════

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
    detectPeaks(config: PeakDetectionConfig): PeakData {
      if (!this.audioAnalysis) {
        throw new Error("[AudioStore] Cannot detect peaks: No audio analysis available");
      }

      const weights = this.audioAnalysis.amplitudeEnvelope;
      const peakData = detectPeaks(weights, config);
      this.peakData = peakData;

      if (this.reactiveMapper) {
        this.reactiveMapper.setPeakData(peakData);
      }

      return peakData;
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                               // legacy // audio // mappings
    // ════════════════════════════════════════════════════════════════════════════

    /**
     * Apply audio reactivity mapping to particle layer (legacy)
     */
    addLegacyMapping(layerId: string, mapping: AudioParticleMapping): void {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const existingRaw = this.legacyMappings.get(layerId);
      const existing = (existingRaw !== null && existingRaw !== undefined && Array.isArray(existingRaw)) ? existingRaw : [];
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      const mappings = this.legacyMappings.get(layerId);
      return (mappings !== null && mappings !== undefined && Array.isArray(mappings)) ? mappings : [];
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                        // new // audio // reactive // system
    // ════════════════════════════════════════════════════════════════════════════

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

    // ════════════════════════════════════════════════════════════════════════════
    //                                                         // audio // playback
    // ════════════════════════════════════════════════════════════════════════════

    // ════════════════════════════════════════════════════════════════════════════
    //                                                         // volume // control
    // ════════════════════════════════════════════════════════════════════════════

    /**
     * Set audio volume (0-100)
     */
    setVolume(volume: number): void {
      this.volume = Math.max(0, Math.min(100, volume));
      this.updateGainNode();
    },

    /**
     * Set muted state
     */
    setMuted(muted: boolean): void {
      this.muted = muted;
      this.updateGainNode();
    },

    /**
     * Toggle muted state
     */
    toggleMuted(): void {
      this.muted = !this.muted;
      this.updateGainNode();
    },

    /**
     * Update gain node with current volume/muted state
     */
    updateGainNode(): void {
      if (this.gainNode) {
        const effectiveVolume = this.muted ? 0 : this.volume / 100;
        this.gainNode.gain.setValueAtTime(
          effectiveVolume,
          (() => {
            // Type proof: currentTime ∈ ℝ ∪ {undefined} → ℝ
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const currentTimeValue = (this.audioContext != null && typeof this.audioContext === "object" && "currentTime" in this.audioContext && typeof this.audioContext.currentTime === "number") ? this.audioContext.currentTime : undefined;
            return isFiniteNumber(currentTimeValue) && currentTimeValue >= 0 ? currentTimeValue : 0;
          })(),
        );
      }
    },

    /**
     * Initialize audio context if needed
     */
    ensureAudioContext(): AudioContext {
      if (!this.audioContext) {
        this.audioContext = new AudioContext();
        // Create persistent gain node for volume control
        this.gainNode = this.audioContext.createGain();
        this.gainNode.connect(this.audioContext.destination);
        this.updateGainNode();
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

      // Create new source and connect through gain node
      this.audioSource = context.createBufferSource();
      this.audioSource.buffer = this.audioBuffer;
      // Type proof: gainNode is guaranteed non-null by ensureAudioContext() creating it
      assertDefined(this.gainNode, "gainNode must exist after ensureAudioContext()");
      this.audioSource.connect(this.gainNode);

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

      // Create and play short snippet through gain node for volume control
      this.audioSource = context.createBufferSource();
      this.audioSource.buffer = this.audioBuffer;
      // Type proof: gainNode is guaranteed non-null by ensureAudioContext() creating it
      assertDefined(this.gainNode, "gainNode must exist after ensureAudioContext()");
      this.audioSource.connect(this.gainNode);

      // Start at frame time, play for scrubDuration
      const endTime = Math.min(time + scrubDuration, this.audioBuffer.duration);
      this.audioSource.start(0, time, endTime - time);
    },

    // ════════════════════════════════════════════════════════════════════════════
    //                                                        // stem // reactivity
    // ════════════════════════════════════════════════════════════════════════════

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
      // Type proof: stemName ∈ string | undefined → string
      const stemNameDisplay = typeof stemName === "string" ? stemName : "main audio";
      storeLogger.debug(`Active stem set to: ${stemNameDisplay}`);

      // Re-initialize the reactive mapper with the new analysis
      this.initializeReactiveMapperForActiveStem();
    },

    /**
     * Initialize reactive mapper for the currently active stem/main audio
     */
    initializeReactiveMapperForActiveStem(): void {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const stemData = this.activeStemName ? this.stemBuffers.get(this.activeStemName) : undefined;
      const analysis = this.activeStemName
        ? ((stemData != null && typeof stemData === "object" && "analysis" in stemData && stemData.analysis != null) ? stemData.analysis : undefined)
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const stemData = this.activeStemName ? this.stemBuffers.get(this.activeStemName) : undefined;
      const analysis = this.activeStemName
        ? ((stemData != null && typeof stemData === "object" && "analysis" in stemData && stemData.analysis != null) ? stemData.analysis : undefined)
        : this.audioAnalysis;

      if (!analysis) return 0;
      return getFeatureAtFrameService(analysis, feature, frame);
    },

    /**
     * Get stem analysis by name
     * @param stemName - Name of the stem
     */
    getStemAnalysis(stemName: string): AudioAnalysis | null {
      // Type proof: analysis ∈ AudioAnalysis | undefined → AudioAnalysis | null
      const stemData = this.stemBuffers.get(stemName);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const analysis = (stemData != null && typeof stemData === "object" && "analysis" in stemData && stemData.analysis != null) ? stemData.analysis : undefined;
      return analysis !== undefined ? analysis : null;
    },

    /**
     * Get stem buffer by name
     * @param stemName - Name of the stem
     */
    getStemBuffer(stemName: string): AudioBuffer | null {
      // Type proof: buffer ∈ AudioBuffer | undefined → AudioBuffer | null
      const stemData = this.stemBuffers.get(stemName);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const buffer = (stemData != null && typeof stemData === "object" && "buffer" in stemData && stemData.buffer != null) ? stemData.buffer : undefined;
      return buffer !== undefined ? buffer : null;
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
