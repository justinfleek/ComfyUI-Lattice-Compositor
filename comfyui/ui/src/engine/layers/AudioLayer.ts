/**
 * AudioLayer - Audio-only Layer
 *
 * An audio-only layer with no visual representation.
 * Used for background music, sound effects, and audio reactivity sources.
 *
 * Features:
 * - Audio playback control with Web Audio API
 * - Level/pan animation via GainNode and StereoPannerNode
 * - Waveform visualization in timeline
 * - Audio feature exposure for linking
 *
 * DETERMINISM: Audio position calculated from frame, not real-time
 */

import * as THREE from "three";
import { interpolateProperty } from "@/services/interpolation";
import type { AudioLayerData, Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";
import { BaseLayer } from "./BaseLayer";

// Web Audio nodes for playback
interface AudioPlaybackNodes {
  context: AudioContext;
  source: AudioBufferSourceNode | null;
  gainNode: GainNode;
  panNode: StereoPannerNode;
  buffer: AudioBuffer | null;
  isPlaying: boolean;
  startTime: number;
  startOffset: number;
}

export class AudioLayer extends BaseLayer {
  private audioData: AudioLayerData;
  private iconGroup: THREE.Group | null = null;
  private playbackNodes: AudioPlaybackNodes | null = null;

  // Static shared AudioContext (reused across all audio layers)
  private static sharedContext: AudioContext | null = null;

  constructor(layerData: Layer) {
    super(layerData);
    this.audioData = this.extractAudioData(layerData);
    this.createIconMesh();
  }

  /**
   * Get or create shared AudioContext
   */
  private static getAudioContext(): AudioContext {
    if (!AudioLayer.sharedContext) {
      AudioLayer.sharedContext = new AudioContext();
    }
    return AudioLayer.sharedContext;
  }

  /**
   * Extract audio layer data from layer object
   */
  private extractAudioData(layerData: Layer): AudioLayerData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: data ∈ Partial<AudioLayerData> | undefined → AudioLayerData (with explicit defaults)
    const data = (layerData.data !== null && typeof layerData.data === "object") ? layerData.data as Partial<AudioLayerData> : undefined;
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    // Pattern match: Extract each property with explicit type narrowing and defaults
    const assetIdValue = (data !== undefined && typeof data === "object" && data !== null && "assetId" in data && data.assetId !== null && typeof data.assetId === "string") ? data.assetId : null;
    const levelValue = (data !== undefined && typeof data === "object" && data !== null && "level" in data && data.level !== null && typeof data.level === "object") ? data.level : createAnimatableProperty("Level", 0, "number");
    const mutedValue = (data !== undefined && typeof data === "object" && data !== null && "muted" in data && typeof data.muted === "boolean") ? data.muted : false;
    const soloValue = (data !== undefined && typeof data === "object" && data !== null && "solo" in data && typeof data.solo === "boolean") ? data.solo : false;
    const panValue = (data !== undefined && typeof data === "object" && data !== null && "pan" in data && data.pan !== null && typeof data.pan === "object") ? data.pan : createAnimatableProperty("Pan", 0, "number");
    const loopValue = (data !== undefined && typeof data === "object" && data !== null && "loop" in data && typeof data.loop === "boolean") ? data.loop : false;
    const startTimeValue = (data !== undefined && typeof data === "object" && data !== null && "startTime" in data && typeof data.startTime === "number" && Number.isFinite(data.startTime)) ? data.startTime : 0;
    const speedValue = (data !== undefined && typeof data === "object" && data !== null && "speed" in data && typeof data.speed === "number" && Number.isFinite(data.speed)) ? data.speed : 1;
    const showWaveformValue = (data !== undefined && typeof data === "object" && data !== null && "showWaveform" in data && typeof data.showWaveform === "boolean") ? data.showWaveform : true;
    const waveformColorValue = (data !== undefined && typeof data === "object" && data !== null && "waveformColor" in data && typeof data.waveformColor === "string" && data.waveformColor.length > 0) ? data.waveformColor : "#4a90d9";
    const exposeFeaturesValue = (data !== undefined && typeof data === "object" && data !== null && "exposeFeatures" in data && typeof data.exposeFeatures === "boolean") ? data.exposeFeatures : false;
    
    return {
      assetId: assetIdValue,
      level: levelValue,
      muted: mutedValue,
      solo: soloValue,
      pan: panValue,
      loop: loopValue,
      startTime: startTimeValue,
      speed: speedValue,
      showWaveform: showWaveformValue,
      waveformColor: waveformColorValue,
      exposeFeatures: exposeFeaturesValue,
    };
  }

  /**
   * Create a visual indicator for the audio layer in the viewport
   * (speaker icon or waveform representation)
   */
  private createIconMesh(): void {
    // Create a simple speaker icon geometry
    this.iconGroup = new THREE.Group();

    // Speaker body
    const bodyGeometry = new THREE.BoxGeometry(20, 30, 5);
    const bodyMaterial = new THREE.MeshBasicMaterial({
      color: 0x4a90d9,
      transparent: true,
      opacity: 0.8,
    });
    const body = new THREE.Mesh(bodyGeometry, bodyMaterial);
    this.iconGroup.add(body);

    // Sound waves (arcs)
    const waveMaterial = new THREE.LineBasicMaterial({
      color: 0x4a90d9,
      transparent: true,
      opacity: 0.6,
    });

    for (let i = 0; i < 3; i++) {
      const curve = new THREE.EllipseCurve(
        15,
        0,
        10 + i * 8,
        15 + i * 5,
        -Math.PI / 3,
        Math.PI / 3,
        false,
        0,
      );
      const points = curve.getPoints(20);
      const geometry = new THREE.BufferGeometry().setFromPoints(
        points.map((p) => new THREE.Vector3(p.x, p.y, 0)),
      );
      const wave = new THREE.Line(geometry, waveMaterial);
      this.iconGroup.add(wave);
    }

    this.iconGroup.name = `audio_icon_${this.id}`;
    this.group.add(this.iconGroup);
  }

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  //                                              // abstract // implementations
  // ═══════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animated audio properties
    if (this.audioData.level) {
      const _level = interpolateProperty(
        this.audioData.level,
        frame,
        this.compositionFps,
      );
      // Level would be applied to audio playback engine
    }

    if (this.audioData.pan) {
      const _pan = interpolateProperty(
        this.audioData.pan,
        frame,
        this.compositionFps,
      );
      // Pan would be applied to audio playback engine
    }

    // Audio layers are typically invisible in render
    // but visible in editor for selection/manipulation
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<AudioLayerData> | undefined;

    if (data) {
      Object.assign(this.audioData, data);
    }
  }

  protected onDispose(): void {
    // Stop and clean up audio playback
    if (this.playbackNodes) {
      this.stopPlayback();
      this.playbackNodes.gainNode.disconnect();
      this.playbackNodes.panNode.disconnect();
      this.playbackNodes = null;
    }

    // Clean up Three.js objects
    if (this.iconGroup) {
      this.iconGroup.traverse((child) => {
        if (child instanceof THREE.Mesh) {
          child.geometry.dispose();
          if (child.material instanceof THREE.Material) {
            child.material.dispose();
          }
        }
        if (child instanceof THREE.Line) {
          child.geometry.dispose();
          if (child.material instanceof THREE.Material) {
            child.material.dispose();
          }
        }
      });
    }
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                             // audio // specific // methods
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Get the audio position for a given frame
   * Used for deterministic audio sync
   */
  getAudioTimeForFrame(frame: number, fps: number): number {
    // Validate fps (0/NaN would cause division by zero or NaN propagation)
    const validFps = Number.isFinite(fps) && fps > 0 ? fps : 30;
    const validFrame = Number.isFinite(frame) ? frame : 0;
    const layerTime = validFrame / validFps;
    // Validate speed (NaN would corrupt audio time calculation)
    const validSpeed = Number.isFinite(this.audioData.speed)
      ? this.audioData.speed
      : 1;
    const validStartTime = Number.isFinite(this.audioData.startTime)
      ? this.audioData.startTime
      : 0;
    const audioTime = (layerTime - validStartTime) * validSpeed;
    return Math.max(0, audioTime);
  }

  /**
   * Check if audio should be playing at given frame
   */
  isPlayingAtFrame(frame: number, fps: number): boolean {
    if (this.audioData.muted) return false;

    const audioTime = this.getAudioTimeForFrame(frame, fps);
    if (audioTime < 0) return false;

    // If looping, always playing (after start)
    if (this.audioData.loop) return true;

    // Check against audio duration if we have a buffer
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const playbackNodes = this.playbackNodes;
    const playbackNodesBuffer = (playbackNodes != null && typeof playbackNodes === "object" && "buffer" in playbackNodes && playbackNodes.buffer != null && typeof playbackNodes.buffer === "object") ? playbackNodes.buffer : undefined;
    if (playbackNodesBuffer != null && typeof playbackNodesBuffer === "object" && "duration" in playbackNodesBuffer && typeof playbackNodesBuffer.duration === "number") {
      return audioTime < playbackNodesBuffer.duration;
    }

    return true;
  }

  // ═══════════════════════════════════════════════════════════════════════════
  //                                             // audio // playback // methods
  // ═══════════════════════════════════════════════════════════════════════════

  /**
   * Initialize playback nodes with an AudioBuffer
   */
  initializePlayback(buffer: AudioBuffer): void {
    const context = AudioLayer.getAudioContext();

    // Create gain and pan nodes
    const gainNode = context.createGain();
    const panNode = context.createStereoPanner();

    // Connect: source -> gain -> pan -> destination
    gainNode.connect(panNode);
    panNode.connect(context.destination);

    this.playbackNodes = {
      context,
      source: null,
      gainNode,
      panNode,
      buffer,
      isPlaying: false,
      startTime: 0,
      startOffset: 0,
    };

    // Apply initial level
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: audioData.level.value ∈ number | undefined → number (default 0)
    const levelValue = (typeof this.audioData.level === "object" && this.audioData.level !== null && "value" in this.audioData.level && typeof this.audioData.level.value === "number" && Number.isFinite(this.audioData.level.value)) ? this.audioData.level.value : 0;
    this.updateGain(levelValue);
    // Pattern match: audioData.pan.value ∈ number | undefined → number (default 0)
    const panValue = (typeof this.audioData.pan === "object" && this.audioData.pan !== null && "value" in this.audioData.pan && typeof this.audioData.pan.value === "number" && Number.isFinite(this.audioData.pan.value)) ? this.audioData.pan.value : 0;
    this.updatePan(panValue);
  }

  /**
   * Start playback from a specific frame
   */
  startPlayback(frame: number, fps: number): void {
    if (!this.playbackNodes || !this.playbackNodes.buffer) return;
    if (this.audioData.muted) return;

    // Stop any existing playback
    this.stopPlayback();

    const context = this.playbackNodes.context;

    // Resume context if suspended (browser autoplay policy)
    if (context.state === "suspended") {
      context.resume();
    }

    // Calculate audio start time based on frame
    const audioTime = this.getAudioTimeForFrame(frame, fps);

    // Don't start if audio position would be beyond buffer duration
    if (
      audioTime < 0 ||
      (!this.audioData.loop && audioTime >= this.playbackNodes.buffer.duration)
    ) {
      return;
    }

    // Create new source node
    const source = context.createBufferSource();
    source.buffer = this.playbackNodes.buffer;
    source.loop = this.audioData.loop;

    // Apply playback rate (speed)
    source.playbackRate.value = this.audioData.speed;

    // Connect to gain node
    source.connect(this.playbackNodes.gainNode);

    // Store reference
    this.playbackNodes.source = source;
    this.playbackNodes.isPlaying = true;
    this.playbackNodes.startTime = context.currentTime;
    this.playbackNodes.startOffset = audioTime;

    // Handle playback end
    source.onended = () => {
      if (this.playbackNodes) {
        this.playbackNodes.isPlaying = false;
      }
    };

    // Start playback from calculated offset
    source.start(0, audioTime);
  }

  /**
   * Stop playback
   */
  stopPlayback(): void {
    if (!this.playbackNodes || !this.playbackNodes.source) return;

    try {
      this.playbackNodes.source.stop();
    } catch {
      // Ignore error if source already stopped
    }

    this.playbackNodes.source.disconnect();
    this.playbackNodes.source = null;
    this.playbackNodes.isPlaying = false;
  }

  /**
   * Check if currently playing
   */
  get isPlaying(): boolean {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: playbackNodes.isPlaying ∈ boolean | undefined → boolean (default false)
    return (this.playbackNodes !== null && typeof this.playbackNodes === "object" && "isPlaying" in this.playbackNodes && typeof this.playbackNodes.isPlaying === "boolean") ? this.playbackNodes.isPlaying : false;
  }

  /**
   * Update gain (level) - dB to linear conversion
   * Level is in dB: 0 = unity gain, -Infinity = silence, +6 = ~2x louder
   */
  updateGain(levelDb: number): void {
    if (!this.playbackNodes) return;

    // Validate levelDb (NaN bypasses Math.max/min and corrupts Web Audio)
    const validDb = Number.isFinite(levelDb) ? levelDb : 0;

    // Convert dB to linear: linear = 10^(dB/20)
    // Clamp to reasonable range: -60dB to +12dB
    const clampedDb = Math.max(-60, Math.min(12, validDb));
    const linearGain = clampedDb <= -60 ? 0 : 10 ** (clampedDb / 20);

    // Use setValueAtTime for immediate update without clicks
    this.playbackNodes.gainNode.gain.setValueAtTime(
      linearGain,
      this.playbackNodes.context.currentTime,
    );
  }

  /**
   * Update stereo pan (-1 = left, 0 = center, +1 = right)
   */
  updatePan(pan: number): void {
    if (!this.playbackNodes) return;

    // Validate pan (NaN bypasses Math.max/min and corrupts Web Audio)
    const validPan = Number.isFinite(pan) ? pan : 0;

    // Clamp pan to valid range
    const clampedPan = Math.max(-1, Math.min(1, validPan));

    this.playbackNodes.panNode.pan.setValueAtTime(
      clampedPan,
      this.playbackNodes.context.currentTime,
    );
  }

  /**
   * Scrub audio at a specific frame (play short snippet)
   */
  scrubAtFrame(frame: number, fps: number): void {
    if (!this.playbackNodes || !this.playbackNodes.buffer) return;
    if (this.audioData.muted) return;

    const context = this.playbackNodes.context;

    // Resume context if suspended
    if (context.state === "suspended") {
      context.resume();
    }

    // Stop any existing playback
    this.stopPlayback();

    // Calculate audio time
    const audioTime = this.getAudioTimeForFrame(frame, fps);
    if (audioTime < 0 || audioTime >= this.playbackNodes.buffer.duration)
      return;

    // Create source for scrub
    const source = context.createBufferSource();
    source.buffer = this.playbackNodes.buffer;
    source.playbackRate.value = this.audioData.speed;
    source.connect(this.playbackNodes.gainNode);

    // Play a short 100ms snippet
    const scrubDuration = 0.1;
    const endTime = Math.min(
      audioTime + scrubDuration,
      this.playbackNodes.buffer.duration,
    );

    this.playbackNodes.source = source;
    source.start(0, audioTime, endTime - audioTime);
  }

  /**
   * Update playback parameters during playback (called each frame)
   */
  updatePlaybackForFrame(frame: number): void {
    if (!this.playbackNodes) return;

    // Interpolate and apply level
    if (this.audioData.level) {
      const level: number = interpolateProperty(
        this.audioData.level,
        frame,
        this.compositionFps,
      );
      this.updateGain(level);
    }

    // Interpolate and apply pan
    if (this.audioData.pan) {
      const pan: number = interpolateProperty(
        this.audioData.pan,
        frame,
        this.compositionFps,
      );
      this.updatePan(pan);
    }
  }

  /**
   * Get the AudioBuffer (if loaded)
   */
  getAudioBuffer(): AudioBuffer | null {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining/nullish coalescing
    // Pattern match: playbackNodes.buffer ∈ AudioBuffer | null | undefined → AudioBuffer | null (default null)
    return (this.playbackNodes !== null && typeof this.playbackNodes === "object" && "buffer" in this.playbackNodes && this.playbackNodes.buffer !== null) ? this.playbackNodes.buffer : null;
  }

  /**
   * Check if audio has been initialized
   */
  get hasAudio(): boolean {
    return this.playbackNodes !== null && this.playbackNodes.buffer !== null;
  }
}
