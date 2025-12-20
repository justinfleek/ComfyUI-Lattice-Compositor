/**
 * AudioLayer - Audio-only Layer
 *
 * An audio-only layer with no visual representation.
 * Used for background music, sound effects, and audio reactivity sources.
 *
 * Features:
 * - Audio playback control
 * - Level/pan animation
 * - Waveform visualization in timeline
 * - Audio feature exposure for linking
 *
 * DETERMINISM: Audio position calculated from frame, not real-time
 */

import * as THREE from 'three';
import type { Layer, AudioLayerData } from '@/types/project';
import { createAnimatableProperty } from '@/types/project';
import { BaseLayer } from './BaseLayer';
import { interpolateProperty } from '@/services/interpolation';

export class AudioLayer extends BaseLayer {
  private audioData: AudioLayerData;
  private iconGroup: THREE.Group | null = null;

  constructor(layerData: Layer) {
    super(layerData);
    this.audioData = this.extractAudioData(layerData);
    this.createIconMesh();
  }

  /**
   * Extract audio layer data from layer object
   */
  private extractAudioData(layerData: Layer): AudioLayerData {
    const data = layerData.data as Partial<AudioLayerData> | undefined;
    return {
      assetId: data?.assetId ?? null,
      level: data?.level ?? createAnimatableProperty('Level', 0, 'number'),
      muted: data?.muted ?? false,
      solo: data?.solo ?? false,
      pan: data?.pan ?? createAnimatableProperty('Pan', 0, 'number'),
      loop: data?.loop ?? false,
      startTime: data?.startTime ?? 0,
      speed: data?.speed ?? 1,
      showWaveform: data?.showWaveform ?? true,
      waveformColor: data?.waveformColor ?? '#4a90d9',
      exposeFeatures: data?.exposeFeatures ?? false
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
      opacity: 0.8
    });
    const body = new THREE.Mesh(bodyGeometry, bodyMaterial);
    this.iconGroup.add(body);

    // Sound waves (arcs)
    const waveMaterial = new THREE.LineBasicMaterial({ color: 0x4a90d9, transparent: true, opacity: 0.6 });

    for (let i = 0; i < 3; i++) {
      const curve = new THREE.EllipseCurve(
        15, 0,
        10 + i * 8, 15 + i * 5,
        -Math.PI / 3, Math.PI / 3,
        false, 0
      );
      const points = curve.getPoints(20);
      const geometry = new THREE.BufferGeometry().setFromPoints(
        points.map(p => new THREE.Vector3(p.x, p.y, 0))
      );
      const wave = new THREE.Line(geometry, waveMaterial);
      this.iconGroup.add(wave);
    }

    this.iconGroup.name = `audio_icon_${this.id}`;
    this.group.add(this.iconGroup);
  }

  // ============================================================================
  // ABSTRACT IMPLEMENTATIONS
  // ============================================================================

  protected onEvaluateFrame(frame: number): void {
    // Evaluate animated audio properties
    if (this.audioData.level) {
      const level = interpolateProperty(this.audioData.level, frame);
      // Level would be applied to audio playback engine
    }

    if (this.audioData.pan) {
      const pan = interpolateProperty(this.audioData.pan, frame);
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

  // ============================================================================
  // AUDIO-SPECIFIC METHODS
  // ============================================================================

  /**
   * Get the audio position for a given frame
   * Used for deterministic audio sync
   */
  getAudioTimeForFrame(frame: number, fps: number): number {
    const layerTime = frame / fps;
    const audioTime = (layerTime - this.audioData.startTime) * this.audioData.speed;
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

    // Otherwise check against audio duration
    // Duration would need to come from asset metadata
    return true;
  }
}
