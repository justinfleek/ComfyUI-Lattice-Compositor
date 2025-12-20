/**
 * Preset Store
 *
 * Manages saving, loading, and organizing presets for particles,
 * effects, animations, and other configurable elements.
 *
 * Features:
 * - localStorage persistence
 * - Import/export to JSON
 * - Built-in presets
 * - Search and filtering
 */

import { defineStore } from 'pinia';
import type {
  Preset,
  PresetCategory,
  PresetCollection,
  ParticlePreset,
  PathEffectPreset,
  CameraShakePreset,
  CameraTrajectoryPreset,
  TextStylePreset,
  AnimationPreset,
} from '@/types/presets';
import {
  BUILT_IN_PARTICLE_PRESETS,
  BUILT_IN_PATH_EFFECT_PRESETS,
} from '@/types/presets';

const STORAGE_KEY = 'weyl-presets';
const PRESET_VERSION = 1;

interface PresetState {
  presets: Preset[];
  loaded: boolean;
}

export const usePresetStore = defineStore('presets', {
  state: (): PresetState => ({
    presets: [],
    loaded: false,
  }),

  getters: {
    /**
     * Get all presets including built-ins
     */
    allPresets(): Preset[] {
      return [
        ...BUILT_IN_PARTICLE_PRESETS,
        ...BUILT_IN_PATH_EFFECT_PRESETS,
        ...this.presets,
      ];
    },

    /**
     * Get presets by category
     */
    byCategory(): (category: PresetCategory) => Preset[] {
      return (category: PresetCategory) =>
        this.allPresets.filter(p => p.category === category);
    },

    /**
     * Get particle presets
     */
    particlePresets(): ParticlePreset[] {
      return this.allPresets.filter(p => p.category === 'particle') as ParticlePreset[];
    },

    /**
     * Get path effect presets
     */
    pathEffectPresets(): PathEffectPreset[] {
      return this.allPresets.filter(p => p.category === 'path-effect') as PathEffectPreset[];
    },

    /**
     * Get camera shake presets
     */
    cameraShakePresets(): CameraShakePreset[] {
      return this.allPresets.filter(p => p.category === 'camera-shake') as CameraShakePreset[];
    },

    /**
     * Get camera trajectory presets
     */
    cameraTrajectoryPresets(): CameraTrajectoryPreset[] {
      return this.allPresets.filter(p => p.category === 'camera-trajectory') as CameraTrajectoryPreset[];
    },

    /**
     * Get text style presets
     */
    textStylePresets(): TextStylePreset[] {
      return this.allPresets.filter(p => p.category === 'text-style') as TextStylePreset[];
    },

    /**
     * Get animation presets
     */
    animationPresets(): AnimationPreset[] {
      return this.allPresets.filter(p => p.category === 'animation') as AnimationPreset[];
    },

    /**
     * Search presets by name or tags
     */
    search(): (query: string, category?: PresetCategory) => Preset[] {
      return (query: string, category?: PresetCategory) => {
        const q = query.toLowerCase();
        let results = this.allPresets;

        if (category) {
          results = results.filter(p => p.category === category);
        }

        return results.filter(p =>
          p.name.toLowerCase().includes(q) ||
          p.description?.toLowerCase().includes(q) ||
          p.tags?.some(t => t.toLowerCase().includes(q))
        );
      };
    },

    /**
     * Get user-created presets (excludes built-ins)
     */
    userPresets(): Preset[] {
      return this.presets.filter(p => !p.isBuiltIn);
    },
  },

  actions: {
    /**
     * Initialize the preset store from localStorage
     */
    initialize() {
      if (this.loaded) return;

      try {
        const stored = localStorage.getItem(STORAGE_KEY);
        if (stored) {
          const data = JSON.parse(stored) as PresetCollection;
          this.presets = data.presets || [];
        }
      } catch (error) {
        console.warn('Failed to load presets from localStorage:', error);
        this.presets = [];
      }

      this.loaded = true;
    },

    /**
     * Save presets to localStorage
     */
    persist() {
      try {
        const collection: PresetCollection = {
          version: PRESET_VERSION,
          presets: this.presets.filter(p => !p.isBuiltIn),
          exportedAt: Date.now(),
        };
        localStorage.setItem(STORAGE_KEY, JSON.stringify(collection));
      } catch (error) {
        console.error('Failed to save presets to localStorage:', error);
      }
    },

    /**
     * Generate a unique preset ID
     */
    generateId(): string {
      return `preset_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    },

    /**
     * Add a new preset
     */
    addPreset(preset: Omit<Preset, 'id' | 'createdAt' | 'updatedAt'>): string {
      const id = this.generateId();
      const now = Date.now();

      const newPreset = {
        ...preset,
        id,
        createdAt: now,
        updatedAt: now,
      } as Preset;

      this.presets.push(newPreset);
      this.persist();

      return id;
    },

    /**
     * Update an existing preset
     */
    updatePreset(id: string, updates: Partial<Preset>): boolean {
      const index = this.presets.findIndex(p => p.id === id);
      if (index === -1) return false;

      // Don't allow updating built-in presets
      if (this.presets[index].isBuiltIn) return false;

      this.presets[index] = {
        ...this.presets[index],
        ...updates,
        updatedAt: Date.now(),
      } as Preset;

      this.persist();
      return true;
    },

    /**
     * Delete a preset
     */
    deletePreset(id: string): boolean {
      const index = this.presets.findIndex(p => p.id === id);
      if (index === -1) return false;

      // Don't allow deleting built-in presets
      if (this.presets[index].isBuiltIn) return false;

      this.presets.splice(index, 1);
      this.persist();
      return true;
    },

    /**
     * Duplicate a preset
     */
    duplicatePreset(id: string): string | null {
      const preset = this.allPresets.find(p => p.id === id);
      if (!preset) return null;

      const duplicated = {
        ...preset,
        name: `${preset.name} (Copy)`,
        isBuiltIn: false,
      };

      // Remove id so a new one is generated
      delete (duplicated as any).id;
      delete (duplicated as any).createdAt;
      delete (duplicated as any).updatedAt;

      return this.addPreset(duplicated as Omit<Preset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Get a preset by ID
     */
    getPreset(id: string): Preset | undefined {
      return this.allPresets.find(p => p.id === id);
    },

    /**
     * Export presets to JSON string
     */
    exportPresets(presetIds?: string[]): string {
      const presetsToExport = presetIds
        ? this.allPresets.filter(p => presetIds.includes(p.id))
        : this.userPresets;

      const collection: PresetCollection = {
        version: PRESET_VERSION,
        presets: presetsToExport,
        exportedAt: Date.now(),
      };

      return JSON.stringify(collection, null, 2);
    },

    /**
     * Import presets from JSON string
     */
    importPresets(jsonString: string): { imported: number; errors: string[] } {
      const errors: string[] = [];
      let imported = 0;

      try {
        const collection = JSON.parse(jsonString) as PresetCollection;

        if (!collection.presets || !Array.isArray(collection.presets)) {
          errors.push('Invalid preset collection format');
          return { imported, errors };
        }

        for (const preset of collection.presets) {
          try {
            // Validate required fields
            if (!preset.name || !preset.category) {
              errors.push(`Skipped preset: missing name or category`);
              continue;
            }

            // Check for duplicate names in same category
            const existing = this.presets.find(
              p => p.name === preset.name && p.category === preset.category
            );

            if (existing) {
              // Update existing preset
              this.updatePreset(existing.id, preset);
            } else {
              // Add new preset (remove id to generate new one)
              const { id, createdAt, updatedAt, ...presetData } = preset;
              this.addPreset(presetData as Omit<Preset, 'id' | 'createdAt' | 'updatedAt'>);
            }

            imported++;
          } catch (err) {
            errors.push(`Failed to import preset "${preset.name}": ${err}`);
          }
        }
      } catch (err) {
        errors.push(`Failed to parse JSON: ${err}`);
      }

      return { imported, errors };
    },

    /**
     * Save current particle config as a preset
     */
    saveParticlePreset(
      name: string,
      config: ParticlePreset['config'],
      options?: {
        description?: string;
        tags?: string[];
        thumbnail?: string;
      }
    ): string {
      return this.addPreset({
        name,
        category: 'particle',
        config,
        ...options,
      } as Omit<ParticlePreset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Save path effects as a preset
     */
    savePathEffectPreset(
      name: string,
      effects: PathEffectPreset['effects'],
      options?: {
        description?: string;
        tags?: string[];
      }
    ): string {
      return this.addPreset({
        name,
        category: 'path-effect',
        effects,
        ...options,
      } as Omit<PathEffectPreset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Save camera shake config as a preset
     */
    saveCameraShakePreset(
      name: string,
      config: CameraShakePreset['config'],
      options?: {
        description?: string;
        tags?: string[];
      }
    ): string {
      return this.addPreset({
        name,
        category: 'camera-shake',
        config,
        ...options,
      } as Omit<CameraShakePreset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Save camera trajectory config as a preset
     */
    saveCameraTrajectoryPreset(
      name: string,
      config: CameraTrajectoryPreset['config'],
      options?: {
        description?: string;
        tags?: string[];
      }
    ): string {
      return this.addPreset({
        name,
        category: 'camera-trajectory',
        config,
        ...options,
      } as Omit<CameraTrajectoryPreset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Save text style as a preset
     */
    saveTextStylePreset(
      name: string,
      style: TextStylePreset['style'],
      options?: {
        description?: string;
        tags?: string[];
      }
    ): string {
      return this.addPreset({
        name,
        category: 'text-style',
        style,
        ...options,
      } as Omit<TextStylePreset, 'id' | 'createdAt' | 'updatedAt'>);
    },

    /**
     * Clear all user presets
     */
    clearUserPresets() {
      this.presets = this.presets.filter(p => p.isBuiltIn);
      this.persist();
    },
  },
});
