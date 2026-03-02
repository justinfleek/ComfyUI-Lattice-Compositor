/**
 * Feature Flags Store
 * 
 * Manages feature flags with priority:
 * 1. User preferences (highest)
 * 2. Project settings
 * 3. Global defaults
 * 4. Code defaults (lowest)
 */

import { defineStore } from 'pinia';
import { ref, computed } from 'vue';

interface FeatureFlag {
  name: string;
  enabled_by_default: boolean;
  category: string;
}

export const useFeatureFlagsStore = defineStore('featureFlags', () => {
  const globalFlags = ref<Record<string, boolean>>({});
  const projectFlags = ref<Record<string, boolean>>({});
  const userFlags = ref<Record<string, boolean>>({});

  /**
   * Check if a feature is enabled
   * Priority: user > project > global > code default
   */
  function isFeatureEnabled(
    flagName: string,
    defaultValue: boolean = false
  ): boolean {
    // Check user override
    if (userFlags.value[flagName] !== undefined) {
      return userFlags.value[flagName];
    }
    
    // Check project override
    if (projectFlags.value[flagName] !== undefined) {
      return projectFlags.value[flagName];
    }
    
    // Check global default
    if (globalFlags.value[flagName] !== undefined) {
      return globalFlags.value[flagName];
    }
    
    // Fallback to code default
    return defaultValue;
  }

  /**
   * Set feature flag (user override)
   */
  function setFeatureFlag(flagName: string, enabled: boolean) {
    userFlags.value[flagName] = enabled;
    // Persist to localStorage
    const stored = JSON.parse(localStorage.getItem('featureFlags') || '{}');
    stored[flagName] = enabled;
    localStorage.setItem('featureFlags', JSON.stringify(stored));
  }

  /**
   * Load user flags from localStorage
   */
  function loadUserFlags() {
    const stored = localStorage.getItem('featureFlags');
    if (stored) {
      userFlags.value = JSON.parse(stored);
    }
  }

  /**
   * Load global feature flags from database
   * TODO: Wire to DuckDB via FFI when backend is ready
   */
  async function loadGlobalFlags() {
    // For now, use hardcoded defaults matching init-feature-flags.sql
    globalFlags.value = {
      'ff-ui-particles': true,
      'ff-ui-physics': true,
      'ff-ui-camera': true,
      'ff-ui-audio': true,
      'ff-ui-ai-chat': true,
      'ff-ui-timeline': true,
      'ff-engine-webgpu': true,
      'ff-engine-webgl': true,
      'ff-engine-motion-blur': false,
      'ff-export-h264': true,
      'ff-export-prores': false,
      'ff-export-webm': true,
      'ff-export-camera': true,
      'ff-ai-chat': true,
      'ff-ai-generation': true,
      'ff-ai-segmentation': true,
      'ff-ai-vectorization': true,
      'ff-particles-enabled': true,
      'ff-particles-gpu': true,
      'ff-particles-sph': false,
      'ff-particles-flocking': true,
      'ff-physics-enabled': true,
      'ff-physics-ragdoll': false,
      'ff-physics-joints': true,
      'ff-experimental-mesh-warp': false,
      'ff-experimental-gaussian-splatting': false,
      'ff-experimental-depthflow': false,
    };
  }

  /**
   * Load project-specific feature flags
   * TODO: Wire to DuckDB via FFI when backend is ready
   */
  async function loadProjectFlags(projectId: string) {
    // For now, empty - will be populated from database
    projectFlags.value = {};
  }

  /**
   * Initialize store
   */
  function init() {
    loadUserFlags();
    loadGlobalFlags();
  }

  return {
    isFeatureEnabled,
    setFeatureFlag,
    loadUserFlags,
    loadGlobalFlags,
    loadProjectFlags,
    init,
  };
});
