# Feature Flags System

> **Purpose:** Modular feature toggling system for Lattice Compositor
> **Status:** 🏗️ FOUNDATION DESIGN
> **Last Updated:** 2026-01-23

**CRITICAL:** All features must be behind feature flags. Features can be toggled:
1. **Globally** (affects all projects)
2. **Per Project** (project-specific overrides)
3. **Per User** (user preferences)
4. **Via UI** (toggle switches in preferences)

---

## Feature Flag Architecture

```
┌─────────────────────────────────────────────────────────────┐
│              Feature Flag Sources (Priority Order)          │
├─────────────────────────────────────────────────────────────┤
│  1. User Preferences (highest priority)                    │
│  2. Project Settings (project.feature_flags JSON)           │
│  3. Global Defaults (feature_flags table)                   │
│  4. Code Defaults (fallback)                                │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│           Feature Flag Resolver (Haskell/TypeScript)        │
│  - Checks user → project → global → code defaults            │
│  - Returns boolean for each feature                          │
└─────────────────────────────────────────────────────────────┘
                          │
        ┌─────────────────┴─────────────────┐
        ▼                                   ▼
┌──────────────────┐            ┌──────────────────────┐
│   UI Components  │            │   Backend Services   │
│   (Conditional)   │            │   (Conditional)     │
└──────────────────┘            └──────────────────────┘
```

---

## Database Schema

**Table:** `feature_flags`

```sql
CREATE TABLE feature_flags (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL UNIQUE,
    description TEXT NOT NULL,
    enabled_by_default BOOLEAN NOT NULL DEFAULT false,
    category TEXT NOT NULL,  -- 'ui' | 'engine' | 'export' | 'ai' | 'experimental'
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
);
```

**Project Override:** `projects.feature_flags` (JSON column)

```json
{
  "ff-particles-enabled": true,
  "ff-physics-enabled": false,
  "ff-experimental-mesh-warp": true
}
```

---

## Feature Flag Categories

### UI Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-ui-particles` | Show particle system UI | `true` | `components/properties/ParticleProperties.vue` |
| `ff-ui-physics` | Show physics UI | `true` | `components/properties/PhysicsProperties.vue` |
| `ff-ui-camera` | Show camera UI | `true` | `components/properties/CameraProperties.vue` |
| `ff-ui-audio` | Show audio panel | `true` | `components/panels/AudioPanel.vue` |
| `ff-ui-ai-chat` | Show AI chat panel | `true` | `components/panels/AIChatPanel.vue` |
| `ff-ui-timeline` | Show timeline panel | `true` | `components/timeline/TimelinePanel.vue` |

### Engine Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-engine-webgpu` | Use WebGPU renderer | `true` | `engine/particles/VerifiedWebGPUCompute.ts` |
| `ff-engine-webgl` | Use WebGL renderer (fallback) | `true` | `engine/core/RenderPipeline.ts` |
| `ff-engine-motion-blur` | Enable motion blur | `false` | `services/motionBlur.ts` |

### Export Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-export-h264` | Enable H.264 export | `true` | `services/export/videoEncoder.ts` |
| `ff-export-prores` | Enable ProRes export | `false` | `services/export/videoEncoder.ts` |
| `ff-export-webm` | Enable WebM export | `true` | `services/export/videoEncoder.ts` |
| `ff-export-camera` | Enable camera export formats | `true` | `services/export/cameraExport.ts` |

### AI Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-ai-chat` | Enable AI chat | `true` | `components/panels/AIChatPanel.vue` |
| `ff-ai-generation` | Enable AI generation | `true` | `services/aiGeneration.ts` |
| `ff-ai-segmentation` | Enable AI segmentation | `true` | `services/segmentation.ts` |
| `ff-ai-vectorization` | Enable AI vectorization | `true` | `services/vectorize.ts` |

### Particle Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-particles-enabled` | Enable particle systems | `true` | `engine/particles/GPUParticleSystem.ts` |
| `ff-particles-gpu` | Use GPU acceleration | `true` | `engine/particles/VerifiedWebGPUCompute.ts` |
| `ff-particles-sph` | Enable SPH fluid simulation | `false` | `engine/particles/GPUSPHSystem.ts` |
| `ff-particles-flocking` | Enable flocking behavior | `true` | `engine/particles/ParticleFlockingSystem.ts` |

### Physics Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-physics-enabled` | Enable physics simulation | `true` | `services/physics/PhysicsEngine.ts` |
| `ff-physics-ragdoll` | Enable ragdoll physics | `false` | `services/physics/RagdollBuilder.ts` |
| `ff-physics-joints` | Enable joint system | `true` | `services/physics/JointSystem.ts` |

### Experimental Features

| Flag Name | Description | Default | Files Affected |
|-----------|-------------|---------|----------------|
| `ff-experimental-mesh-warp` | Enable mesh warp deformation | `false` | `services/meshWarpDeformation.ts` |
| `ff-experimental-gaussian-splatting` | Enable Gaussian splatting | `false` | `services/gaussianSplatting.ts` |
| `ff-experimental-depthflow` | Enable depth flow | `false` | `services/depthflow.ts` |

---

## Implementation

### TypeScript (UI Layer)

**File:** `ui/src/stores/featureFlagsStore.ts`

```typescript
import { defineStore } from 'pinia';
import { ref, computed } from 'vue';

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
    // Persist to localStorage or backend
  }

  /**
   * Load global feature flags from database
   */
  async function loadGlobalFlags() {
    // Query feature_flags table
    const flags = await queryDatabase('SELECT name, enabled_by_default FROM feature_flags');
    globalFlags.value = Object.fromEntries(
      flags.map((f: { name: string; enabled_by_default: boolean }) => [
        f.name,
        f.enabled_by_default,
      ])
    );
  }

  /**
   * Load project-specific feature flags
   */
  async function loadProjectFlags(projectId: string) {
    const project = await queryDatabase(
      'SELECT feature_flags FROM projects WHERE id = ?',
      [projectId]
    );
    if (project && project.feature_flags) {
      projectFlags.value = JSON.parse(project.feature_flags);
    }
  }

  return {
    isFeatureEnabled,
    setFeatureFlag,
    loadGlobalFlags,
    loadProjectFlags,
  };
});
```

**Usage in Components:**

```vue
<script setup lang="ts">
import { useFeatureFlagsStore } from '@/stores/featureFlagsStore';

const featureFlags = useFeatureFlagsStore();

// Conditional rendering
const showParticles = computed(() => 
  featureFlags.isFeatureEnabled('ff-ui-particles', true)
);
</script>

<template>
  <ParticleProperties v-if="showParticles" />
</template>
```

---

### Haskell (Backend Layer)

**File:** `src/lattice/Services/FeatureFlags.hs`

```haskell
module Lattice.Services.FeatureFlags where

import Data.Aeson (Value, Object, (.=), object, (.:?), (.:))
import Data.Text (Text)
import Database.DuckDB (Connection, query)

data FeatureFlag = FeatureFlag
  { flagName :: Text
  , flagDescription :: Text
  , flagEnabledByDefault :: Bool
  , flagCategory :: Text
  }

-- Check if feature is enabled
-- Priority: user > project > global > code default
isFeatureEnabled ::
  Connection ->
  Maybe Text ->  -- User ID (optional)
  Maybe Text ->  -- Project ID (optional)
  Text ->        -- Flag name
  Bool ->        -- Code default
  IO Bool
isFeatureEnabled conn mUserId mProjectId flagName codeDefault = do
  -- Check user override (if user ID provided)
  case mUserId of
    Just userId -> do
      userFlag <- queryUserFlag conn userId flagName
      case userFlag of
        Just enabled -> return enabled
        Nothing -> checkProjectOrGlobal
    Nothing -> checkProjectOrGlobal
  where
    checkProjectOrGlobal = do
      -- Check project override (if project ID provided)
      case mProjectId of
        Just projectId -> do
          projectFlag <- queryProjectFlag conn projectId flagName
          case projectFlag of
            Just enabled -> return enabled
            Nothing -> checkGlobal
        Nothing -> checkGlobal
    
    checkGlobal = do
      -- Check global default
      globalFlag <- queryGlobalFlag conn flagName
      case globalFlag of
        Just enabled -> return enabled
        Nothing -> return codeDefault

-- Query user-specific flag
queryUserFlag :: Connection -> Text -> Text -> IO (Maybe Bool)
queryUserFlag conn userId flagName = do
  -- Query user_feature_flags table (if exists)
  -- For now, return Nothing (not implemented)
  return Nothing

-- Query project-specific flag
queryProjectFlag :: Connection -> Text -> Text -> IO (Maybe Bool)
queryProjectFlag conn projectId flagName = do
  result <- query conn
    "SELECT json_extract(feature_flags, ?) FROM projects WHERE id = ?"
    [flagName, projectId]
  case result of
    [value] -> return (Just (value == "true"))
    _ -> return Nothing

-- Query global flag default
queryGlobalFlag :: Connection -> Text -> IO (Maybe Bool)
queryGlobalFlag conn flagName = do
  result <- query conn
    "SELECT enabled_by_default FROM feature_flags WHERE name = ?"
    [flagName]
  case result of
    [enabled] -> return (Just enabled)
    _ -> return Nothing
```

---

## UI Toggle Component

**File:** `ui/src/components/preferences/FeatureFlagsPanel.vue`

```vue
<template>
  <div class="feature-flags-panel">
    <h2>Feature Flags</h2>
    
    <div v-for="category in categories" :key="category.name" class="category">
      <h3>{{ category.name }}</h3>
      
      <div v-for="flag in category.flags" :key="flag.name" class="flag-item">
        <label>
          <input
            type="checkbox"
            :checked="isEnabled(flag.name)"
            @change="toggleFlag(flag.name, $event.target.checked)"
          />
          <span class="flag-name">{{ flag.name }}</span>
        </label>
        <p class="flag-description">{{ flag.description }}</p>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { useFeatureFlagsStore } from '@/stores/featureFlagsStore';
import { computed } from 'vue';

const featureFlags = useFeatureFlagsStore();

const categories = computed(() => [
  {
    name: 'UI Features',
    flags: [
      { name: 'ff-ui-particles', description: 'Show particle system UI' },
      { name: 'ff-ui-physics', description: 'Show physics UI' },
      // ... more flags
    ],
  },
  {
    name: 'Engine Features',
    flags: [
      { name: 'ff-engine-webgpu', description: 'Use WebGPU renderer' },
      // ... more flags
    ],
  },
  // ... more categories
]);

function isEnabled(flagName: string): boolean {
  return featureFlags.isFeatureEnabled(flagName, false);
}

function toggleFlag(flagName: string, enabled: boolean) {
  featureFlags.setFeatureFlag(flagName, enabled);
}
</script>
```

---

## Database Initialization

**File:** `scripts/init-feature-flags.sql`

```sql
-- Insert default feature flags
INSERT INTO feature_flags (id, name, description, enabled_by_default, category) VALUES
    ('ff-ui-particles', 'UI: Particles', 'Show particle system UI', true, 'ui'),
    ('ff-ui-physics', 'UI: Physics', 'Show physics UI', true, 'ui'),
    ('ff-ui-camera', 'UI: Camera', 'Show camera UI', true, 'ui'),
    ('ff-ui-audio', 'UI: Audio', 'Show audio panel', true, 'ui'),
    ('ff-ui-ai-chat', 'UI: AI Chat', 'Show AI chat panel', true, 'ui'),
    
    ('ff-engine-webgpu', 'Engine: WebGPU', 'Use WebGPU renderer', true, 'engine'),
    ('ff-engine-webgl', 'Engine: WebGL', 'Use WebGL renderer (fallback)', true, 'engine'),
    ('ff-engine-motion-blur', 'Engine: Motion Blur', 'Enable motion blur', false, 'engine'),
    
    ('ff-export-h264', 'Export: H.264', 'Enable H.264 export', true, 'export'),
    ('ff-export-prores', 'Export: ProRes', 'Enable ProRes export', false, 'export'),
    ('ff-export-webm', 'Export: WebM', 'Enable WebM export', true, 'export'),
    
    ('ff-ai-chat', 'AI: Chat', 'Enable AI chat', true, 'ai'),
    ('ff-ai-generation', 'AI: Generation', 'Enable AI generation', true, 'ai'),
    ('ff-ai-segmentation', 'AI: Segmentation', 'Enable AI segmentation', true, 'ai'),
    
    ('ff-particles-enabled', 'Particles: Enabled', 'Enable particle systems', true, 'particles'),
    ('ff-particles-gpu', 'Particles: GPU', 'Use GPU acceleration', true, 'particles'),
    ('ff-particles-sph', 'Particles: SPH', 'Enable SPH fluid simulation', false, 'particles'),
    
    ('ff-physics-enabled', 'Physics: Enabled', 'Enable physics simulation', true, 'physics'),
    ('ff-physics-ragdoll', 'Physics: Ragdoll', 'Enable ragdoll physics', false, 'physics'),
    
    ('ff-experimental-mesh-warp', 'Experimental: Mesh Warp', 'Enable mesh warp deformation', false, 'experimental'),
    ('ff-experimental-gaussian-splatting', 'Experimental: Gaussian Splatting', 'Enable Gaussian splatting', false, 'experimental');
```

---

## Migration from Current System

**Current:** Hard-coded feature checks in components

**Target:** Feature flag system with database

**Steps:**
1. Create `feature_flags` table
2. Insert default flags
3. Create `featureFlagsStore.ts`
4. Update components to use `isFeatureEnabled()`
5. Add UI toggle panel
6. Migrate existing toggles to feature flags

---

## Related Documents

- `docs/DATABASE_SCHEMA.md` - Database schema (feature_flags table)
- `docs/MCP_SERVER_CONFIG.md` - MCP server exposes feature flags
- `docs/LITERATE_PROGRAMMING_MAPPING.md` - Code-to-feature-flag mapping

---

*Feature Flags System Version: 1.0*
*Last Updated: 2026-01-23*
