# UI Implementation Plan

Step-by-step plan to incorporate the new design system into the existing Weyl codebase.

---

## Phase 1: Foundation (Non-Breaking)

### 1.1 Import Design Tokens

Add the design tokens CSS to the app entry point:

**File:** `ui/src/main.ts`
```typescript
import './styles/design-tokens.css';
```

**File:** `ui/src/App.vue` or root component
```css
body {
  background: var(--weyl-void);
  font-family: var(--weyl-font-sans);
  color: var(--weyl-text-primary);
}
```

### 1.2 Add Keyframe Shapes Service

**Files to create:**
- `ui/src/styles/keyframe-shapes.ts` (already exists)

**Integration point:** Import into `PropertyTrack.vue`, `GraphEditorCanvas.vue`

### 1.3 Theme Selector Store

**File:** `ui/src/stores/themeStore.ts`

```typescript
import { defineStore } from 'pinia';

export type ThemeName = 'violet' | 'ocean' | 'sunset' | 'forest' | 'ember' | 'mono';

export const useThemeStore = defineStore('theme', {
  state: () => ({
    currentTheme: 'violet' as ThemeName
  }),
  actions: {
    setTheme(theme: ThemeName) {
      this.currentTheme = theme;
      document.documentElement.style.setProperty(
        '--weyl-accent',
        `var(--weyl-theme-${theme}-primary)`
      );
      document.documentElement.style.setProperty(
        '--weyl-accent-secondary',
        `var(--weyl-theme-${theme}-secondary)`
      );
      document.documentElement.style.setProperty(
        '--weyl-accent-gradient',
        `var(--weyl-theme-${theme}-gradient)`
      );
    }
  }
});
```

---

## Phase 2: Panel Layout Conversion

### 2.1 WorkspaceLayout.vue Updates

**Current:** Fixed grid with borders
**Target:** Floating panels with gutters

```vue
<template>
  <div class="workspace" :style="{ background: 'var(--weyl-void)' }">
    <div class="panel-container" :style="panelStyle">
      <!-- Panels float inside container -->
    </div>
  </div>
</template>

<style scoped>
.workspace {
  padding: var(--weyl-gutter);
  display: grid;
  gap: var(--weyl-gutter);
}

.panel {
  background: var(--weyl-surface-1);
  border-radius: var(--weyl-radius-xl);
  box-shadow: var(--weyl-shadow-panel);
  border: none;
}
</style>
```

### 2.2 Panel Components to Update

| Component | Changes |
|-----------|---------|
| `ProjectPanel.vue` | Add `.floating-panel` class, remove borders |
| `PropertiesPanel.vue` | Add `.floating-panel` class, remove borders |
| `TimelinePanel.vue` | Add `.floating-panel` class, remove borders |
| `PreviewPanel.vue` | Add `.floating-panel` class, remove borders |
| `AudioPanel.vue` | Add `.floating-panel` class, remove borders |
| `EffectControlsPanel.vue` | Add `.floating-panel` class, remove borders |

---

## Phase 3: Timeline Node System

### 3.1 Data Model Extensions

**File:** `ui/src/types/project.ts`

Add node connection types:

```typescript
interface ConnectionPort {
  id: string;
  name: string;
  type: 'visual' | 'parameter' | 'modifier';
  direction: 'input' | 'output';
}

interface NodeConnection {
  id: string;
  sourceNode: string;
  sourcePort: string;
  targetNode: string;
  targetPort: string;
  type: 'visual' | 'parameter' | 'modifier';
}

interface TimelineNode {
  id: string;
  type: 'clip' | 'effect' | 'parameter' | 'modifier';
  name: string;
  inputs: ConnectionPort[];
  outputs: ConnectionPort[];
  position: { x: number; y: number }; // For expanded view
  parameters: Record<string, any>;
}
```

### 3.2 Connection Rendering Component

**File:** `ui/src/components/timeline/NodeConnection.vue`

```vue
<template>
  <svg class="connection-layer">
    <defs>
      <linearGradient :id="gradientId">
        <stop offset="0%" :stop-color="startColor" />
        <stop offset="100%" :stop-color="endColor" />
      </linearGradient>
    </defs>
    <path
      :d="bezierPath"
      :stroke="connectionType === 'visual' ? `url(#${gradientId})` : color"
      :stroke-width="connectionType === 'visual' ? 3 : 1"
      :stroke-dasharray="connectionType === 'modifier' ? '4,4' : 'none'"
      fill="none"
    />
  </svg>
</template>
```

### 3.3 Timeline Integration

**Files to modify:**
- `TimelinePanel.vue` - Add connection layer behind tracks
- `EnhancedLayerTrack.vue` - Add connection ports to clips
- `compositorStore.ts` - Add `connections: NodeConnection[]` to state

### 3.4 Expanded Node View

**File:** `ui/src/components/timeline/NodeGraphView.vue`

New component for full node graph editing when track is expanded.

---

## Phase 4: Keyframe Shape Integration

### 4.1 PropertyTrack.vue Updates

Replace diamond icons with semantic shapes:

```typescript
import { getShapeForEasing, KEYFRAME_SHAPES } from '@/styles/keyframe-shapes';

// In keyframe rendering
const shape = getShapeForEasing(keyframe.easing);
```

### 4.2 Graph Editor Updates

**File:** `GraphEditorCanvas.vue`

Add keyframe shape legend and render appropriate shapes.

---

## Phase 5: Component Styling Migration

### 5.1 Button Styles

**File:** `ui/src/components/ui/WeylButton.vue` (new)

```vue
<template>
  <button :class="['weyl-btn', variant, size]">
    <slot />
  </button>
</template>

<style scoped>
.weyl-btn {
  font-family: var(--weyl-font-sans);
  font-size: var(--weyl-text-sm);
  border-radius: var(--weyl-radius-md);
  transition: var(--weyl-transition-fast);
}

.weyl-btn.primary {
  background: var(--weyl-accent-gradient);
  color: white;
}

.weyl-btn.ghost {
  background: transparent;
  color: var(--weyl-text-secondary);
}

.weyl-btn.ghost:hover {
  background: var(--weyl-surface-3);
  color: var(--weyl-text-primary);
}
</style>
```

### 5.2 Input Styles

**File:** `ui/src/components/ui/WeylInput.vue` (new)

### 5.3 Slider Styles

Update sliders to use gradient fill.

---

## Phase 6: Theme Selector UI

### 6.1 Settings Panel Addition

**File:** `ui/src/components/dialogs/SettingsDialog.vue`

Add theme selector grid:

```vue
<template>
  <div class="theme-grid">
    <button
      v-for="theme in themes"
      :key="theme.name"
      :class="['theme-swatch', { active: currentTheme === theme.name }]"
      :style="{ background: theme.gradient }"
      @click="setTheme(theme.name)"
    />
  </div>
</template>
```

---

## Phase 7: Polish & Animation

### 7.1 Transition Classes

Add utility classes for consistent animations:

```css
.weyl-fade-enter-active,
.weyl-fade-leave-active {
  transition: opacity var(--weyl-transition-normal);
}

.weyl-slide-enter-active,
.weyl-slide-leave-active {
  transition: transform var(--weyl-transition-normal);
}
```

### 7.2 Hover States

Ensure all interactive elements have hover feedback using `--weyl-surface-3`.

### 7.3 Focus States

Add consistent focus rings using `.focus-ring` class.

---

## Migration Checklist

### Phase 1: Foundation
- [ ] Import design-tokens.css in main.ts
- [ ] Set body background to --weyl-void
- [ ] Create themeStore.ts
- [ ] Add theme persistence to localStorage

### Phase 2: Panels
- [ ] Update WorkspaceLayout.vue grid to use gutters
- [ ] Add .floating-panel class to all panel components
- [ ] Remove all panel borders
- [ ] Add panel shadows

### Phase 3: Node Timeline
- [ ] Add NodeConnection type to project.ts
- [ ] Create NodeConnection.vue component
- [ ] Add connections array to compositorStore
- [ ] Render connections in TimelinePanel
- [ ] Add connection ports to clips
- [ ] Create NodeGraphView.vue for expanded mode

### Phase 4: Keyframes
- [ ] Import keyframe-shapes.ts in PropertyTrack.vue
- [ ] Replace keyframe icons with semantic shapes
- [ ] Add shape legend to GraphEditorCanvas

### Phase 5: Components
- [ ] Create WeylButton.vue
- [ ] Create WeylInput.vue
- [ ] Update slider components with gradient fill
- [ ] Update toggle components

### Phase 6: Theming
- [ ] Add theme selector to settings
- [ ] Wire theme changes to CSS variables
- [ ] Add theme to project save/load

### Phase 7: Polish
- [ ] Add transition utilities
- [ ] Verify all hover states
- [ ] Add focus rings to interactive elements
- [ ] Test keyboard navigation

---

## File Summary

| Action | Files |
|--------|-------|
| **Create** | `themeStore.ts`, `NodeConnection.vue`, `NodeGraphView.vue`, `WeylButton.vue`, `WeylInput.vue` |
| **Modify** | `main.ts`, `WorkspaceLayout.vue`, `TimelinePanel.vue`, `EnhancedLayerTrack.vue`, `PropertyTrack.vue`, `GraphEditorCanvas.vue`, `project.ts`, `compositorStore.ts`, 6 panel components |
| **Already Done** | `design-tokens.css`, `keyframe-shapes.ts`, `NODE_TIMELINE_SPEC.md`, `UI_MIGRATION_PLAN.md` |

---

## Backward Compatibility

All changes are additive. Existing projects will:
- Use default Violet theme
- Show connections as hidden (collapsed view default)
- Render old keyframe shapes until easing type detected

No breaking changes to:
- Project file format
- ComfyUI integration
- Export functionality
- Keyboard shortcuts
