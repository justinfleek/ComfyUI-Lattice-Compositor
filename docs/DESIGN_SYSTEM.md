# Weyl Compositor Design System

**Version:** 1.0 | **Date:** December 20, 2024

This document defines the complete design system for the Weyl Compositor UI. All components MUST use these CSS variables - never hardcode colors or spacing values.

---

## Design Philosophy

### "Dense Islands, Empty Ocean"

The UI follows a **floating island architecture**:
- Content-rich panels float on a dark void background
- Generous 20px gutters between panels
- Rounded corners (8px) with soft shadows
- No visible borders - depth conveyed through shadows only
- Creates clear visual hierarchy and reduces cognitive load

---

## Color Tokens

### Surface Hierarchy (5 Levels)

```css
--weyl-void: #050505;        /* App background - THE DARKEST */
--weyl-surface-0: #0A0A0A;   /* Canvas background */
--weyl-surface-1: #121212;   /* Panel backgrounds */
--weyl-surface-2: #1A1A1A;   /* Cards, raised sections */
--weyl-surface-3: #222222;   /* Dropdowns, tooltips */
--weyl-surface-4: #2A2A2A;   /* Highest elevation */
```

### Accent Colors (Purple/Pink Gradient)

```css
--weyl-accent: #8B5CF6;           /* Primary purple */
--weyl-accent-secondary: #EC4899; /* Secondary pink */
--weyl-accent-gradient: linear-gradient(135deg, #8B5CF6, #EC4899);
--weyl-accent-hover: #A78BFA;     /* Lighter purple for hover */
--weyl-accent-muted: rgba(139, 92, 246, 0.2);  /* For backgrounds */
```

### Text Colors

```css
--weyl-text-primary: #E5E5E5;     /* Main text */
--weyl-text-secondary: #9CA3AF;   /* Labels, descriptions */
--weyl-text-muted: #6B7280;       /* Disabled, hints */
--weyl-text-inverse: #050505;     /* Text on light backgrounds */
```

### Border Colors

```css
--weyl-border-subtle: #2A2A2A;    /* Subtle dividers */
--weyl-border-default: #333333;   /* Normal borders */
--weyl-border-hover: #444444;     /* Hover state */
```

### Status Colors

```css
--weyl-success: #10B981;          /* Success green */
--weyl-warning: #F59E0B;          /* Warning amber */
--weyl-error: #EF4444;            /* Error red */
--weyl-info: #3B82F6;             /* Info blue */
```

---

## Spacing Tokens

```css
--weyl-gutter: 20px;              /* Panel separation */
--weyl-gap-xl: 24px;              /* Extra large gaps */
--weyl-gap-lg: 16px;              /* Large gaps */
--weyl-gap-md: 8px;               /* Medium gaps */
--weyl-gap-sm: 4px;               /* Small gaps */
--weyl-gap-xs: 2px;               /* Extra small gaps */
```

---

## Border Radius Tokens

```css
--weyl-radius-xs: 2px;            /* Inputs, small elements */
--weyl-radius-sm: 4px;            /* Buttons, chips */
--weyl-radius-md: 6px;            /* Cards, dropdowns */
--weyl-radius-lg: 8px;            /* Panels */
--weyl-radius-xl: 12px;           /* Large cards */
--weyl-radius-pill: 999px;        /* Pills, fully rounded */
```

---

## Shadow Tokens

```css
--weyl-shadow-sm: 0 1px 2px rgba(0,0,0,0.2);
--weyl-shadow-md: 0 4px 8px rgba(0,0,0,0.3);
--weyl-shadow-lg: 0 8px 16px rgba(0,0,0,0.4);
--weyl-shadow-panel: 0 8px 32px rgba(0,0,0,0.4);
--weyl-shadow-dropdown: 0 4px 12px rgba(0,0,0,0.3);
--weyl-shadow-button: 0 2px 4px rgba(0,0,0,0.2);
```

---

## Typography

### Font Stack

```css
--weyl-font-sans: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
--weyl-font-mono: 'JetBrains Mono', 'Fira Code', monospace;
```

### Font Sizes

```css
--weyl-text-xs: 10px;
--weyl-text-sm: 12px;
--weyl-text-base: 14px;
--weyl-text-lg: 16px;
--weyl-text-xl: 18px;
--weyl-text-2xl: 24px;
```

### Font Weights

```css
--weyl-font-normal: 400;
--weyl-font-medium: 500;
--weyl-font-semibold: 600;
--weyl-font-bold: 700;
```

---

## 6 Gradient Themes

The app supports 6 switchable color themes via `themeStore.ts`:

| Theme | Primary | Secondary | CSS Class |
|-------|---------|-----------|-----------|
| **Violet** (default) | `#8B5CF6` | `#EC4899` | `.theme-violet` |
| **Ocean** | `#06B6D4` | `#3B82F6` | `.theme-ocean` |
| **Sunset** | `#F59E0B` | `#EF4444` | `.theme-sunset` |
| **Forest** | `#10B981` | `#06B6D4` | `.theme-forest` |
| **Ember** | `#EF4444` | `#F97316` | `.theme-ember` |
| **Mono** | `#6B7280` | `#9CA3AF` | `.theme-mono` |

### Theme Usage

```typescript
import { useThemeStore } from '@/stores/themeStore';

const themeStore = useThemeStore();
themeStore.setTheme('ocean'); // Switch to ocean theme
```

---

## Component Patterns

### Panel Component

```vue
<template>
  <div class="weyl-panel">
    <div class="weyl-panel-header">
      <h3>Panel Title</h3>
    </div>
    <div class="weyl-panel-content">
      <!-- Content -->
    </div>
  </div>
</template>

<style scoped>
.weyl-panel {
  background: var(--weyl-surface-1);
  border-radius: var(--weyl-radius-lg);
  box-shadow: var(--weyl-shadow-panel);
}

.weyl-panel-header {
  padding: var(--weyl-gap-md) var(--weyl-gap-lg);
  border-bottom: 1px solid var(--weyl-border-subtle);
}

.weyl-panel-content {
  padding: var(--weyl-gap-lg);
}
</style>
```

### Button Variants

```css
/* Primary Button */
.weyl-btn-primary {
  background: var(--weyl-accent-gradient);
  color: white;
  border: none;
  border-radius: var(--weyl-radius-sm);
  padding: var(--weyl-gap-sm) var(--weyl-gap-md);
}

/* Secondary Button */
.weyl-btn-secondary {
  background: var(--weyl-surface-2);
  color: var(--weyl-text-primary);
  border: 1px solid var(--weyl-border-default);
}

/* Ghost Button */
.weyl-btn-ghost {
  background: transparent;
  color: var(--weyl-text-secondary);
  border: none;
}
```

### Input Styling

```css
.weyl-input {
  background: var(--weyl-surface-2);
  border: 1px solid var(--weyl-border-default);
  border-radius: var(--weyl-radius-xs);
  color: var(--weyl-text-primary);
  padding: var(--weyl-gap-sm) var(--weyl-gap-md);
}

.weyl-input:focus {
  border-color: var(--weyl-accent);
  outline: none;
  box-shadow: 0 0 0 2px var(--weyl-accent-muted);
}
```

---

## Semantic Keyframe Shapes

16 unique SVG shapes map to easing types for instant visual recognition:

| Shape | Easing Type | SVG Path |
|-------|-------------|----------|
| Diamond (◆) | Linear | `M0,-6 L6,0 L0,6 L-6,0 Z` |
| Circle | Hold/Step | `circle r=5` |
| Triangle | Ease In | `M0,-6 L6,6 L-6,6 Z` |
| Inverted Triangle | Ease Out | `M-6,-6 L6,-6 L0,6 Z` |
| Hourglass | Ease In-Out | Two triangles |
| Star (5-point) | Bounce | Star path |
| Octagon | Elastic | 8-sided polygon |
| Pentagon | Cubic | 5-sided polygon |
| Hexagon | Expo | 6-sided polygon |
| Sparkle | Back | 4-pointed star |
| Pill | Bezier (custom) | Rounded rectangle |
| Double Diamond | Sine | Two diamonds |
| Slash Diamond | Circ | Rotated diamond |
| Arrow Diamond | Quint | Diamond with arrow |
| Cross | Spring | Plus shape |
| Square | Generic ease | `rect` |

Defined in `styles/keyframe-shapes.ts`.

---

## Color Reference Quick Guide

| Purpose | Variable | Hex |
|---------|----------|-----|
| App background | `--weyl-void` | `#050505` |
| Canvas background | `--weyl-surface-0` | `#0A0A0A` |
| Panel backgrounds | `--weyl-surface-1` | `#121212` |
| Raised elements | `--weyl-surface-2` | `#1A1A1A` |
| Dropdowns | `--weyl-surface-3` | `#222222` |
| Primary accent | `--weyl-accent` | `#8B5CF6` |
| Secondary accent | `--weyl-accent-secondary` | `#EC4899` |
| Main text | `--weyl-text-primary` | `#E5E5E5` |
| Secondary text | `--weyl-text-secondary` | `#9CA3AF` |
| Muted text | `--weyl-text-muted` | `#6B7280` |

---

## File Locations

| File | Purpose |
|------|---------|
| `ui/src/styles/design-tokens.css` | CSS custom properties |
| `ui/src/styles/keyframe-shapes.ts` | Keyframe SVG definitions |
| `ui/src/stores/themeStore.ts` | Theme state management |
| `ui/src/components/ui/ThemeSelector.vue` | Theme picker component |

---

## Migration Notes

### Deprecated Colors (Do Not Use)

| Old Value | Replacement |
|-----------|-------------|
| `#1a1a2e` | `var(--weyl-void)` or `#050505` |
| `#16213e` | `var(--weyl-surface-0)` or `#0A0A0A` |
| `#1a1a38` | `var(--weyl-surface-1)` or `#121212` |

### December 2024 Migration

All hardcoded `#1a1a2e` colors were replaced with `#050505` in:
- `types/project.ts`
- `compositorStore.ts`
- `ThreeCanvas.vue`
- `ExportPanel.vue`
- `extension.js`
- `WeylEngine.ts`

---

**Document Version:** 1.0
**Last Updated:** December 20, 2024
