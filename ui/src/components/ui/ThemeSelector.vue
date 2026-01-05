<template>
  <div class="theme-selector">
    <div class="theme-label">Theme</div>
    <div class="theme-grid">
      <button
        v-for="theme in themes"
        :key="theme.name"
        class="theme-swatch"
        :class="{ active: currentTheme === theme.name }"
        :style="{ background: theme.gradient }"
        :title="theme.label"
        @click="setTheme(theme.name)"
      >
        <span class="theme-check" v-if="currentTheme === theme.name">
          <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3">
            <polyline points="20 6 9 17 4 12"></polyline>
          </svg>
        </span>
      </button>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { type ThemeName, useThemeStore } from "@/stores/themeStore";

const themeStore = useThemeStore();

const _currentTheme = computed(() => themeStore.currentTheme);

const _themes: Array<{ name: ThemeName; label: string; gradient: string }> = [
  {
    name: "violet",
    label: "Violet",
    gradient: "linear-gradient(135deg, #8B5CF6, #EC4899)",
  },
  {
    name: "ocean",
    label: "Ocean",
    gradient: "linear-gradient(135deg, #06B6D4, #3B82F6)",
  },
  {
    name: "sunset",
    label: "Sunset",
    gradient: "linear-gradient(135deg, #F59E0B, #EF4444)",
  },
  {
    name: "forest",
    label: "Forest",
    gradient: "linear-gradient(135deg, #10B981, #06B6D4)",
  },
  {
    name: "ember",
    label: "Ember",
    gradient: "linear-gradient(135deg, #EF4444, #F97316)",
  },
  {
    name: "mono",
    label: "Mono",
    gradient: "linear-gradient(135deg, #4B5563, #6B7280)",
  },
];

function _setTheme(theme: ThemeName) {
  themeStore.setTheme(theme);
}
</script>

<style scoped>
.theme-selector {
  padding: 12px;
}

.theme-label {
  font-size: var(--lattice-text-xs, 10px);
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--lattice-text-muted, #6B7280);
  margin-bottom: 8px;
}

.theme-grid {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: 8px;
}

.theme-swatch {
  aspect-ratio: 1;
  border: none;
  border-radius: var(--lattice-radius-md, 4px);
  cursor: pointer;
  transition: var(--lattice-transition-fast, 100ms ease);
  position: relative;
  display: flex;
  align-items: center;
  justify-content: center;
}

.theme-swatch:hover {
  transform: scale(1.05);
  box-shadow: var(--lattice-shadow-md, 0 4px 8px rgba(0,0,0,0.25));
}

.theme-swatch.active {
  box-shadow: 0 0 0 2px var(--lattice-void, #050505), 0 0 0 4px white;
}

.theme-check {
  color: white;
  filter: drop-shadow(0 1px 2px rgba(0,0,0,0.5));
}
</style>
