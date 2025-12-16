<template>
  <div class="effects-panel">
    <div class="panel-header">
      <span class="panel-title">Effects & Presets</span>
      <div class="header-actions">
        <input
          type="text"
          v-model="searchQuery"
          placeholder="Search..."
          class="search-input"
        />
      </div>
    </div>

    <div class="panel-content">
      <!-- Tabs -->
      <div class="tabs">
        <button
          :class="{ active: activeTab === 'effects' }"
          @click="activeTab = 'effects'"
        >
          Effects
        </button>
        <button
          :class="{ active: activeTab === 'presets' }"
          @click="activeTab = 'presets'"
        >
          Presets
        </button>
        <button
          :class="{ active: activeTab === 'favorites' }"
          @click="activeTab = 'favorites'"
        >
          Favorites
        </button>
      </div>

      <!-- Effects List -->
      <div v-if="activeTab === 'effects'" class="effects-list">
        <div
          v-for="category in filteredCategories"
          :key="category.key"
          class="effect-category"
        >
          <div
            class="category-header"
            @click="toggleCategory(category.key)"
          >
            <span class="expand-icon">{{ expandedCategories.includes(category.key) ? '▼' : '►' }}</span>
            <span class="category-icon">{{ category.icon }}</span>
            <span class="category-name">{{ category.label }}</span>
            <span class="effect-count">{{ category.effects.length }}</span>
          </div>

          <div v-if="expandedCategories.includes(category.key)" class="category-effects">
            <div
              v-for="effect in category.effects"
              :key="effect.key"
              class="effect-item"
              :class="{ favorite: favorites.includes(effect.key) }"
              @dblclick="applyEffect(effect.key)"
              @dragstart="onDragStart(effect.key, $event)"
              draggable="true"
            >
              <span class="effect-name">{{ effect.name }}</span>
              <button
                class="favorite-btn"
                @click.stop="toggleFavorite(effect.key)"
                :title="favorites.includes(effect.key) ? 'Remove from favorites' : 'Add to favorites'"
              >
                {{ favorites.includes(effect.key) ? '★' : '☆' }}
              </button>
            </div>
          </div>
        </div>
      </div>

      <!-- Animation Presets -->
      <div v-else-if="activeTab === 'presets'" class="presets-list">
        <div
          v-for="group in groupedPresets"
          :key="group.category"
          class="preset-category"
        >
          <div
            class="category-header"
            @click="togglePresetCategory(group.category)"
          >
            <span class="expand-icon">{{ expandedPresetCategories.includes(group.category) ? '▼' : '►' }}</span>
            <span class="category-name">{{ group.category }}</span>
            <span class="preset-count">{{ group.presets.length }}</span>
          </div>

          <div v-if="expandedPresetCategories.includes(group.category)" class="category-presets">
            <div
              v-for="preset in group.presets"
              :key="preset.id"
              class="preset-item"
              @dblclick="applyPreset(preset)"
              @dragstart="onDragPreset(preset, $event)"
              draggable="true"
            >
              <div class="preset-preview">
                <!-- Simple animation preview icon -->
                <span class="preview-icon">▶</span>
              </div>
              <div class="preset-info">
                <span class="preset-name">{{ preset.name }}</span>
                <span class="preset-description">{{ preset.description }}</span>
              </div>
            </div>
          </div>
        </div>
      </div>

      <!-- Favorites -->
      <div v-else-if="activeTab === 'favorites'" class="favorites-list">
        <div v-if="favoriteEffects.length === 0" class="empty-favorites">
          <p>No favorites yet</p>
          <p class="hint">Click the star icon on effects to add them here</p>
        </div>
        <div
          v-for="effect in favoriteEffects"
          :key="effect.key"
          class="effect-item"
          @dblclick="applyEffect(effect.key)"
          @dragstart="onDragStart(effect.key, $event)"
          draggable="true"
        >
          <span class="category-badge">{{ getCategoryIcon(effect.category) }}</span>
          <span class="effect-name">{{ effect.name }}</span>
          <button
            class="favorite-btn active"
            @click.stop="toggleFavorite(effect.key)"
          >
            ★
          </button>
        </div>
      </div>
    </div>

    <!-- Quick apply info -->
    <div class="panel-footer">
      <span class="info-text">Double-click or drag to apply</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import {
  EFFECT_DEFINITIONS,
  EFFECT_CATEGORIES,
  ANIMATION_PRESETS,
  createEffect,
  type EffectCategory,
  type AnimationPreset
} from '@/types/effects';

const store = useCompositorStore();

// State
const activeTab = ref<'effects' | 'presets' | 'favorites'>('effects');
const searchQuery = ref('');
const expandedCategories = ref<EffectCategory[]>(['blur-sharpen', 'color-correction']);
const expandedPresetCategories = ref<string[]>(['Fade', 'Scale']);
const favorites = ref<string[]>([]);

// Load favorites from localStorage
onMounted(() => {
  const saved = localStorage.getItem('effect-favorites');
  if (saved) {
    try {
      favorites.value = JSON.parse(saved);
    } catch {
      favorites.value = [];
    }
  }
});

// Save favorites
function saveFavorites() {
  localStorage.setItem('effect-favorites', JSON.stringify(favorites.value));
}

// Computed
const allEffects = computed(() => {
  return Object.entries(EFFECT_DEFINITIONS).map(([key, def]) => ({
    key,
    name: def.name,
    category: def.category,
    description: def.description
  }));
});

const filteredCategories = computed(() => {
  const query = searchQuery.value.toLowerCase();

  return (Object.entries(EFFECT_CATEGORIES) as [EffectCategory, typeof EFFECT_CATEGORIES[EffectCategory]][]).map(([key, cat]) => {
    const effects = allEffects.value.filter(e => {
      if (e.category !== key) return false;
      if (query && !e.name.toLowerCase().includes(query)) return false;
      return true;
    });

    return {
      key,
      label: cat.label,
      icon: cat.icon,
      effects
    };
  }).filter(cat => cat.effects.length > 0);
});

const groupedPresets = computed(() => {
  const query = searchQuery.value.toLowerCase();
  const groups: Record<string, AnimationPreset[]> = {};

  for (const preset of ANIMATION_PRESETS) {
    if (query && !preset.name.toLowerCase().includes(query)) continue;

    if (!groups[preset.category]) {
      groups[preset.category] = [];
    }
    groups[preset.category].push(preset);
  }

  return Object.entries(groups).map(([category, presets]) => ({
    category,
    presets
  }));
});

const favoriteEffects = computed(() => {
  return allEffects.value.filter(e => favorites.value.includes(e.key));
});

// Actions
function toggleCategory(category: EffectCategory) {
  const index = expandedCategories.value.indexOf(category);
  if (index >= 0) {
    expandedCategories.value.splice(index, 1);
  } else {
    expandedCategories.value.push(category);
  }
}

function togglePresetCategory(category: string) {
  const index = expandedPresetCategories.value.indexOf(category);
  if (index >= 0) {
    expandedPresetCategories.value.splice(index, 1);
  } else {
    expandedPresetCategories.value.push(category);
  }
}

function toggleFavorite(effectKey: string) {
  const index = favorites.value.indexOf(effectKey);
  if (index >= 0) {
    favorites.value.splice(index, 1);
  } else {
    favorites.value.push(effectKey);
  }
  saveFavorites();
}

function getCategoryIcon(category: EffectCategory): string {
  return EFFECT_CATEGORIES[category]?.icon || '?';
}

function applyEffect(effectKey: string) {
  const selectedLayer = store.selectedLayer;
  if (!selectedLayer) {
    console.warn('No layer selected to apply effect');
    return;
  }

  // Add effect to layer via store action (use key directly)
  store.addEffectToLayer(selectedLayer.id, effectKey);
}

function applyPreset(preset: AnimationPreset) {
  const selectedLayer = store.selectedLayer;
  if (!selectedLayer) return;

  const comp = store.getActiveComp();
  if (!comp) return;

  // Calculate frame range for preset (use layer duration)
  const startFrame = selectedLayer.inPoint;
  const endFrame = selectedLayer.outPoint;
  const duration = endFrame - startFrame;

  // Apply keyframes from preset to layer properties
  for (const propDef of preset.keyframes) {
    for (const kf of propDef.keyframes) {
      // Convert normalized time (0-1) to frame number
      const frame = Math.round(startFrame + kf.time * duration);
      store.addKeyframe(selectedLayer.id, propDef.property, kf.value, frame);
    }
  }
}

// Drag and drop
function onDragStart(effectKey: string, event: DragEvent) {
  event.dataTransfer?.setData('application/effect', effectKey);
}

function onDragPreset(preset: AnimationPreset, event: DragEvent) {
  event.dataTransfer?.setData('application/preset', JSON.stringify(preset));
}
</script>

<style scoped>
.effects-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 12px;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 12px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
}

.search-input {
  width: 120px;
  padding: 4px 8px;
  border: 1px solid #444;
  background: #1a1a1a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.search-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.panel-content {
  flex: 1;
  overflow: hidden;
  display: flex;
  flex-direction: column;
}

.tabs {
  display: flex;
  background: #222;
  border-bottom: 1px solid #333;
}

.tabs button {
  flex: 1;
  padding: 8px;
  border: none;
  background: transparent;
  color: #888;
  font-size: 11px;
  cursor: pointer;
  border-bottom: 2px solid transparent;
}

.tabs button:hover {
  color: #e0e0e0;
}

.tabs button.active {
  color: #e0e0e0;
  border-bottom-color: #7c9cff;
}

.effects-list,
.presets-list,
.favorites-list {
  flex: 1;
  overflow-y: auto;
}

.effect-category,
.preset-category {
  border-bottom: 1px solid #2a2a2a;
}

.category-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px;
  background: #222;
  cursor: pointer;
  user-select: none;
}

.category-header:hover {
  background: #2a2a2a;
}

.expand-icon {
  font-size: 8px;
  color: #666;
  width: 10px;
}

.category-icon {
  width: 18px;
  height: 18px;
  background: #333;
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 10px;
  color: #7c9cff;
}

.category-name {
  flex: 1;
  font-size: 11px;
}

.effect-count,
.preset-count {
  font-size: 9px;
  color: #666;
  background: #333;
  padding: 2px 6px;
  border-radius: 10px;
}

.category-effects,
.category-presets {
  padding: 4px;
}

.effect-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 8px;
  border-radius: 3px;
  cursor: grab;
}

.effect-item:hover {
  background: #2a2a2a;
}

.effect-item.favorite .effect-name {
  color: #ffc107;
}

.category-badge {
  width: 20px;
  height: 20px;
  background: #333;
  border-radius: 3px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 9px;
  color: #7c9cff;
}

.effect-name {
  flex: 1;
  font-size: 11px;
}

.favorite-btn {
  width: 20px;
  height: 20px;
  border: none;
  background: transparent;
  color: #555;
  cursor: pointer;
  font-size: 12px;
  opacity: 0;
  transition: opacity 0.1s;
}

.effect-item:hover .favorite-btn,
.effect-item.favorite .favorite-btn {
  opacity: 1;
}

.favorite-btn:hover,
.favorite-btn.active {
  color: #ffc107;
}

.preset-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px;
  border-radius: 3px;
  cursor: grab;
}

.preset-item:hover {
  background: #2a2a2a;
}

.preset-preview {
  width: 40px;
  height: 30px;
  background: #333;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.preview-icon {
  color: #7c9cff;
  font-size: 14px;
}

.preset-info {
  flex: 1;
  display: flex;
  flex-direction: column;
  gap: 2px;
}

.preset-name {
  font-size: 11px;
}

.preset-description {
  font-size: 9px;
  color: #666;
}

.empty-favorites {
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-favorites .hint {
  font-size: 11px;
  margin-top: 8px;
}

.panel-footer {
  padding: 8px 12px;
  background: #222;
  border-top: 1px solid #333;
}

.info-text {
  font-size: 10px;
  color: #666;
}
</style>
