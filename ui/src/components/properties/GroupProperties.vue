<template>
  <div class="group-properties">
    <!-- Group Appearance -->
    <div class="prop-section">
      <div class="section-title">Group Appearance</div>

      <div class="row color-row">
        <label>Label Color</label>
        <div class="color-picker-wrapper">
          <input
            type="color"
            :value="groupData.color"
            @input="updateData('color', ($event.target as HTMLInputElement).value)"
          />
          <span class="color-hex">{{ groupData.color }}</span>
        </div>
      </div>

      <!-- Quick color presets -->
      <div class="color-presets">
        <button
          v-for="preset in colorPresets"
          :key="preset.color"
          class="preset-btn"
          :style="{ backgroundColor: preset.color }"
          :title="preset.name"
          @click="updateData('color', preset.color)"
        />
      </div>
    </div>

    <!-- Group Behavior -->
    <div class="prop-section">
      <div class="section-title">Group Behavior</div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="groupData.collapsed" @change="updateData('collapsed', !groupData.collapsed)" />
          Collapsed in Timeline
        </label>
        <span class="hint-icon" title="Hide child layers in the timeline panel">?</span>
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="groupData.passThrough" @change="updateData('passThrough', !groupData.passThrough)" />
          Pass-Through Mode
        </label>
        <span class="hint-icon" title="Blend modes of child layers affect layers outside the group">?</span>
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="groupData.isolate" @change="updateData('isolate', !groupData.isolate)" />
          Isolate Group
        </label>
        <span class="hint-icon" title="Only show this group's contents in the viewer">?</span>
      </div>
    </div>

    <!-- Group Contents Info -->
    <div class="prop-section">
      <div class="section-title">Contents</div>

      <div class="info-row">
        <span class="info-label">Child Layers</span>
        <span class="info-value">{{ childCount }}</span>
      </div>

      <div class="child-list" v-if="childLayers.length > 0">
        <div
          v-for="child in childLayers"
          :key="child.id"
          class="child-item"
          @click="selectLayer(child.id)"
        >
          <span class="child-icon">{{ getLayerIcon(child.type) }}</span>
          <span class="child-name">{{ child.name }}</span>
        </div>
      </div>

      <p v-else class="empty-hint">
        No child layers. Parent other layers to this group.
      </p>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type { GroupLayerData, Layer, LayerType } from "@/types/project";

const props = defineProps<{
  layer: Layer;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<GroupLayerData>) => void>();

const store = useCompositorStore();

const groupData = computed(() => props.layer.data as GroupLayerData);

// Find child layers (layers that have this group as parent)
const childLayers = computed(() => {
  return store.layers.filter((l) => l.parentId === props.layer.id);
});

const childCount = computed(() => childLayers.value.length);

const colorPresets = [
  { name: "Red", color: "#e74c3c" },
  { name: "Orange", color: "#e67e22" },
  { name: "Yellow", color: "#f1c40f" },
  { name: "Green", color: "#2ecc71" },
  { name: "Cyan", color: "#1abc9c" },
  { name: "Blue", color: "#3498db" },
  { name: "Purple", color: "#9b59b6" },
  { name: "Pink", color: "#e91e63" },
  { name: "Gray", color: "#888888" },
];

function updateData<K extends keyof GroupLayerData>(
  key: K,
  value: GroupLayerData[K],
) {
  emit("update", { [key]: value } as Partial<GroupLayerData>);
}

function selectLayer(layerId: string) {
  store.selectLayer(layerId);
}

function getLayerIcon(type: LayerType): string {
  const icons: Record<string, string> = {
    image: "🖼",
    video: "🎬",
    solid: "■",
    null: "◇",
    text: "T",
    spline: "〰",
    shape: "◆",
    particles: "✦",
    camera: "📷",
    light: "💡",
    group: "📁",
    audio: "🔊",
    depth: "🌊",
    normal: "🧭",
    generated: "🤖",
  };
  return icons[type] || "•";
}
</script>

<style scoped>
.group-properties {
  padding: 8px 0;
}

.prop-section {
  margin-bottom: 12px;
  padding: 0 10px;
}

.section-title {
  font-size: 12px;
  font-weight: 600;
  color: #4a90d9;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: 8px;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.row label {
  min-width: 90px;
  font-size: 13px;
  color: #888;
}

.color-row {
  display: flex;
  align-items: center;
}

.color-picker-wrapper {
  display: flex;
  align-items: center;
  gap: 8px;
  flex: 1;
}

.color-picker-wrapper input[type="color"] {
  width: 40px;
  height: 28px;
  padding: 0;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: transparent;
  cursor: pointer;
}

.color-hex {
  font-family: monospace;
  font-size: 12px;
  color: #888;
  text-transform: uppercase;
}

.color-presets {
  display: flex;
  gap: 4px;
  flex-wrap: wrap;
  margin-top: 8px;
}

.preset-btn {
  width: 24px;
  height: 24px;
  border: 2px solid #1e1e1e;
  border-radius: 4px;
  cursor: pointer;
  transition: all 0.15s;
}

.preset-btn:hover {
  transform: scale(1.1);
  border-color: #fff;
}

.checkbox-row {
  display: flex;
  align-items: center;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  min-width: auto;
  color: #e0e0e0;
  font-size: 13px;
  flex: 1;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
  accent-color: #4a90d9;
}

.hint-icon {
  width: 16px;
  height: 16px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 10px;
  color: #666;
  background: #333;
  border-radius: 50%;
  cursor: help;
}

.info-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 4px 0;
}

.info-label {
  font-size: 13px;
  color: #888;
}

.info-value {
  font-size: 13px;
  color: #e0e0e0;
  font-weight: 500;
}

.child-list {
  margin-top: 8px;
  max-height: 150px;
  overflow-y: auto;
}

.child-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 8px;
  background: #252525;
  border-radius: 4px;
  margin-bottom: 4px;
  cursor: pointer;
  transition: background 0.15s;
}

.child-item:hover {
  background: #333;
}

.child-icon {
  font-size: 14px;
}

.child-name {
  font-size: 12px;
  color: #e0e0e0;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.empty-hint {
  font-size: 12px;
  color: #666;
  text-align: center;
  padding: 16px;
}
</style>
