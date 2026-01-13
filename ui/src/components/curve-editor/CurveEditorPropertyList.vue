<!--
  @component CurveEditorPropertyList
  @description Property selector sidebar for the Curve Editor.
  Extracted from CurveEditor.vue to reduce file size.
-->
<template>
  <div class="property-list">
    <div class="property-list-header">
      Properties
      <button
        class="toggle-all-btn"
        @click="$emit('toggleAllProperties')"
        :title="allPropertiesVisible ? 'Hide All' : 'Show All'"
      >
        {{ allPropertiesVisible ? 'Hide' : 'Show' }}
      </button>
    </div>

    <div
      v-for="prop in animatableProperties"
      :key="prop.id"
      class="property-item"
      :class="{
        selected: selectedPropertyIds.includes(prop.id),
        animated: prop.animated
      }"
    >
      <div class="property-row" @click="$emit('toggleProperty', prop.id)">
        <span
          class="visibility-toggle"
          :class="{ visible: visiblePropertyIds.includes(prop.id) }"
          @click.stop="$emit('togglePropertyVisibility', prop.id)"
        />
        <span
          class="property-color"
          :style="{ background: getPropertyColor(prop.id) }"
        />
        <span class="property-name">{{ prop.name }}</span>
        <span class="keyframe-count" v-if="prop.animated">
          {{ prop.keyframes.length }}
        </span>
      </div>

      <!-- Separate dimensions toggle for position/scale -->
      <div
        v-if="prop.name === 'Position' || prop.name === 'Scale'"
        class="dimension-toggles"
      >
        <button
          v-for="dim in ['x', 'y', 'z']"
          :key="dim"
          :class="{
            active: visibleDimensions[prop.id]?.includes(dim),
            hasValue: hasDimension(prop, dim)
          }"
          @click="$emit('toggleDimension', prop.id, dim)"
        >
          {{ dim.toUpperCase() }}
        </button>
      </div>
    </div>

    <div v-if="animatableProperties.length === 0" class="no-properties">
      No animated properties
    </div>
  </div>
</template>

<script setup lang="ts">
import type { AnimatableProperty } from "@/types/project";

defineProps<{
  animatableProperties: AnimatableProperty<any>[];
  selectedPropertyIds: string[];
  visiblePropertyIds: string[];
  visibleDimensions: Record<string, string[]>;
  allPropertiesVisible: boolean;
  getPropertyColor: (propId: string) => string;
  hasDimension: (prop: AnimatableProperty<any>, dim: string) => boolean;
}>();

defineEmits<{
  toggleAllProperties: [];
  toggleProperty: [propId: string];
  togglePropertyVisibility: [propId: string];
  toggleDimension: [propId: string, dim: string];
}>();
</script>

<style scoped>
.property-list {
  width: 140px;
  min-width: 140px;
  background: #222;
  border-right: 1px solid #333;
  overflow-y: auto;
}

.property-list-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 6px 8px;
  background: #2a2a2a;
  border-bottom: 1px solid #333;
  font-size: 12px;
  color: #888;
}

.toggle-all-btn {
  padding: 2px 6px;
  border: 1px solid #444;
  background: transparent;
  color: #888;
  border-radius: 2px;
  font-size: 11px;
  cursor: pointer;
}

.property-item {
  border-bottom: 1px solid #2a2a2a;
}

.property-item.animated {
  border-left: 2px solid #7c9cff;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  cursor: pointer;
}

.property-row:hover {
  background: #2a2a2a;
}

.property-item.selected .property-row {
  background: rgba(124, 156, 255, 0.15);
}

.visibility-toggle {
  width: 12px;
  height: 12px;
  border: 1px solid #555;
  border-radius: 2px;
  cursor: pointer;
}

.visibility-toggle.visible {
  background: #7c9cff;
  border-color: #7c9cff;
}

.property-color {
  width: 8px;
  height: 8px;
  border-radius: 50%;
}

.property-name {
  flex: 1;
  font-size: 13px;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.keyframe-count {
  font-size: 11px;
  color: #666;
  background: #333;
  padding: 1px 4px;
  border-radius: 2px;
}

.dimension-toggles {
  display: flex;
  gap: 2px;
  padding: 2px 8px 6px 26px;
}

.dimension-toggles button {
  padding: 2px 6px;
  border: 1px solid #444;
  background: transparent;
  color: #666;
  border-radius: 2px;
  font-size: 11px;
  cursor: pointer;
}

.dimension-toggles button.active {
  background: #444;
  color: #fff;
}

.dimension-toggles button:not(.hasValue) {
  opacity: 0.3;
  cursor: default;
}

.no-properties {
  padding: 12px 8px;
  color: #555;
  font-size: 13px;
  text-align: center;
}
</style>
