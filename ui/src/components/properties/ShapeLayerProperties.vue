<template>
  <div class="shape-layer-properties">
    <!-- Layer Settings -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('settings')">
        <span class="expand-icon">{{ expandedSections.includes('settings') ? '▼' : '►' }}</span>
        <span class="section-title">Layer Settings</span>
      </div>
      <div v-if="expandedSections.includes('settings')" class="section-content">
        <div class="property-row">
          <label>Quality</label>
          <select v-model="layerData.quality" @change="updateData">
            <option value="draft">Draft</option>
            <option value="normal">Normal</option>
            <option value="high">High</option>
          </select>
        </div>
        <div class="property-row checkbox-row">
          <label>
            <input type="checkbox" v-model="layerData.gpuAccelerated" @change="updateData" />
            GPU Accelerated
          </label>
        </div>
      </div>
    </div>

    <!-- Contents Tree -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('contents')">
        <span class="expand-icon">{{ expandedSections.includes('contents') ? '▼' : '►' }}</span>
        <span class="section-title">Contents</span>
        <span class="item-count" v-if="layerData.contents?.length">{{ layerData.contents.length }}</span>
      </div>
      <div v-if="expandedSections.includes('contents')" class="section-content">
        <!-- Add Content Button -->
        <div class="add-content-row">
          <select v-model="newContentType" class="content-select">
            <option value="">Add...</option>
            <optgroup label="Generators">
              <option value="rectangle">Rectangle</option>
              <option value="ellipse">Ellipse</option>
              <option value="polygon">Polygon</option>
              <option value="star">Star</option>
              <option value="path">Path</option>
            </optgroup>
            <optgroup label="Modifiers">
              <option value="fill">Fill</option>
              <option value="stroke">Stroke</option>
              <option value="gradientFill">Gradient Fill</option>
              <option value="gradientStroke">Gradient Stroke</option>
            </optgroup>
            <optgroup label="Operators">
              <option value="trimPaths">Trim Paths</option>
              <option value="repeater">Repeater</option>
              <option value="offsetPaths">Offset Paths</option>
              <option value="puckerBloat">Pucker & Bloat</option>
              <option value="wigglePaths">Wiggle Paths</option>
              <option value="zigZag">Zig Zag</option>
              <option value="twist">Twist</option>
              <option value="roundedCorners">Rounded Corners</option>
              <option value="mergePaths">Merge Paths</option>
            </optgroup>
            <optgroup label="Structure">
              <option value="group">Group</option>
              <option value="transform">Transform</option>
            </optgroup>
          </select>
          <button class="add-btn" @click="addContent" :disabled="!newContentType">+</button>
        </div>

        <!-- Contents List -->
        <div class="contents-list">
          <template v-for="(item, index) in layerData.contents || []" :key="item.name + index">
            <ShapeContentItem
              :item="item"
              :index="index"
              :depth="0"
              @update="updateContentItem(index, $event)"
              @delete="deleteContentItem(index)"
              @move-up="moveContentItem(index, -1)"
              @move-down="moveContentItem(index, 1)"
            />
          </template>
        </div>

        <div v-if="!layerData.contents?.length" class="no-contents">
          No shape contents. Add a generator (Rectangle, Ellipse) and modifiers (Fill, Stroke).
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch } from 'vue';
import type { Layer } from '@/types/project';
import type {
  ShapeLayerData,
  ShapeContent,
  ShapeGroup,
  RectangleShape,
  EllipseShape,
  PolygonShape,
  StarShape,
  PathShape,
  FillShape,
  StrokeShape,
  TrimPathsOperator,
  RepeaterOperator,
  OffsetPathsOperator,
  PuckerBloatOperator,
  WigglePathsOperator,
  ZigZagOperator,
  TwistOperator,
  RoundedCornersOperator,
  MergePathsOperator,
  ShapeTransform,
} from '@/types/shapes';
import {
  createDefaultShapeLayerData,
  createDefaultGroup,
  createDefaultRectangle,
  createDefaultEllipse,
  createDefaultPolygon,
  createDefaultStar,
  createDefaultPath,
  createDefaultFill,
  createDefaultStroke,
  createDefaultGradientFill,
  createDefaultGradientStroke,
  createDefaultTrimPaths,
  createDefaultRepeater,
  createDefaultOffsetPaths,
  createDefaultPuckerBloat,
  createDefaultWigglePaths,
  createDefaultZigZag,
  createDefaultTwist,
  createDefaultRoundedCorners,
  createDefaultMergePaths,
  createDefaultShapeTransform,
} from '@/types/shapes';
import { useCompositorStore } from '@/stores/compositorStore';
import ShapeContentItem from './ShapeContentItem.vue';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const expandedSections = ref<string[]>(['contents', 'settings']);
const newContentType = ref<string>('');

// Get layer data with defaults
const layerData = computed<ShapeLayerData>(() => {
  const data = props.layer.data as ShapeLayerData;
  if (!data || !data.contents) {
    return createDefaultShapeLayerData();
  }
  return data;
});

function toggleSection(section: string) {
  const idx = expandedSections.value.indexOf(section);
  if (idx >= 0) {
    expandedSections.value.splice(idx, 1);
  } else {
    expandedSections.value.push(section);
  }
}

function updateData() {
  store.updateLayer(props.layer.id, {
    data: { ...layerData.value }
  });
  emit('update');
}

function addContent() {
  if (!newContentType.value) return;

  const contents = [...(layerData.value.contents || [])];
  let newItem: ShapeContent;

  switch (newContentType.value) {
    // Generators
    case 'rectangle':
      newItem = createDefaultRectangle();
      break;
    case 'ellipse':
      newItem = createDefaultEllipse();
      break;
    case 'polygon':
      newItem = createDefaultPolygon();
      break;
    case 'star':
      newItem = createDefaultStar();
      break;
    case 'path':
      newItem = createDefaultPath();
      break;
    // Modifiers
    case 'fill':
      newItem = createDefaultFill();
      break;
    case 'stroke':
      newItem = createDefaultStroke();
      break;
    case 'gradientFill':
      newItem = createDefaultGradientFill();
      break;
    case 'gradientStroke':
      newItem = createDefaultGradientStroke();
      break;
    // Operators
    case 'trimPaths':
      newItem = createDefaultTrimPaths();
      break;
    case 'repeater':
      newItem = createDefaultRepeater();
      break;
    case 'offsetPaths':
      newItem = createDefaultOffsetPaths();
      break;
    case 'puckerBloat':
      newItem = createDefaultPuckerBloat();
      break;
    case 'wigglePaths':
      newItem = createDefaultWigglePaths();
      break;
    case 'zigZag':
      newItem = createDefaultZigZag();
      break;
    case 'twist':
      newItem = createDefaultTwist();
      break;
    case 'roundedCorners':
      newItem = createDefaultRoundedCorners();
      break;
    case 'mergePaths':
      newItem = createDefaultMergePaths();
      break;
    // Structure
    case 'group':
      newItem = createDefaultGroup();
      break;
    case 'transform':
      newItem = createDefaultShapeTransform();
      break;
    default:
      return;
  }

  contents.push(newItem);

  store.updateLayer(props.layer.id, {
    data: { ...layerData.value, contents }
  });
  emit('update');
  newContentType.value = '';
}

function updateContentItem(index: number, updatedItem: ShapeContent) {
  const contents = [...(layerData.value.contents || [])];
  contents[index] = updatedItem;

  store.updateLayer(props.layer.id, {
    data: { ...layerData.value, contents }
  });
  emit('update');
}

function deleteContentItem(index: number) {
  const contents = [...(layerData.value.contents || [])];
  contents.splice(index, 1);

  store.updateLayer(props.layer.id, {
    data: { ...layerData.value, contents }
  });
  emit('update');
}

function moveContentItem(index: number, direction: -1 | 1) {
  const contents = [...(layerData.value.contents || [])];
  const newIndex = index + direction;
  if (newIndex < 0 || newIndex >= contents.length) return;

  // Swap items
  [contents[index], contents[newIndex]] = [contents[newIndex], contents[index]];

  store.updateLayer(props.layer.id, {
    data: { ...layerData.value, contents }
  });
  emit('update');
}
</script>

<style scoped>
.shape-layer-properties {
  padding: 0;
}

.prop-section {
  border-bottom: 1px solid var(--weyl-border-subtle, #2a2a2a);
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
  background: var(--weyl-surface-2, #1a1a1a);
}

.section-header:hover {
  background: var(--weyl-surface-3, #222);
}

.expand-icon {
  width: 10px;
  font-size: 11px;
  color: var(--weyl-text-muted, #666);
}

.section-title {
  flex: 1;
  font-weight: 600;
  font-size: 13px;
  color: var(--weyl-text-secondary, #ccc);
}

.item-count {
  background: var(--weyl-accent, #8B5CF6);
  color: #fff;
  font-size: 10px;
  padding: 1px 6px;
  border-radius: 8px;
}

.section-content {
  padding: 8px 10px;
  background: var(--weyl-surface-1, #121212);
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  min-height: 24px;
}

.property-row label {
  width: 90px;
  color: var(--weyl-text-muted, #888);
  font-size: 12px;
  flex-shrink: 0;
}

.property-row select {
  flex: 1;
  padding: 4px 8px;
  background: var(--weyl-surface-0, #0a0a0a);
  border: 1px solid var(--weyl-border-default, #333);
  border-radius: 3px;
  color: var(--weyl-text-primary, #e0e0e0);
  font-size: 12px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  width: auto;
  color: var(--weyl-text-secondary, #ccc);
  font-size: 12px;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
}

/* Add Content */
.add-content-row {
  display: flex;
  gap: 6px;
  margin-bottom: 8px;
}

.content-select {
  flex: 1;
  padding: 6px 8px;
  background: var(--weyl-surface-0, #0a0a0a);
  border: 1px solid var(--weyl-border-default, #333);
  border-radius: 3px;
  color: var(--weyl-text-primary, #e0e0e0);
  font-size: 12px;
  cursor: pointer;
}

.content-select:focus {
  outline: none;
  border-color: var(--weyl-accent, #8B5CF6);
}

.content-select optgroup {
  color: var(--weyl-text-muted, #888);
  font-weight: 600;
}

.add-btn {
  width: 28px;
  height: 28px;
  padding: 0;
  border: 1px solid var(--weyl-accent, #8B5CF6);
  background: var(--weyl-accent, #8B5CF6);
  color: #fff;
  border-radius: 3px;
  cursor: pointer;
  font-size: 18px;
  font-weight: bold;
  line-height: 1;
}

.add-btn:hover:not(:disabled) {
  background: var(--weyl-accent-hover, #9d6eff);
}

.add-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

/* Contents List */
.contents-list {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.no-contents {
  color: var(--weyl-text-muted, #666);
  font-size: 12px;
  text-align: center;
  padding: 16px;
  font-style: italic;
  background: var(--weyl-surface-0, #0a0a0a);
  border-radius: 4px;
}
</style>
