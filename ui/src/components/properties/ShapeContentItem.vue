<template>
  <div class="shape-content-item" :class="{ expanded: isExpanded }">
    <!-- Header -->
    <div class="item-header" @click="isExpanded = !isExpanded">
      <span class="expand-icon">{{ isExpanded ? '▼' : '►' }}</span>
      <span class="item-icon">{{ getItemIcon(item.type) }}</span>
      <span class="item-name">{{ item.name }}</span>
      <div class="item-actions" @click.stop>
        <button
          class="action-btn"
          @click="$emit('move-up')"
          :disabled="index === 0"
          title="Move Up"
        >▲</button>
        <button
          class="action-btn"
          @click="$emit('move-down')"
          title="Move Down"
        >▼</button>
        <button
          class="action-btn delete"
          @click="$emit('delete')"
          title="Delete"
        >×</button>
      </div>
    </div>

    <!-- Content -->
    <div v-if="isExpanded" class="item-content">
      <!-- Rectangle -->
      <template v-if="item.type === 'rectangle'">
        <RectangleEditor :shape="item as RectangleShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Ellipse -->
      <template v-else-if="item.type === 'ellipse'">
        <EllipseEditor :shape="item as EllipseShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Polygon -->
      <template v-else-if="item.type === 'polygon'">
        <PolygonEditor :shape="item as PolygonShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Star -->
      <template v-else-if="item.type === 'star'">
        <StarEditor :shape="item as StarShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Path -->
      <template v-else-if="item.type === 'path'">
        <PathEditor :shape="item as PathShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Fill -->
      <template v-else-if="item.type === 'fill'">
        <FillEditor :shape="item as FillShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Stroke -->
      <template v-else-if="item.type === 'stroke'">
        <StrokeEditor :shape="item as StrokeShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Gradient Fill -->
      <template v-else-if="item.type === 'gradientFill'">
        <GradientFillEditor :shape="item as GradientFillShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Gradient Stroke -->
      <template v-else-if="item.type === 'gradientStroke'">
        <GradientStrokeEditor :shape="item as GradientStrokeShape" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Trim Paths -->
      <template v-else-if="item.type === 'trimPaths'">
        <TrimPathsEditor :operator="item as TrimPathsOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Repeater -->
      <template v-else-if="item.type === 'repeater'">
        <RepeaterEditor :operator="item as RepeaterOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Offset Paths -->
      <template v-else-if="item.type === 'offsetPaths'">
        <OffsetPathsEditor :operator="item as OffsetPathsOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Pucker & Bloat -->
      <template v-else-if="item.type === 'puckerBloat'">
        <PuckerBloatEditor :operator="item as PuckerBloatOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Wiggle Paths -->
      <template v-else-if="item.type === 'wigglePaths'">
        <WigglePathsEditor :operator="item as WigglePathsOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Zig Zag -->
      <template v-else-if="item.type === 'zigZag'">
        <ZigZagEditor :operator="item as ZigZagOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Twist -->
      <template v-else-if="item.type === 'twist'">
        <TwistEditor :operator="item as TwistOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Rounded Corners -->
      <template v-else-if="item.type === 'roundedCorners'">
        <RoundedCornersEditor :operator="item as RoundedCornersOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Merge Paths -->
      <template v-else-if="item.type === 'mergePaths'">
        <MergePathsEditor :operator="item as MergePathsOperator" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Transform -->
      <template v-else-if="item.type === 'transform'">
        <TransformEditor :transform="item as ShapeTransform" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Group (recursive) -->
      <template v-else-if="item.type === 'group'">
        <GroupEditor :group="item as ShapeGroup" :layerId="layerId" @update="emitUpdate" />
      </template>

      <!-- Fallback -->
      <template v-else>
        <div class="unsupported">
          {{ item.type }} editor not implemented yet
        </div>
      </template>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref } from "vue";
import type {
  ShapeContent,
  RectangleShape,
  EllipseShape,
  PolygonShape,
  StarShape,
  PathShape,
  FillShape,
  StrokeShape,
  GradientFillShape,
  GradientStrokeShape,
  TrimPathsOperator,
  RepeaterOperator,
  OffsetPathsOperator,
  PuckerBloatOperator,
  WigglePathsOperator,
  ZigZagOperator,
  TwistOperator,
  RoundedCornersOperator,
  MergePathsOperator,
  ShapeGroup,
  ShapeTransform,
} from "@/types/shapes";

const props = defineProps<{
  item: ShapeContent;
  index: number;
  depth: number;
  layerId: string;
}>();

const emit = defineEmits(["update", "delete", "move-up", "move-down"]);

const isExpanded = ref(false);

function getItemIcon(type: string): string {
  const icons: Record<string, string> = {
    // Generators
    rectangle: "▭",
    ellipse: "○",
    polygon: "⬡",
    star: "★",
    path: "〰",
    // Modifiers
    fill: "◼",
    stroke: "◻",
    gradientFill: "▤",
    gradientStroke: "▥",
    // Operators
    trimPaths: "✂",
    repeater: "⊞",
    offsetPaths: "⊕",
    puckerBloat: "◉",
    wigglePaths: "∿",
    zigZag: "⚡",
    twist: "⟳",
    roundedCorners: "◢",
    mergePaths: "⊗",
    // Structure
    group: "📁",
    transform: "⤢",
  };
  return icons[type] || "•";
}

function emitUpdate(updated: ShapeContent) {
  emit("update", updated);
}
</script>

<style scoped>
.shape-content-item {
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 4px;
  overflow: hidden;
}

.shape-content-item.expanded {
  background: var(--lattice-surface-1, #121212);
}

.item-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  cursor: pointer;
  user-select: none;
}

.item-header:hover {
  background: var(--lattice-surface-3, #222);
}

.expand-icon {
  width: 10px;
  font-size: 10px;
  color: var(--lattice-text-muted, #666);
}

.item-icon {
  font-size: 12px;
  width: 16px;
  text-align: center;
}

.item-name {
  flex: 1;
  font-size: 12px;
  color: var(--lattice-text-secondary, #ccc);
}

.item-actions {
  display: flex;
  gap: 2px;
  opacity: 0;
  transition: opacity 0.15s;
}

.item-header:hover .item-actions {
  opacity: 1;
}

.action-btn {
  background: transparent;
  border: none;
  color: var(--lattice-text-muted, #666);
  cursor: pointer;
  font-size: 10px;
  padding: 2px 4px;
  border-radius: 2px;
}

.action-btn:hover:not(:disabled) {
  background: var(--lattice-surface-3, #333);
  color: var(--lattice-text-secondary, #ccc);
}

.action-btn:disabled {
  opacity: 0.3;
  cursor: not-allowed;
}

.action-btn.delete {
  color: #c44;
  font-size: 14px;
  font-weight: bold;
}

.action-btn.delete:hover {
  background: #c44;
  color: #fff;
}

.item-content {
  padding: 8px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.unsupported {
  color: var(--lattice-text-muted, #666);
  font-size: 11px;
  font-style: italic;
  padding: 8px;
  text-align: center;
}
</style>
