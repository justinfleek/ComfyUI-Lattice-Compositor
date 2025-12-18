<template>
  <div class="pickwhip-container" ref="containerRef">
    <!-- The pickwhip icon/button -->
    <div
      class="pickwhip-handle"
      :class="{ dragging: isDragging, linked: hasLink }"
      @mousedown="startDrag"
      @touchstart.prevent="startDrag"
      :title="hasLink ? `Linked to: ${linkTargetName}` : 'Drag to link property'"
    >
      <svg viewBox="0 0 16 16" class="pickwhip-icon">
        <circle cx="8" cy="8" r="3" fill="currentColor" />
        <path
          v-if="!hasLink"
          d="M8 5 L8 2 M8 11 L8 14 M5 8 L2 8 M11 8 L14 8"
          stroke="currentColor"
          stroke-width="1.5"
          fill="none"
        />
        <path
          v-else
          d="M11 5 L14 2 M11 11 L14 14"
          stroke="currentColor"
          stroke-width="1.5"
          fill="none"
        />
      </svg>
    </div>

    <!-- Clear link button (shown when linked) -->
    <button
      v-if="hasLink"
      class="clear-link-btn"
      @click="clearLink"
      title="Remove link"
    >
      &times;
    </button>

    <!-- Drag line visualization (portal to body) -->
    <Teleport to="body">
      <svg
        v-if="isDragging"
        class="pickwhip-line"
        :style="lineStyle"
      >
        <line
          :x1="dragStart.x"
          :y1="dragStart.y"
          :x2="dragEnd.x"
          :y2="dragEnd.y"
          stroke="#4a90d9"
          stroke-width="2"
          stroke-dasharray="4 2"
        />
        <circle
          :cx="dragEnd.x"
          :cy="dragEnd.y"
          r="6"
          fill="#4a90d9"
          stroke="#fff"
          stroke-width="1"
        />
      </svg>
    </Teleport>

    <!-- Drop target highlight overlay -->
    <Teleport to="body">
      <div
        v-if="isDragging && currentDropTarget"
        class="drop-target-highlight"
        :style="dropTargetStyle"
      >
        <span class="drop-label">{{ currentDropTarget.label }}</span>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted } from 'vue';
import type { PropertyPath } from '@/services/propertyDriver';

interface DropTarget {
  layerId: string;
  property: PropertyPath;
  label: string;
  element: HTMLElement;
  rect: DOMRect;
}

const props = defineProps<{
  layerId: string;
  property: PropertyPath;
  linkedTo?: { layerId: string; property: PropertyPath } | null;
}>();

const emit = defineEmits<{
  (e: 'link', target: { layerId: string; property: PropertyPath }): void;
  (e: 'unlink'): void;
}>();

const containerRef = ref<HTMLDivElement | null>(null);
const isDragging = ref(false);
const dragStart = ref({ x: 0, y: 0 });
const dragEnd = ref({ x: 0, y: 0 });
const currentDropTarget = ref<DropTarget | null>(null);

const hasLink = computed(() => !!props.linkedTo);

const linkTargetName = computed(() => {
  if (!props.linkedTo) return '';
  return `${props.linkedTo.layerId}.${props.linkedTo.property}`;
});

const lineStyle = computed(() => ({
  position: 'fixed' as const,
  top: 0,
  left: 0,
  width: '100vw',
  height: '100vh',
  pointerEvents: 'none' as const,
  zIndex: 10000
}));

const dropTargetStyle = computed(() => {
  if (!currentDropTarget.value) return {};
  const rect = currentDropTarget.value.rect;
  return {
    position: 'fixed' as const,
    top: `${rect.top}px`,
    left: `${rect.left}px`,
    width: `${rect.width}px`,
    height: `${rect.height}px`,
    zIndex: 9999
  };
});

// Find all valid drop targets in the DOM
function findDropTargets(): DropTarget[] {
  const targets: DropTarget[] = [];

  // Find all elements with data-pickwhip-target attribute
  const elements = document.querySelectorAll('[data-pickwhip-target]');

  elements.forEach(el => {
    const htmlEl = el as HTMLElement;
    const layerId = htmlEl.dataset.pickwhipLayerId;
    const property = htmlEl.dataset.pickwhipTarget as PropertyPath;
    const label = htmlEl.dataset.pickwhipLabel || property;

    // Don't allow linking to self
    if (layerId === props.layerId && property === props.property) {
      return;
    }

    if (layerId && property) {
      targets.push({
        layerId,
        property,
        label,
        element: htmlEl,
        rect: htmlEl.getBoundingClientRect()
      });
    }
  });

  return targets;
}

// Find drop target at position
function findTargetAtPosition(x: number, y: number, targets: DropTarget[]): DropTarget | null {
  for (const target of targets) {
    const rect = target.rect;
    if (x >= rect.left && x <= rect.right && y >= rect.top && y <= rect.bottom) {
      return target;
    }
  }
  return null;
}

let dropTargets: DropTarget[] = [];

function startDrag(e: MouseEvent | TouchEvent) {
  e.preventDefault();
  e.stopPropagation();

  const clientX = 'touches' in e ? e.touches[0].clientX : e.clientX;
  const clientY = 'touches' in e ? e.touches[0].clientY : e.clientY;

  // Get start position from the pickwhip handle
  const rect = containerRef.value?.getBoundingClientRect();
  if (rect) {
    dragStart.value = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 };
  } else {
    dragStart.value = { x: clientX, y: clientY };
  }

  dragEnd.value = { x: clientX, y: clientY };
  isDragging.value = true;

  // Collect all drop targets
  dropTargets = findDropTargets();

  // Add listeners
  window.addEventListener('mousemove', onDrag);
  window.addEventListener('mouseup', endDrag);
  window.addEventListener('touchmove', onDrag);
  window.addEventListener('touchend', endDrag);
}

function onDrag(e: MouseEvent | TouchEvent) {
  if (!isDragging.value) return;

  const clientX = 'touches' in e ? e.touches[0].clientX : e.clientX;
  const clientY = 'touches' in e ? e.touches[0].clientY : e.clientY;

  dragEnd.value = { x: clientX, y: clientY };

  // Update drop target rects (in case of scroll)
  dropTargets.forEach(t => {
    t.rect = t.element.getBoundingClientRect();
  });

  // Check for drop target under cursor
  currentDropTarget.value = findTargetAtPosition(clientX, clientY, dropTargets);
}

function endDrag(e: MouseEvent | TouchEvent) {
  if (!isDragging.value) return;

  const clientX = 'changedTouches' in e ? e.changedTouches[0].clientX : e.clientX;
  const clientY = 'changedTouches' in e ? e.changedTouches[0].clientY : e.clientY;

  // Check if we're over a valid drop target
  const target = findTargetAtPosition(clientX, clientY, dropTargets);

  if (target) {
    emit('link', { layerId: target.layerId, property: target.property });
  }

  // Cleanup
  isDragging.value = false;
  currentDropTarget.value = null;
  dropTargets = [];

  window.removeEventListener('mousemove', onDrag);
  window.removeEventListener('mouseup', endDrag);
  window.removeEventListener('touchmove', onDrag);
  window.removeEventListener('touchend', endDrag);
}

function clearLink() {
  emit('unlink');
}

onUnmounted(() => {
  // Cleanup any lingering listeners
  window.removeEventListener('mousemove', onDrag);
  window.removeEventListener('mouseup', endDrag);
  window.removeEventListener('touchmove', onDrag);
  window.removeEventListener('touchend', endDrag);
});
</script>

<style scoped>
.pickwhip-container {
  display: inline-flex;
  align-items: center;
  gap: 4px;
}

.pickwhip-handle {
  width: 16px;
  height: 16px;
  cursor: crosshair;
  color: #666;
  transition: color 0.15s, transform 0.15s;
  user-select: none;
}

.pickwhip-handle:hover {
  color: #4a90d9;
  transform: scale(1.1);
}

.pickwhip-handle.dragging {
  color: #4a90d9;
  transform: scale(1.2);
}

.pickwhip-handle.linked {
  color: #2ecc71;
}

.pickwhip-icon {
  width: 100%;
  height: 100%;
}

.clear-link-btn {
  width: 14px;
  height: 14px;
  padding: 0;
  border: none;
  background: #e74c3c;
  color: white;
  border-radius: 50%;
  font-size: 12px;
  line-height: 1;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
}

.clear-link-btn:hover {
  background: #c0392b;
}
</style>

<style>
/* Global styles for pickwhip visualization */
.pickwhip-line {
  pointer-events: none;
}

.drop-target-highlight {
  background: rgba(74, 144, 217, 0.3);
  border: 2px solid #4a90d9;
  border-radius: 4px;
  pointer-events: none;
  display: flex;
  align-items: center;
  justify-content: center;
}

.drop-label {
  background: #4a90d9;
  color: white;
  padding: 2px 8px;
  border-radius: 3px;
  font-size: 12px;
  font-weight: bold;
}

/* Mark elements as pickwhip targets */
[data-pickwhip-target] {
  position: relative;
}

[data-pickwhip-target]::after {
  content: '';
  position: absolute;
  inset: -2px;
  border: 2px solid transparent;
  border-radius: 4px;
  pointer-events: none;
  transition: border-color 0.15s;
}

/* This would be activated via JS when dragging */
.pickwhip-target-active[data-pickwhip-target]::after {
  border-color: rgba(74, 144, 217, 0.5);
}
</style>
