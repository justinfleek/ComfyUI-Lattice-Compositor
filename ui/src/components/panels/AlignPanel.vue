<template>
  <div class="align-panel">
    <div class="panel-header">
      <span class="panel-title">Align</span>
    </div>

    <div class="panel-content">
      <!-- Align To Selection -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Align Layers To</span>
        </div>
        <div class="align-target-toggle">
          <button
            class="target-btn"
            :class="{ active: alignTarget === 'composition' }"
            @click="alignTarget = 'composition'"
            title="Align layers to composition bounds"
          >
            Composition
          </button>
          <button
            class="target-btn"
            :class="{ active: alignTarget === 'selection' }"
            @click="alignTarget = 'selection'"
            title="Align layers to selection bounds"
          >
            Selection
          </button>
        </div>
      </div>

      <!-- Align Buttons -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Align</span>
        </div>
        <div class="align-buttons">
          <!-- Horizontal Align -->
          <button
            class="align-btn"
            @click="alignLayers('left')"
            :disabled="!canAlign"
            title="Align Left Edges"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="3" y="4" width="2" height="16" fill="currentColor"/>
              <rect x="7" y="6" width="10" height="4" fill="currentColor"/>
              <rect x="7" y="14" width="14" height="4" fill="currentColor"/>
            </svg>
          </button>
          <button
            class="align-btn"
            @click="alignLayers('centerH')"
            :disabled="!canAlign"
            title="Align Horizontal Centers"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="11" y="4" width="2" height="16" fill="currentColor"/>
              <rect x="5" y="6" width="14" height="4" fill="currentColor"/>
              <rect x="3" y="14" width="18" height="4" fill="currentColor"/>
            </svg>
          </button>
          <button
            class="align-btn"
            @click="alignLayers('right')"
            :disabled="!canAlign"
            title="Align Right Edges"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="19" y="4" width="2" height="16" fill="currentColor"/>
              <rect x="7" y="6" width="10" height="4" fill="currentColor"/>
              <rect x="3" y="14" width="14" height="4" fill="currentColor"/>
            </svg>
          </button>

          <div class="separator"></div>

          <!-- Vertical Align -->
          <button
            class="align-btn"
            @click="alignLayers('top')"
            :disabled="!canAlign"
            title="Align Top Edges"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="4" y="3" width="16" height="2" fill="currentColor"/>
              <rect x="6" y="7" width="4" height="10" fill="currentColor"/>
              <rect x="14" y="7" width="4" height="14" fill="currentColor"/>
            </svg>
          </button>
          <button
            class="align-btn"
            @click="alignLayers('centerV')"
            :disabled="!canAlign"
            title="Align Vertical Centers"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="4" y="11" width="16" height="2" fill="currentColor"/>
              <rect x="6" y="5" width="4" height="14" fill="currentColor"/>
              <rect x="14" y="3" width="4" height="18" fill="currentColor"/>
            </svg>
          </button>
          <button
            class="align-btn"
            @click="alignLayers('bottom')"
            :disabled="!canAlign"
            title="Align Bottom Edges"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="4" y="19" width="16" height="2" fill="currentColor"/>
              <rect x="6" y="7" width="4" height="10" fill="currentColor"/>
              <rect x="14" y="3" width="4" height="14" fill="currentColor"/>
            </svg>
          </button>
        </div>
      </div>

      <!-- Distribute Buttons -->
      <div class="control-section">
        <div class="section-header">
          <span class="section-title">Distribute</span>
        </div>
        <div class="align-buttons">
          <button
            class="align-btn wide"
            @click="distributeLayers('horizontal')"
            :disabled="!canDistribute"
            title="Distribute Horizontally"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="3" y="6" width="4" height="12" fill="currentColor"/>
              <rect x="10" y="8" width="4" height="8" fill="currentColor"/>
              <rect x="17" y="6" width="4" height="12" fill="currentColor"/>
            </svg>
            <span>Horizontal</span>
          </button>
          <button
            class="align-btn wide"
            @click="distributeLayers('vertical')"
            :disabled="!canDistribute"
            title="Distribute Vertically"
          >
            <svg viewBox="0 0 24 24" class="align-icon">
              <rect x="6" y="3" width="12" height="4" fill="currentColor"/>
              <rect x="8" y="10" width="8" height="4" fill="currentColor"/>
              <rect x="6" y="17" width="12" height="4" fill="currentColor"/>
            </svg>
            <span>Vertical</span>
          </button>
        </div>
      </div>

      <!-- Selection Info -->
      <div class="selection-info">
        <span v-if="selectedCount === 0">No layers selected</span>
        <span v-else-if="selectedCount === 1">1 layer selected</span>
        <span v-else>{{ selectedCount }} layers selected</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";

const store = useCompositorStore();
const layerStore = useLayerStore();

const alignTarget = ref<"composition" | "selection">("composition");

const selectedCount = computed(() => store.selectedLayerIds.length);
const canAlign = computed(() => selectedCount.value >= 1);
const canDistribute = computed(() => selectedCount.value >= 3);

type AlignDirection =
  | "left"
  | "centerH"
  | "right"
  | "top"
  | "centerV"
  | "bottom";
type DistributeDirection = "horizontal" | "vertical";

function alignLayers(direction: AlignDirection) {
  const layerIds = store.selectedLayerIds;
  if (layerIds.length === 0) return;

  const comp = store.getActiveComp();
  if (!comp) return;

  // Get layer bounds
  const layers = layerIds.map((id) => layerStore.getLayerById(store, id)).filter(Boolean);
  if (layers.length === 0) return;

  let targetBounds: {
    left: number;
    right: number;
    top: number;
    bottom: number;
    centerX: number;
    centerY: number;
  };

  if (alignTarget.value === "composition") {
    targetBounds = {
      left: 0,
      right: comp.settings.width,
      top: 0,
      bottom: comp.settings.height,
      centerX: comp.settings.width / 2,
      centerY: comp.settings.height / 2,
    };
  } else {
    // Calculate selection bounds
    let minX = Infinity,
      maxX = -Infinity,
      minY = Infinity,
      maxY = -Infinity;
    for (const layer of layers) {
      if (!layer) continue;
      const pos = layer.transform?.position?.value || { x: 0, y: 0 };
      minX = Math.min(minX, pos.x);
      maxX = Math.max(maxX, pos.x);
      minY = Math.min(minY, pos.y);
      maxY = Math.max(maxY, pos.y);
    }
    targetBounds = {
      left: minX,
      right: maxX,
      top: minY,
      bottom: maxY,
      centerX: (minX + maxX) / 2,
      centerY: (minY + maxY) / 2,
    };
  }

  // Apply alignment
  for (const layer of layers) {
    if (!layer || !layer.transform?.position) continue;

    const pos = { ...layer.transform.position.value };

    switch (direction) {
      case "left":
        pos.x = targetBounds.left;
        break;
      case "centerH":
        pos.x = targetBounds.centerX;
        break;
      case "right":
        pos.x = targetBounds.right;
        break;
      case "top":
        pos.y = targetBounds.top;
        break;
      case "centerV":
        pos.y = targetBounds.centerY;
        break;
      case "bottom":
        pos.y = targetBounds.bottom;
        break;
    }

    layer.transform.position.value = pos;
  }

  store.project.meta.modified = new Date().toISOString();
}

function distributeLayers(direction: DistributeDirection) {
  const layerIds = store.selectedLayerIds;
  if (layerIds.length < 3) return;

  const layers = layerIds
    .map((id) => layerStore.getLayerById(store, id))
    .filter(Boolean)
    .filter((l) => l?.transform?.position);

  if (layers.length < 3) return;

  // Sort layers by position
  const sorted = [...layers].sort((a, b) => {
    const posA = a?.transform?.position?.value;
    const posB = b?.transform?.position?.value;
    if (!posA || !posB) return 0;
    return direction === "horizontal" ? posA.x - posB.x : posA.y - posB.y;
  });

  // Get first and last positions
  const first = sorted[0]?.transform?.position?.value;
  const last = sorted[sorted.length - 1]?.transform?.position?.value;
  if (!first || !last) return;

  // Calculate spacing
  const totalDistance =
    direction === "horizontal" ? last.x - first.x : last.y - first.y;
  const spacing = totalDistance / (sorted.length - 1);

  // Apply distribution
  for (let i = 1; i < sorted.length - 1; i++) {
    const layer = sorted[i];
    if (!layer?.transform?.position) continue;
    const pos = { ...layer.transform.position.value };

    if (direction === "horizontal") {
      pos.x = first.x + spacing * i;
    } else {
      pos.y = first.y + spacing * i;
    }

    layer.transform.position.value = pos;
  }

  store.project.meta.modified = new Date().toISOString();
}
</script>

<style scoped>
.align-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #1e1e1e);
  color: #e0e0e0;
}

.panel-header {
  padding: 8px 12px;
  background: var(--lattice-surface-2, #252525);
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
}

.panel-content {
  flex: 1;
  padding: 12px;
  overflow-y: auto;
}

.control-section {
  margin-bottom: 16px;
}

.section-header {
  margin-bottom: 8px;
}

.section-title {
  font-size: 11px;
  font-weight: 600;
  color: #888;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.align-target-toggle {
  display: flex;
  gap: 4px;
}

.target-btn {
  flex: 1;
  padding: 6px 12px;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: #252525;
  color: #888;
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.target-btn:hover {
  background: #333;
  color: #e0e0e0;
}

.target-btn.active {
  background: var(--lattice-accent, #4a90d9);
  border-color: var(--lattice-accent, #4a90d9);
  color: #fff;
}

.align-buttons {
  display: flex;
  gap: 4px;
  flex-wrap: wrap;
}

.align-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
  width: 36px;
  height: 36px;
  padding: 0;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: #252525;
  color: #888;
  cursor: pointer;
  transition: all 0.15s;
}

.align-btn.wide {
  width: auto;
  flex: 1;
  padding: 8px 12px;
  font-size: 11px;
}

.align-btn:hover:not(:disabled) {
  background: #333;
  color: #e0e0e0;
  border-color: #4a90d9;
}

.align-btn:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.align-icon {
  width: 18px;
  height: 18px;
}

.separator {
  width: 1px;
  height: 28px;
  background: #3a3a3a;
  margin: 4px 4px;
}

.selection-info {
  margin-top: 16px;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
  font-size: 11px;
  color: #666;
  text-align: center;
}
</style>
