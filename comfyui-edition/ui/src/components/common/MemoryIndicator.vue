<template>
  <div
    class="memory-indicator"
    :class="warningClass"
    @click="showDetails = !showDetails"
    :title="tooltipText"
  >
    <div class="memory-bar">
      <div class="memory-fill" :style="{ width: `${usagePercent}%` }" />
    </div>
    <span class="memory-text">{{ usageText }}</span>

    <!-- Expanded Details -->
    <div v-if="showDetails" class="memory-details" @click.stop>
      <div class="details-header">
        <span>GPU Memory Usage</span>
        <button class="close-details" @click="showDetails = false">
          <i class="pi pi-times" />
        </button>
      </div>

      <div class="gpu-info" v-if="gpuInfo">
        <small>{{ gpuInfo.renderer }}</small>
        <small>~{{ formatMB(gpuInfo.estimatedVRAM) }} VRAM ({{ gpuInfo.tier }})</small>
      </div>

      <div class="category-breakdown">
        <div
          v-for="(value, category) in usageByCategory"
          :key="category"
          class="category-row"
          v-show="value > 0"
        >
          <span class="category-name">{{ formatCategory(category) }}</span>
          <span class="category-value">{{ formatMB(value) }}</span>
        </div>
      </div>

      <div v-if="warning" class="warning-box" :class="warning.level">
        <p>{{ warning.message }}</p>
        <ul v-if="warning.suggestions.length > 0">
          <li v-for="(suggestion, i) in warning.suggestions.slice(0, 3)" :key="i">
            {{ suggestion }}
          </li>
        </ul>
      </div>

      <div class="details-footer" v-if="unloadableCount > 0">
        <button class="cleanup-btn" @click="performCleanup" :disabled="isCleaningUp">
          <i class="pi pi-trash" />
          {{ isCleaningUp ? 'Cleaning...' : `Free Memory (${unloadableCount} items)` }}
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref } from "vue";
import {
  freeMemory,
  getWarning,
  initializeGPUDetection,
  memoryState,
  unloadableItems,
} from "@/services/memoryBudget";

const showDetails = ref(false);
const isCleaningUp = ref(false);

// Computed values from memory state
const usagePercent = computed(() =>
  Math.round(memoryState.usagePercent.value * 100),
);
const totalUsage = computed(() => memoryState.totalUsageMB.value);
const available = computed(() => memoryState.availableVRAM.value);
const warningLevel = computed(() => memoryState.warningLevel.value);
const gpuInfo = computed(() => memoryState.gpuInfo.value);
const usageByCategory = computed(() => memoryState.usageByCategory.value);
const warning = computed(() => getWarning());
const unloadableCount = computed(() => unloadableItems.value.length);

const warningClass = computed(() => ({
  "level-none": warningLevel.value === "none",
  "level-info": warningLevel.value === "info",
  "level-warning": warningLevel.value === "warning",
  "level-critical": warningLevel.value === "critical",
}));

const usageText = computed(() => {
  return `${formatMB(totalUsage.value)} / ${formatMB(available.value)}`;
});

const tooltipText = computed(() => {
  const percent = usagePercent.value;
  if (warningLevel.value === "critical") {
    return `CRITICAL: ${percent}% GPU memory used - cleanup needed!`;
  }
  if (warningLevel.value === "warning") {
    return `Warning: ${percent}% GPU memory used - consider cleanup`;
  }
  return `GPU Memory: ${percent}% used`;
});

function formatMB(mb: number): string {
  if (mb >= 1000) {
    return `${(mb / 1000).toFixed(1)}GB`;
  }
  return `${Math.round(mb)}MB`;
}

function formatCategory(category: string): string {
  const labels: Record<string, string> = {
    model: "AI Models",
    texture: "Textures",
    framebuffer: "Frame Cache",
    particles: "Particles",
    geometry: "3D Geometry",
    audio: "Audio",
    other: "Other",
  };
  return labels[category] || category;
}

async function performCleanup() {
  isCleaningUp.value = true;
  try {
    const target = totalUsage.value * 0.3; // Try to free 30%
    await freeMemory(target);
  } finally {
    isCleaningUp.value = false;
  }
}

onMounted(() => {
  initializeGPUDetection();
});
</script>

<style scoped>
.memory-indicator {
  position: relative;
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 6px 12px;
  background: var(--lattice-surface-2, #1e1e1e);
  border-radius: 4px;
  cursor: pointer;
  font-size: 13px;
  user-select: none;
}

.memory-indicator:hover {
  background: #2a2a2a;
}

.memory-bar {
  width: 60px;
  height: 6px;
  background: #333;
  border-radius: 3px;
  overflow: hidden;
}

.memory-fill {
  height: 100%;
  background: #4a90d9;
  transition: width 0.3s ease, background 0.3s ease;
}

.level-info .memory-fill {
  background: #4a90d9;
}

.level-warning .memory-fill {
  background: #ffc107;
}

.level-critical .memory-fill {
  background: #f44336;
  animation: pulse 1s infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.7; }
}

.memory-text {
  color: var(--lattice-text-secondary, #9CA3AF);
  white-space: nowrap;
  font-weight: 500;
}

.level-warning .memory-text {
  color: #ffc107;
}

.level-critical .memory-text {
  color: #f44336;
  font-weight: 500;
}

/* Details Panel */
.memory-details {
  position: absolute;
  top: 100%;
  right: 0;
  margin-top: 8px;
  width: 280px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 6px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
  z-index: 1000;
}

.details-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 10px 12px;
  border-bottom: 1px solid #444;
  font-weight: 500;
  color: #e0e0e0;
}

.close-details {
  padding: 2px 6px;
  border: none;
  background: transparent;
  color: #888;
  cursor: pointer;
}

.close-details:hover {
  color: #fff;
}

.gpu-info {
  padding: 8px 12px;
  background: #1e1e1e;
  display: flex;
  flex-direction: column;
  gap: 2px;
}

.gpu-info small {
  color: #888;
  font-size: 10px;
}

.category-breakdown {
  padding: 8px 12px;
}

.category-row {
  display: flex;
  justify-content: space-between;
  padding: 4px 0;
  font-size: 12px;
}

.category-name {
  color: #aaa;
}

.category-value {
  color: #e0e0e0;
  font-family: monospace;
}

.warning-box {
  margin: 8px 12px;
  padding: 10px;
  border-radius: 4px;
  font-size: 11px;
}

.warning-box.info {
  background: rgba(74, 144, 217, 0.15);
  border: 1px solid rgba(74, 144, 217, 0.3);
  color: #4a90d9;
}

.warning-box.warning {
  background: rgba(255, 193, 7, 0.15);
  border: 1px solid rgba(255, 193, 7, 0.3);
  color: #ffc107;
}

.warning-box.critical {
  background: rgba(244, 67, 54, 0.15);
  border: 1px solid rgba(244, 67, 54, 0.3);
  color: #f44336;
}

.warning-box p {
  margin: 0 0 8px;
}

.warning-box ul {
  margin: 0;
  padding-left: 16px;
}

.warning-box li {
  margin: 4px 0;
  color: #ccc;
}

.details-footer {
  padding: 8px 12px;
  border-top: 1px solid #444;
}

.cleanup-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  width: 100%;
  padding: 8px;
  border: none;
  background: #3d3d3d;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.cleanup-btn:hover:not(:disabled) {
  background: #4a4a4a;
}

.cleanup-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}
</style>
