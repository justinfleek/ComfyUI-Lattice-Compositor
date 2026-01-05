<template>
  <div class="driver-list" v-if="drivers.length > 0">
    <div class="driver-list-header" @click="expanded = !expanded">
      <span class="expand-icon">{{ expanded ? '▼' : '►' }}</span>
      <span class="title">Property Drivers</span>
      <span class="count">({{ drivers.length }})</span>
    </div>

    <div v-if="expanded" class="driver-items">
      <div
        v-for="driver in drivers"
        :key="driver.id"
        class="driver-item"
        :class="{ disabled: !driver.enabled }"
      >
        <div class="driver-header">
          <button
            class="toggle-btn"
            :class="{ active: driver.enabled }"
            @click="toggleDriver(driver.id)"
            title="Toggle driver"
          >
            ⚡
          </button>

          <div class="driver-info">
            <span class="target">{{ formatProperty(driver.targetProperty) }}</span>
            <span class="arrow">←</span>
            <span class="source" v-if="driver.sourceType === 'property'">
              {{ getSourceLayerName(driver.sourceLayerId) }}.{{ formatProperty(driver.sourceProperty) }}
            </span>
            <span class="source audio" v-else-if="driver.sourceType === 'audio'">
              🎵 {{ driver.audioFeature }}
            </span>
            <span class="source time" v-else-if="driver.sourceType === 'time'">
              ⏱ Time
            </span>
          </div>

          <button
            class="remove-btn"
            @click="removeDriver(driver.id)"
            title="Remove driver"
          >
            ×
          </button>
        </div>

        <div v-if="driver.transforms.length > 0" class="driver-transforms">
          <span
            v-for="(t, i) in driver.transforms"
            :key="i"
            class="transform-chip"
            :title="formatTransform(t)"
          >
            {{ t.type }}
          </span>
        </div>
      </div>
    </div>

    <!-- Add Audio Driver -->
    <div v-if="expanded" class="add-driver-section">
      <button class="add-driver-btn" @click="showAddMenu = !showAddMenu">
        + Add Audio Driver
      </button>

      <div v-if="showAddMenu" class="add-menu">
        <div class="menu-section">
          <label>Audio Feature:</label>
          <select v-model="newDriver.audioFeature">
            <option value="amplitude">Amplitude</option>
            <option value="bass">Bass</option>
            <option value="mid">Mid</option>
            <option value="high">High</option>
            <option value="rms">RMS</option>
          </select>
        </div>

        <div class="menu-section">
          <label>Target Property:</label>
          <select v-model="newDriver.targetProperty">
            <option value="transform.position.x">Position X</option>
            <option value="transform.position.y">Position Y</option>
            <option value="transform.scale.x">Scale X</option>
            <option value="transform.scale.y">Scale Y</option>
            <option value="transform.rotation">Rotation</option>
            <option value="opacity">Opacity</option>
          </select>
        </div>

        <div class="menu-section">
          <label>Scale:</label>
          <input type="number" v-model.number="newDriver.scale" step="10" />
        </div>

        <div class="menu-section">
          <label>Threshold:</label>
          <input type="number" v-model.number="newDriver.threshold" min="0" max="1" step="0.1" />
        </div>

        <div class="menu-actions">
          <button @click="createAudioDriver">Create</button>
          <button @click="showAddMenu = false">Cancel</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import type { DriverTransform, PropertyPath } from "@/services/propertyDriver";
import { useCompositorStore } from "@/stores/compositorStore";

const props = defineProps<{
  layerId: string;
}>();

const store = useCompositorStore();
const _expanded = ref(true);
const showAddMenu = ref(false);

const newDriver = ref({
  audioFeature: "amplitude" as "amplitude" | "bass" | "mid" | "high" | "rms",
  targetProperty: "transform.position.y" as PropertyPath,
  scale: 100,
  threshold: 0,
});

const _drivers = computed(() => {
  return store.getDriversForLayer(props.layerId);
});

function _formatProperty(prop?: PropertyPath | string): string {
  if (!prop) return "?";
  const names: Record<string, string> = {
    "transform.position.x": "Pos X",
    "transform.position.y": "Pos Y",
    "transform.position.z": "Pos Z",
    "transform.scale.x": "Scale X",
    "transform.scale.y": "Scale Y",
    "transform.rotation": "Rotation",
    "transform.rotationX": "Rot X",
    "transform.rotationY": "Rot Y",
    "transform.rotationZ": "Rot Z",
    opacity: "Opacity",
  };
  return names[prop] || prop;
}

function _getSourceLayerName(layerId?: string): string {
  if (!layerId) return "?";
  const layer = store.layers.find((l) => l.id === layerId);
  return layer?.name || layerId.slice(0, 8);
}

function _formatTransform(t: DriverTransform): string {
  switch (t.type) {
    case "scale":
      return `Scale: ${t.factor}`;
    case "offset":
      return `Offset: ${t.amount}`;
    case "clamp":
      return `Clamp: ${t.min}-${t.max}`;
    case "smooth":
      return `Smooth: ${t.smoothing}`;
    case "threshold":
      return `Threshold: ${t.threshold}`;
    default:
      return t.type;
  }
}

function _toggleDriver(driverId: string) {
  store.togglePropertyDriver(driverId);
}

function _removeDriver(driverId: string) {
  store.removePropertyDriver(driverId);
}

function _createAudioDriver() {
  store.createAudioPropertyDriver(
    props.layerId,
    newDriver.value.targetProperty,
    newDriver.value.audioFeature,
    {
      scale: newDriver.value.scale,
      threshold:
        newDriver.value.threshold > 0 ? newDriver.value.threshold : undefined,
    },
  );
  showAddMenu.value = false;
}
</script>

<style scoped>
.driver-list {
  border-top: 1px solid #333;
  margin-top: 8px;
}

.driver-list-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 10px;
  cursor: pointer;
  background: #252525;
}

.driver-list-header:hover {
  background: #2a2a2a;
}

.expand-icon {
  font-size: 11px;
  color: #888;
  width: 10px;
}

.title {
  font-size: 13px;
  font-weight: 500;
  color: #2ecc71;
}

.count {
  font-size: 12px;
  color: #888;
}

.driver-items {
  padding: 4px 0;
}

.driver-item {
  padding: 4px 10px;
  border-bottom: 1px solid #2a2a2a;
}

.driver-item.disabled {
  opacity: 0.5;
}

.driver-header {
  display: flex;
  align-items: center;
  gap: 6px;
}

.toggle-btn {
  background: transparent;
  border: none;
  color: #2ecc71;
  cursor: pointer;
  padding: 2px;
  font-size: 12px;
}

.toggle-btn:not(.active) {
  color: #666;
}

.driver-info {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
  font-size: 12px;
}

.target {
  color: #4a90d9;
  font-weight: 500;
}

.arrow {
  color: #666;
}

.source {
  color: #aaa;
}

.source.audio {
  color: #f1c40f;
}

.source.time {
  color: #9b59b6;
}

.remove-btn {
  background: transparent;
  border: none;
  color: #666;
  cursor: pointer;
  padding: 2px 4px;
  font-size: 14px;
}

.remove-btn:hover {
  color: #e74c3c;
}

.driver-transforms {
  display: flex;
  gap: 4px;
  margin-top: 4px;
  padding-left: 24px;
}

.transform-chip {
  font-size: 11px;
  padding: 1px 4px;
  background: #333;
  border-radius: 2px;
  color: #888;
}

.add-driver-section {
  padding: 8px 10px;
}

.add-driver-btn {
  width: 100%;
  padding: 4px 8px;
  background: #333;
  border: 1px solid #444;
  color: #aaa;
  cursor: pointer;
  border-radius: 3px;
  font-size: 12px;
}

.add-driver-btn:hover {
  background: #444;
  color: #fff;
}

.add-menu {
  margin-top: 8px;
  padding: 8px;
  background: #252525;
  border-radius: 4px;
}

.menu-section {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 6px;
}

.menu-section label {
  width: 80px;
  font-size: 12px;
  color: #888;
}

.menu-section select,
.menu-section input {
  flex: 1;
  padding: 2px 4px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #ccc;
  border-radius: 2px;
  font-size: 12px;
}

.menu-actions {
  display: flex;
  gap: 8px;
  margin-top: 8px;
}

.menu-actions button {
  flex: 1;
  padding: 4px 8px;
  border: none;
  border-radius: 3px;
  font-size: 12px;
  cursor: pointer;
}

.menu-actions button:first-child {
  background: #2ecc71;
  color: #fff;
}

.menu-actions button:last-child {
  background: #555;
  color: #ccc;
}
</style>
