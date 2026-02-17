<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Collision Planes</span>
      <button class="add-btn" @click.stop="addPlane('floor')" title="Add Floor Plane">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <p class="help-text">
        Add floor, wall, and ceiling planes for particles to bounce off.
      </p>

      <!-- Quick Add Buttons -->
      <div class="quick-add-row">
        <button class="quick-add-btn" @click="addPlane('floor')" title="Add horizontal floor">
          <i class="pi pi-chevron-down" />
          Floor
        </button>
        <button class="quick-add-btn" @click="addPlane('ceiling')" title="Add horizontal ceiling">
          <i class="pi pi-chevron-up" />
          Ceiling
        </button>
        <button class="quick-add-btn" @click="addPlane('wall-left')" title="Add left wall">
          <i class="pi pi-chevron-left" />
          Left
        </button>
        <button class="quick-add-btn" @click="addPlane('wall-right')" title="Add right wall">
          <i class="pi pi-chevron-right" />
          Right
        </button>
      </div>

      <!-- Existing Planes -->
      <div v-if="planes.length === 0" class="empty-state">
        No collision planes. Click buttons above to add.
      </div>

      <div
        v-for="plane in planes"
        :key="plane.id"
        class="plane-item"
      >
        <div class="plane-header">
          <label class="enabled-toggle">
            <input
              type="checkbox"
              :checked="plane.enabled"
              @change="updatePlane(plane.id, 'enabled', ($event.target as HTMLInputElement).checked)"
            />
          </label>
          <span class="plane-name">{{ plane.name || plane.id }}</span>
          <button class="remove-btn" @click="removePlane(plane.id)" title="Remove">
            <i class="pi pi-trash" />
          </button>
        </div>

        <div class="plane-content">
          <div class="property-row">
            <label title="Position along the normal axis (Y for floor/ceiling, X for left/right walls)">Position</label>
            <input
              type="range"
              :value="getPlanePosition(plane)"
              min="-1000"
              max="1000"
              step="10"
              @input="updatePlanePosition(plane.id, Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ getPlanePosition(plane) }}</span>
          </div>

          <div class="property-row">
            <label title="How much velocity is preserved after bounce (0 = stop, 1 = perfect bounce)">Bounciness</label>
            <input
              type="range"
              :value="plane.bounciness"
              min="0"
              max="1"
              step="0.05"
              @input="updatePlane(plane.id, 'bounciness', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ (plane.bounciness * 100).toFixed(0) }}%</span>
          </div>

          <div class="property-row">
            <label title="How much horizontal velocity is reduced on contact (0 = slide, 1 = stop)">Friction</label>
            <input
              type="range"
              :value="plane.friction"
              min="0"
              max="1"
              step="0.05"
              @input="updatePlane(plane.id, 'friction', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ (plane.friction * 100).toFixed(0) }}%</span>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from "vue";

export interface CollisionPlane {
  id: string;
  name?: string;
  enabled: boolean;
  point: { x: number; y: number; z: number };
  normal: { x: number; y: number; z: number };
  bounciness: number;
  friction: number;
}

const props = defineProps<{
  planes: CollisionPlane[];
  expanded: boolean;
}>();

const emit = defineEmits<{
  toggle: [];
  addPlane: [type: string];
  updatePlane: [id: string, key: string, value: number | boolean | { x: number; y: number; z: number }];
  removePlane: [id: string];
}>();

function addPlane(type: string) {
  emit("addPlane", type);
}

function updatePlane(id: string, key: string, value: number | boolean) {
  emit("updatePlane", id, key, value);
}

function removePlane(id: string) {
  emit("removePlane", id);
}

function getPlanePosition(plane: CollisionPlane): number {
  // Return the position along the plane's normal axis
  if (Math.abs(plane.normal.y) > 0.5) {
    // Horizontal plane (floor/ceiling) - return Y position
    return plane.point.y;
  } else if (Math.abs(plane.normal.x) > 0.5) {
    // Vertical plane facing X - return X position
    return plane.point.x;
  } else {
    // Vertical plane facing Z - return Z position
    return plane.point.z;
  }
}

function updatePlanePosition(id: string, value: number) {
  const plane = props.planes.find(p => p.id === id);
  if (!plane) return;

  const newPoint = { ...plane.point };
  
  if (Math.abs(plane.normal.y) > 0.5) {
    newPoint.y = value;
  } else if (Math.abs(plane.normal.x) > 0.5) {
    newPoint.x = value;
  } else {
    newPoint.z = value;
  }

  emit("updatePlane", id, "point", newPoint);
}
</script>

<style scoped>
.property-section {
  border-bottom: 1px solid #333;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 10px 12px;
  cursor: pointer;
  user-select: none;
  background: #1e1e1e;
}

.section-header:hover {
  background: #252525;
}

.section-header span {
  flex: 1;
}

.add-btn {
  padding: 4px 8px;
  background: #3a3a3a;
  border: none;
  border-radius: 4px;
  color: #fff;
  cursor: pointer;
}

.add-btn:hover {
  background: #4a4a4a;
}

.section-content {
  padding: 12px;
  background: #181818;
}

.help-text {
  color: #888;
  font-size: 12px;
  margin: 0 0 12px 0;
  line-height: 1.4;
}

.quick-add-row {
  display: flex;
  gap: 6px;
  margin-bottom: 12px;
}

.quick-add-btn {
  flex: 1;
  padding: 6px 8px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  color: #ccc;
  cursor: pointer;
  font-size: 11px;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 4px;
}

.quick-add-btn:hover {
  background: #3a3a3a;
  border-color: #555;
}

.empty-state {
  text-align: center;
  color: #666;
  font-size: 12px;
  padding: 16px;
}

.plane-item {
  background: #1a1a1a;
  border-radius: 6px;
  margin-bottom: 8px;
  overflow: hidden;
}

.plane-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 10px;
  background: #222;
}

.plane-name {
  flex: 1;
  font-size: 12px;
  color: #ccc;
}

.enabled-toggle input {
  cursor: pointer;
}

.remove-btn {
  padding: 4px 6px;
  background: transparent;
  border: none;
  color: #888;
  cursor: pointer;
}

.remove-btn:hover {
  color: #ff6b6b;
}

.plane-content {
  padding: 8px 10px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 6px;
}

.property-row label {
  flex: 0 0 70px;
  font-size: 11px;
  color: #aaa;
}

.property-row input[type="range"] {
  flex: 1;
}

.value-display {
  flex: 0 0 45px;
  text-align: right;
  font-size: 10px;
  color: #888;
}
</style>
