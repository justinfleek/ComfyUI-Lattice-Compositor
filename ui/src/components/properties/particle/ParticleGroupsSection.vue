<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Particle Groups</span>
      <button class="add-btn" @click.stop="addGroup" title="Add Group">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <p class="help-text">
        Organize particles into groups for selective collision and connection behaviors.
      </p>

      <!-- Existing Groups -->
      <div v-if="groups.length === 0" class="empty-state">
        No particle groups. Click + to add one.
      </div>

      <div
        v-for="group in groups"
        :key="group.id"
        class="group-item"
        :class="{ selected: selectedGroupId === group.id }"
        @click="selectGroup(group.id)"
      >
        <div class="group-header">
          <label class="enabled-toggle">
            <input
              type="checkbox"
              :checked="group.enabled"
              @change="updateGroup(group.id, 'enabled', ($event.target as HTMLInputElement).checked)"
              @click.stop
            />
          </label>
          <div
            class="color-swatch"
            :style="{ background: rgbaToColor(group.color) }"
            @click.stop="openColorPicker(group.id)"
            title="Click to change color"
          />
          <input
            v-if="editingNameId === group.id"
            type="text"
            v-model="editingName"
            class="name-input"
            @blur="saveGroupName(group.id)"
            @keyup.enter="saveGroupName(group.id)"
            @click.stop
          />
          <span v-else class="group-name" @dblclick.stop="startEditName(group)">
            {{ group.name }}
          </span>
          <button
            v-if="group.id !== 'default'"
            class="remove-btn"
            @click.stop="removeGroup(group.id)"
            title="Remove"
          >
            <i class="pi pi-trash" />
          </button>
        </div>

        <div v-if="selectedGroupId === group.id" class="group-content">
          <!-- Collision Mask -->
          <div class="mask-section">
            <label>Collides With:</label>
            <div class="mask-checkboxes">
              <label
                v-for="otherGroup in groups"
                :key="otherGroup.id"
                class="mask-checkbox"
              >
                <input
                  type="checkbox"
                  :checked="hasCollisionWith(group, otherGroup)"
                  @change="toggleCollision(group.id, otherGroup.id, ($event.target as HTMLInputElement).checked)"
                />
                <span class="mask-label">{{ otherGroup.name }}</span>
              </label>
            </div>
          </div>

          <!-- Connection Mask -->
          <div class="mask-section">
            <label>Connects To:</label>
            <div class="mask-checkboxes">
              <label
                v-for="otherGroup in groups"
                :key="otherGroup.id"
                class="mask-checkbox"
              >
                <input
                  type="checkbox"
                  :checked="hasConnectionWith(group, otherGroup)"
                  @change="toggleConnection(group.id, otherGroup.id, ($event.target as HTMLInputElement).checked)"
                />
                <span class="mask-label">{{ otherGroup.name }}</span>
              </label>
            </div>
          </div>
        </div>
      </div>

      <!-- Info Panel -->
      <div class="info-panel">
        <p><strong>How to use:</strong></p>
        <ul>
          <li>Assign particles to groups in the Emitter settings</li>
          <li>Use collision masks to control which groups bounce off each other</li>
          <li>Use connection masks to control which groups draw lines between them</li>
        </ul>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from "vue";

export interface ParticleGroup {
  id: string;
  name: string;
  enabled: boolean;
  color: [number, number, number, number]; // RGBA 0-1
  collisionMask: number;
  connectionMask: number;
}

const props = defineProps<{
  groups: ParticleGroup[];
  expanded: boolean;
}>();

const emit = defineEmits<{
  toggle: [];
  addGroup: [];
  updateGroup: [id: string, key: string, value: string | number | boolean | [number, number, number, number]];
  removeGroup: [id: string];
}>();

const selectedGroupId = ref<string | null>(null);
const editingNameId = ref<string | null>(null);
const editingName = ref<string>("");

function selectGroup(id: string) {
  selectedGroupId.value = selectedGroupId.value === id ? null : id;
}

function addGroup() {
  emit("addGroup");
}

function updateGroup(id: string, key: string, value: string | number | boolean | [number, number, number, number]) {
  emit("updateGroup", id, key, value);
}

function removeGroup(id: string) {
  if (selectedGroupId.value === id) {
    selectedGroupId.value = null;
  }
  emit("removeGroup", id);
}

function startEditName(group: ParticleGroup) {
  editingNameId.value = group.id;
  editingName.value = group.name;
}

function saveGroupName(id: string) {
  if (editingName.value.trim()) {
    emit("updateGroup", id, "name", editingName.value.trim());
  }
  editingNameId.value = null;
}

function openColorPicker(id: string) {
  // In a real implementation, this would open a color picker dialog
  // For now, we'll cycle through some preset colors
  const group = props.groups.find(g => g.id === id);
  if (!group) return;

  const presetColors: [number, number, number, number][] = [
    [1, 1, 1, 1],       // White
    [1, 0.3, 0.3, 1],   // Red
    [0.3, 1, 0.3, 1],   // Green
    [0.3, 0.3, 1, 1],   // Blue
    [1, 1, 0.3, 1],     // Yellow
    [1, 0.3, 1, 1],     // Magenta
    [0.3, 1, 1, 1],     // Cyan
    [1, 0.6, 0.3, 1],   // Orange
  ];

  const currentIndex = presetColors.findIndex(
    c => c[0] === group.color[0] && c[1] === group.color[1] && c[2] === group.color[2]
  );
  const nextIndex = (currentIndex + 1) % presetColors.length;
  emit("updateGroup", id, "color", presetColors[nextIndex]);
}

function rgbaToColor(rgba: [number, number, number, number]): string {
  const [r, g, b, a] = rgba;
  return `rgba(${Math.round(r * 255)}, ${Math.round(g * 255)}, ${Math.round(b * 255)}, ${a})`;
}

function getGroupIndex(group: ParticleGroup): number {
  return props.groups.findIndex(g => g.id === group.id);
}

function hasCollisionWith(group: ParticleGroup, otherGroup: ParticleGroup): boolean {
  const otherIndex = getGroupIndex(otherGroup);
  return (group.collisionMask & (1 << otherIndex)) !== 0;
}

function hasConnectionWith(group: ParticleGroup, otherGroup: ParticleGroup): boolean {
  const otherIndex = getGroupIndex(otherGroup);
  return (group.connectionMask & (1 << otherIndex)) !== 0;
}

function toggleCollision(groupId: string, otherGroupId: string, enabled: boolean) {
  const group = props.groups.find(g => g.id === groupId);
  const otherGroup = props.groups.find(g => g.id === otherGroupId);
  if (!group || !otherGroup) return;

  const otherIndex = getGroupIndex(otherGroup);
  let newMask = group.collisionMask;

  if (enabled) {
    newMask |= (1 << otherIndex);
  } else {
    newMask &= ~(1 << otherIndex);
  }

  emit("updateGroup", groupId, "collisionMask", newMask);
}

function toggleConnection(groupId: string, otherGroupId: string, enabled: boolean) {
  const group = props.groups.find(g => g.id === groupId);
  const otherGroup = props.groups.find(g => g.id === otherGroupId);
  if (!group || !otherGroup) return;

  const otherIndex = getGroupIndex(otherGroup);
  let newMask = group.connectionMask;

  if (enabled) {
    newMask |= (1 << otherIndex);
  } else {
    newMask &= ~(1 << otherIndex);
  }

  emit("updateGroup", groupId, "connectionMask", newMask);
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

.empty-state {
  text-align: center;
  color: #666;
  font-size: 12px;
  padding: 16px;
}

.group-item {
  background: #1a1a1a;
  border-radius: 6px;
  margin-bottom: 8px;
  overflow: hidden;
  border: 1px solid transparent;
  cursor: pointer;
}

.group-item:hover {
  border-color: #333;
}

.group-item.selected {
  border-color: #555;
}

.group-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 10px;
  background: #222;
}

.enabled-toggle input {
  cursor: pointer;
}

.color-swatch {
  width: 18px;
  height: 18px;
  border-radius: 4px;
  border: 1px solid #444;
  cursor: pointer;
}

.color-swatch:hover {
  border-color: #666;
}

.group-name {
  flex: 1;
  font-size: 12px;
  color: #ccc;
}

.name-input {
  flex: 1;
  background: #333;
  border: 1px solid #555;
  border-radius: 3px;
  padding: 2px 6px;
  color: #fff;
  font-size: 12px;
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

.group-content {
  padding: 10px;
  border-top: 1px solid #333;
}

.mask-section {
  margin-bottom: 12px;
}

.mask-section label {
  display: block;
  font-size: 11px;
  color: #888;
  margin-bottom: 6px;
}

.mask-checkboxes {
  display: flex;
  flex-wrap: wrap;
  gap: 6px;
}

.mask-checkbox {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  background: #2a2a2a;
  border-radius: 4px;
  cursor: pointer;
}

.mask-checkbox:hover {
  background: #333;
}

.mask-checkbox input {
  cursor: pointer;
}

.mask-label {
  font-size: 11px;
  color: #aaa;
}

.info-panel {
  margin-top: 16px;
  padding: 10px;
  background: #1a1a1a;
  border-radius: 6px;
  border: 1px solid #333;
}

.info-panel p {
  margin: 0 0 6px 0;
  font-size: 11px;
  color: #888;
}

.info-panel ul {
  margin: 0;
  padding-left: 16px;
  font-size: 10px;
  color: #666;
  line-height: 1.6;
}
</style>
