<template>
  <div class="composition-tabs">
    <!-- Breadcrumb navigation for nested compositions -->
    <div v-if="breadcrumbPath.length > 1" class="breadcrumb-nav">
      <template v-for="(crumb, idx) in breadcrumbPath" :key="crumb.id">
        <span
          class="breadcrumb-item"
          :class="{ current: idx === breadcrumbPath.length - 1 }"
          @click="navigateToBreadcrumb(idx)"
        >
          {{ crumb.name }}
        </span>
        <span v-if="idx < breadcrumbPath.length - 1" class="breadcrumb-sep">›</span>
      </template>
      <button class="back-btn" @click="navigateBack" title="Go back (Backspace)">⬅</button>
    </div>

    <div class="tabs-container">
      <div
        v-for="comp in openCompositions"
        :key="comp.id"
        class="tab"
        :class="{
          active: comp.id === activeCompositionId,
          nestedComp: comp.isNestedComp
        }"
        @click="switchToComposition(comp.id)"
        @dblclick="startRename(comp)"
        @contextmenu.prevent="showContextMenu($event, comp)"
      >
        <span v-if="comp.isNestedComp" class="nested-comp-icon" title="Nested Composition">&#x25A0;</span>
        <span v-if="editingId === comp.id" class="tab-name">
          <input
            ref="renameInput"
            v-model="editingName"
            type="text"
            class="rename-input"
            @blur="finishRename"
            @keydown.enter="finishRename"
            @keydown.escape="cancelRename"
            @click.stop
          />
        </span>
        <span v-else class="tab-name">{{ comp.name }}</span>
        <span class="tab-info">{{ formatCompInfo(comp) }}</span>
        <button
          v-if="openCompositions.length > 1"
          class="close-btn"
          @click.stop="closeTab(comp.id)"
          title="Close tab"
        >
          &times;
        </button>
      </div>

      <!-- New Composition Button -->
      <button
        class="new-comp-btn"
        @click="emit('newComposition')"
        title="New Composition (Ctrl+K)"
      >
        +
      </button>
    </div>

    <!-- Context Menu -->
    <Teleport to="body">
      <div
        v-if="contextMenu.visible"
        class="context-menu"
        :style="{ left: contextMenu.x + 'px', top: contextMenu.y + 'px' }"
        @click.stop
      >
        <button @click="openCompSettings">Composition Settings...</button>
        <button @click="renameFromMenu">Rename</button>
        <button @click="duplicateComposition">Duplicate</button>
        <button @click="openInNewTab">Open in New Tab</button>
        <hr />
        <button @click="setAsMainComp" :disabled="getContextMenuCompId() === mainCompositionId">
          Set as Main Composition
        </button>
        <hr />
        <button
          @click="deleteComposition"
          :disabled="getContextMenuCompId() === mainCompositionId"
          class="danger"
        >
          Delete Composition
        </button>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { computed, nextTick, onMounted, onUnmounted, ref } from "vue";
import { useCompositionStore } from "@/stores/compositionStore";
import type { CompositionStoreAccess } from "@/stores/compositionStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import type { Composition } from "@/types/project";
import { generateKeyframeId } from "@/utils/uuid5";
import { regenerateKeyframeIds } from "@/stores/layerStore/crud";

const emit = defineEmits<{
  (e: "newComposition"): void;
  (e: "openCompositionSettings"): void;
}>();

const compositionStore = useCompositionStore();
const projectStore = useProjectStore();
const selectionStore = useSelectionStore();

// Helper to create CompositionStoreAccess for composition operations
function getCompositionStoreAccess(): CompositionStoreAccess {
  return {
    project: {
      compositions: projectStore.project.compositions,
      mainCompositionId: projectStore.project.mainCompositionId,
      composition: projectStore.project.composition,
      meta: projectStore.project.meta,
    },
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    switchComposition: (compId: string) => {
      compositionStore.switchComposition(getCompositionStoreAccess(), compId);
    },
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Computed from stores
const breadcrumbPath = computed(() => {
  return projectStore.compositionBreadcrumbs.map((id: string) => {
    const comp = projectStore.project.compositions[id];
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const compName = (comp != null && typeof comp === "object" && "name" in comp && typeof comp.name === "string") ? comp.name : undefined;
    return { id, name: compName != null ? compName : id };
  });
});

// State
const editingId = ref<string | null>(null);
const editingName = ref("");
const renameInput = ref<HTMLInputElement | null>(null);

const contextMenu = ref<{
  visible: boolean;
  x: number;
  y: number;
  comp: Composition | null;
}>({
  visible: false,
  x: 0,
  y: 0,
  comp: null,
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
function getContextMenuCompId(): string | undefined {
  const comp = contextMenu.value.comp;
  return (comp != null && typeof comp === "object" && "id" in comp && typeof comp.id === "string") ? comp.id : undefined;
}

// Computed
const openCompositions = computed(() => {
  return projectStore.openCompositionIds
    .map((id: string) => projectStore.project.compositions[id])
    .filter(Boolean) as Composition[];
});
const activeCompositionId = computed(() => projectStore.activeCompositionId);
const mainCompositionId = computed(() => projectStore.project.mainCompositionId);

// Methods
function switchToComposition(compId: string) {
  compositionStore.switchComposition(getCompositionStoreAccess(), compId);
}

function closeTab(compId: string) {
  compositionStore.closeCompositionTab(getCompositionStoreAccess(), compId);
}

// Breadcrumb navigation
function navigateToBreadcrumb(idx: number) {
  compositionStore.navigateToBreadcrumb(getCompositionStoreAccess(), idx);
}

function navigateBack() {
  compositionStore.navigateBack(getCompositionStoreAccess());
}

function formatCompInfo(comp: Composition): string {
  const s = comp.settings;
  return `${s.width}x${s.height} ${s.fps}fps`;
}

function startRename(comp: Composition) {
  editingId.value = comp.id;
  editingName.value = comp.name;
  nextTick(() => {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const renameInputValue = renameInput.value;
    if (renameInputValue != null && typeof renameInputValue === "object" && typeof renameInputValue.focus === "function") {
      renameInputValue.focus();
    }
    if (renameInputValue != null && typeof renameInputValue === "object" && typeof renameInputValue.select === "function") {
      renameInputValue.select();
    }
  });
}

function finishRename() {
  if (editingId.value && editingName.value.trim()) {
    compositionStore.renameComposition(
      getCompositionStoreAccess(),
      editingId.value,
      editingName.value.trim(),
    );
  }
  editingId.value = null;
  editingName.value = "";
}

function cancelRename() {
  editingId.value = null;
  editingName.value = "";
}

function showContextMenu(event: MouseEvent, comp: Composition) {
  contextMenu.value = {
    visible: true,
    x: event.clientX,
    y: event.clientY,
    comp,
  };
}

function hideContextMenu() {
  contextMenu.value.visible = false;
  contextMenu.value.comp = null;
}

function openCompSettings() {
  // Switch to the composition first if not active
  if (
    contextMenu.value.comp &&
    contextMenu.value.comp.id !== activeCompositionId.value
  ) {
    compositionStore.switchComposition(
      getCompositionStoreAccess(),
      contextMenu.value.comp.id,
    );
  }
  emit("openCompositionSettings");
  hideContextMenu();
}

function renameFromMenu() {
  if (contextMenu.value.comp) {
    startRename(contextMenu.value.comp);
  }
  hideContextMenu();
}

function duplicateComposition() {
  if (contextMenu.value.comp) {
    const original = contextMenu.value.comp;
    const newComp = compositionStore.createComposition(
      `${original.name} Copy`,
      original.settings,
      original.isNestedComp,
    );

    // Deep clone and copy layers with new IDs
    for (const layer of original.layers) {
      const clonedLayer = structuredClone(layer);

      // Generate new IDs for layer and its properties
      clonedLayer.id = `layer_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

      // Regenerate keyframe IDs deterministically (like layer duplication)
      regenerateKeyframeIds(clonedLayer);

      // Add cloned layer to new composition
      newComp.layers.push(clonedLayer);
    }

    console.log(
      "[CompositionTabs] Duplicated:",
      newComp.name,
      "with",
      newComp.layers.length,
      "layers",
    );
  }
  hideContextMenu();
}

function openInNewTab() {
  if (contextMenu.value.comp) {
    compositionStore.switchComposition(getCompositionStoreAccess(), contextMenu.value.comp.id);
  }
  hideContextMenu();
}

function setAsMainComp() {
  if (contextMenu.value.comp) {
    projectStore.project.mainCompositionId = contextMenu.value.comp.id;
    projectStore.pushHistory();
    console.log(
      "[CompositionTabs] Set main composition:",
      contextMenu.value.comp.name,
    );
  }
  hideContextMenu();
}

function deleteComposition() {
  if (
    contextMenu.value.comp &&
    contextMenu.value.comp.id !== mainCompositionId.value
  ) {
    compositionStore.deleteComposition(getCompositionStoreAccess(), contextMenu.value.comp.id);
  }
  hideContextMenu();
}

// Close context menu on outside click
function handleOutsideClick() {
  if (contextMenu.value.visible) {
    hideContextMenu();
  }
}

onMounted(() => {
  document.addEventListener("click", handleOutsideClick);
});

onUnmounted(() => {
  document.removeEventListener("click", handleOutsideClick);
});
</script>

<style scoped>
.composition-tabs {
  display: flex;
  align-items: center;
  background: #252525;
  border-bottom: 1px solid #333;
  height: 28px;
  padding: 0 4px;
  overflow-x: auto;
  overflow-y: hidden;
}

.tabs-container {
  display: flex;
  align-items: center;
  gap: 2px;
  min-width: max-content;
}

.tab {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 8px;
  background: #1e1e1e;
  border: 1px solid #333;
  border-bottom: none;
  border-radius: 4px 4px 0 0;
  cursor: pointer;
  font-size: 13px;
  color: #888;
  max-width: 200px;
  white-space: nowrap;
  user-select: none;
}

.tab:hover {
  background: #2a2a2a;
  color: #aaa;
}

.tab.active {
  background: #1a1a1a;
  color: #e0e0e0;
  border-color: #4a90d9;
  border-bottom: 1px solid #1a1a1a;
  margin-bottom: -1px;
}

.tab.nestedComp {
  font-style: italic;
}

.nested-comp-icon {
  font-size: 11px;
  color: #6b8bb8;
}

.tab-name {
  overflow: hidden;
  text-overflow: ellipsis;
  max-width: 120px;
}

.tab-info {
  font-size: 11px;
  color: #666;
}

.close-btn {
  width: 14px;
  height: 14px;
  padding: 0;
  border: none;
  background: transparent;
  color: #666;
  font-size: 14px;
  line-height: 1;
  cursor: pointer;
  border-radius: 2px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.close-btn:hover {
  background: #444;
  color: #fff;
}

.new-comp-btn {
  width: 22px;
  height: 22px;
  padding: 0;
  border: 1px dashed #444;
  background: transparent;
  color: #666;
  font-size: 14px;
  cursor: pointer;
  border-radius: 4px;
  margin-left: 4px;
}

.new-comp-btn:hover {
  background: #333;
  color: #aaa;
  border-color: #555;
}

.rename-input {
  width: 100px;
  padding: 1px 4px;
  border: 1px solid #4a90d9;
  background: #1a1a1a;
  color: #e0e0e0;
  font-size: 13px;
  border-radius: 2px;
}

.rename-input:focus {
  outline: none;
}

/* Context Menu */
.context-menu {
  position: fixed;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  z-index: 1000;
  min-width: 160px;
  padding: 4px 0;
}

.context-menu button {
  display: block;
  width: 100%;
  padding: 6px 12px;
  border: none;
  background: transparent;
  color: #e0e0e0;
  font-size: 13px;
  text-align: left;
  cursor: pointer;
}

.context-menu button:hover:not(:disabled) {
  background: #3a5070;
}

.context-menu button:disabled {
  color: #555;
  cursor: not-allowed;
}

.context-menu button.danger {
  color: #e57373;
}

.context-menu button.danger:hover:not(:disabled) {
  background: #5a3030;
}

.context-menu hr {
  border: none;
  border-top: 1px solid #444;
  margin: 4px 0;
}

/* Breadcrumb Navigation */
.breadcrumb-nav {
  display: flex;
  align-items: center;
  gap: 2px;
  padding: 0 8px;
  margin-right: 8px;
  border-right: 1px solid #444;
  font-size: 13px;
}

.breadcrumb-item {
  color: #888;
  cursor: pointer;
  padding: 2px 4px;
  border-radius: 2px;
  white-space: nowrap;
  max-width: 100px;
  overflow: hidden;
  text-overflow: ellipsis;
}

.breadcrumb-item:hover {
  background: #333;
  color: #aaa;
}

.breadcrumb-item.current {
  color: #e0e0e0;
  cursor: default;
  font-weight: 500;
}

.breadcrumb-item.current:hover {
  background: transparent;
}

.breadcrumb-sep {
  color: #555;
  font-size: 12px;
}

.back-btn {
  width: 20px;
  height: 20px;
  padding: 0;
  border: none;
  background: transparent;
  color: #888;
  font-size: 12px;
  cursor: pointer;
  border-radius: 2px;
  display: flex;
  align-items: center;
  justify-content: center;
  margin-left: 4px;
}

.back-btn:hover {
  background: #333;
  color: #e0e0e0;
}
</style>
