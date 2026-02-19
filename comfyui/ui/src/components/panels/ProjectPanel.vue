<template>
  <div class="project-panel">
    <div class="panel-header">
      <span class="panel-title">Project</span>
      <div class="header-actions">
        <button @click="triggerFileImport" title="Import File (Ctrl+I)">📥</button>
        <div class="dropdown-container">
          <button @click="showNewMenu = !showNewMenu" title="New Item">+</button>
          <div v-if="showNewMenu" class="dropdown-menu">
            <button @click="createNewComposition"><PhFilmSlate class="menu-icon" /> New Composition</button>
            <button @click="createNewFolder"><PhFolder class="menu-icon" /> New Folder</button>
            <hr class="menu-divider" />
            <button @click="createNewSolid"><span class="menu-icon">⬜</span> New Solid</button>
            <button @click="createNewText"><span class="menu-icon">🔤</span> New Text</button>
            <button @click="createNewControl"><span class="menu-icon">⊕</span> New Control</button>
            <button @click="createNewSpline"><span class="menu-icon">✏️</span> New Spline</button>
            <button @click="createNewModel"><span class="menu-icon">🧊</span> New 3D Model</button>
            <button @click="createNewPointCloud"><span class="menu-icon">☁️</span> New Point Cloud</button>
            <hr class="menu-divider" />
            <button @click="openDecomposeDialog"><PhSparkle class="menu-icon" /> AI Layer Decompose</button>
            <button @click="openVectorizeDialog"><span class="menu-icon">✒️</span> Vectorize Image</button>
            <hr class="menu-divider" />
            <button @click="cleanupUnusedAssets"><span class="menu-icon">🗑️</span> Remove Unused Assets</button>
          </div>
        </div>
        <button @click="showSearch = !showSearch" title="Search">🔍</button>
      </div>
    </div>

    <!-- Decompose Dialog -->
    <DecomposeDialog
      v-if="showDecomposeDialog"
      @close="showDecomposeDialog = false"
      @decomposed="onDecomposed"
    />

    <!-- Vectorize Dialog -->
    <VectorizeDialog
      :visible="showVectorizeDialog"
      @close="showVectorizeDialog = false"
      @created="onVectorized"
    />

    <!-- FPS Mismatch Dialog -->
    <FpsMismatchDialog
      :visible="showFpsMismatchDialog"
      :file-name="pendingFpsMismatchFileName"
      :imported-fps="pendingFpsMismatchImportedFps"
      :composition-fps="pendingFpsMismatchCompositionFps"
      :video-duration="pendingFpsMismatchVideoDuration"
      @match="handleFpsMismatchMatch"
      @conform="handleFpsMismatchConform"
      @cancel="handleFpsMismatchCancel"
    />

    <!-- FPS Select Dialog (for unknown fps) -->
    <FpsSelectDialog
      :visible="showFpsSelectDialog"
      :file-name="pendingFpsUnknownFileName"
      :video-duration="pendingFpsUnknownVideoDuration"
      @confirm="handleFpsSelected"
      @cancel="handleFpsSelectCancel"
    />

    <!-- Hidden file input -->
    <input
      ref="fileInputRef"
      type="file"
      multiple
      accept="image/*,video/*,audio/*,.json,.csv,.tsv,.mgjson"
      style="display: none"
      @change="handleFileImport"
    />

    <div v-if="showSearch" class="search-bar">
      <input
        type="text"
        v-model="searchQuery"
        placeholder="Search project..."
        class="search-input"
      />
    </div>

    <!-- Asset Preview Area -->
    <div v-if="selectedPreview" class="preview-area">
      <div class="preview-thumbnail">
        <img
          v-if="selectedPreview.type === 'image'"
          :src="selectedPreviewUrl"
          :alt="selectedPreview.name"
        />
        <video
          v-else-if="selectedPreview.type === 'video'"
          :src="selectedPreviewUrl"
          muted
          loop
          autoplay
        />
        <div v-else class="preview-placeholder">
          <span class="preview-icon">{{ selectedPreview.icon }}</span>
        </div>
      </div>
      <div class="preview-info">
        <div class="preview-name">{{ selectedPreview.name }}</div>
        <div class="preview-details">{{ selectedPreview.details }}</div>
      </div>
    </div>

    <div class="panel-content">
      <!-- Folders -->
      <div class="folder-tree">
        <div
          v-for="folder in filteredFolders"
          :key="folder.id"
          class="folder-item"
        >
          <div
            class="folder-header"
            :class="{ selected: selectedItem === folder.id }"
            @click="selectItem(folder.id)"
            @dblclick="toggleFolder(folder.id)"
          >
            <span class="expand-icon" @click.stop="toggleFolder(folder.id)">
              {{ expandedFolders.includes(folder.id) ? '▼' : '►' }}
            </span>
            <PhFolder class="folder-icon" />
            <span class="folder-name">{{ folder.name }}</span>
            <span class="item-count">{{ folder.items.length }}</span>
          </div>

          <div v-if="expandedFolders.includes(folder.id)" class="folder-contents">
            <div
              v-for="item in folder.items"
              :key="item.id"
              class="project-item"
              :class="{ selected: selectedItem === item.id }"
              @click="selectItem(item.id)"
              @dblclick="openItem(item)"
              draggable="true"
              @dragstart="onDragStart(item, $event)"
            >
              <span class="item-icon">{{ getItemIcon(item.type) }}</span>
              <span class="item-name">{{ item.name }}</span>
              <span class="item-info">{{ getItemInfo(item) }}</span>
            </div>
          </div>
        </div>

        <!-- Root Items (not in folders) -->
        <div
          v-for="item in filteredRootItems"
          :key="item.id"
          class="project-item"
          :class="{ selected: selectedItem === item.id }"
          @click="selectItem(item.id)"
          @dblclick="openItem(item)"
          draggable="true"
          @dragstart="onDragStart(item, $event)"
        >
          <span class="item-icon">{{ getItemIcon(item.type) }}</span>
          <span class="item-name">{{ item.name }}</span>
          <span class="item-info">{{ getItemInfo(item) }}</span>
        </div>
      </div>

      <!-- Empty State -->
      <div v-if="items.length === 0" class="empty-state">
        <p>No items in project</p>
        <p class="hint">Import footage or create compositions</p>
      </div>
    </div>

    <!-- Footer with item details -->
    <div v-if="selectedItemDetails" class="panel-footer">
      <div class="item-details">
        <span class="detail-label">{{ selectedItemDetails.name }}</span>
        <span class="detail-info">{{ selectedItemDetails.info }}</span>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { importDataFromFile } from "@/services/dataImport";
import type { DecomposedLayer } from "@/services/layerDecomposition";
import { exportLayers, exportSplineLayer } from "@/services/svgExport";
import type {
  VideoImportFpsMismatch,
  VideoImportFpsUnknown,
} from "@/stores/videoStore";
import { useVideoStore } from "@/stores/videoStore";
import { useAudioStore } from "@/stores/audioStore";
import { useProjectStore } from "@/stores/projectStore";
import { useLayerStore } from "@/stores/layerStore";
import { useSelectionStore } from "@/stores/selectionStore";
import {
  getDataFileType,
  isCSVAsset,
  isJSONAsset,
  isSupportedDataFile,
} from "@/types/dataAsset";

const emit = defineEmits<(e: "openCompositionSettings") => void>();

interface ProjectItem {
  id: string;
  name: string;
  type: "composition" | "footage" | "solid" | "audio" | "folder" | "data";
  width?: number;
  height?: number;
  duration?: number;
  fps?: number;
  dataType?: "json" | "csv" | "tsv" | "mgjson"; // For data files
  dataInfo?: string; // Summary info like "5 rows, 3 columns"
}

interface Folder {
  id: string;
  name: string;
  items: ProjectItem[];
}

const projectStore = useProjectStore();
const layerStore = useLayerStore();
const selectionStore = useSelectionStore();
const compositionStore = useCompositionStore();
const audioStore = useAudioStore();

// Helper function to create CompositionStoreAccess
function getCompositionStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    switchComposition: (id: string) => compositionStore.switchComposition(getCompositionStoreAccess(), id),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// Refs
const fileInputRef = ref<HTMLInputElement | null>(null);

// State
const showSearch = ref(false);
const showNewMenu = ref(false);
const showDecomposeDialog = ref(false);
const showVectorizeDialog = ref(false);
const showFpsMismatchDialog = ref(false);
const pendingFpsMismatch = ref<VideoImportFpsMismatch | null>(null);
const showFpsSelectDialog = ref(false);
const pendingFpsUnknown = ref<VideoImportFpsUnknown | null>(null);
const searchQuery = ref("");
const selectedItem = ref<string | null>(null);
const expandedFolders = ref<string[]>(["compositions", "footage"]);
const customFolders = ref<Folder[]>([]);

// Check if selected layer is a spline layer
const hasSelectedSplineLayer = computed(() => {
  const selectedLayerIds = selectionStore.selectedLayerIds;
  if (selectedLayerIds.length === 0) return false;

  const layers = projectStore.getActiveCompLayers();
  const selectedLayer = layers.find((l) => l.id === selectedLayerIds[0]);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (selectedLayer != null && typeof selectedLayer === "object" && "type" in selectedLayer && selectedLayer.type === "spline");
});

// Reactive storage for footage items (persists across re-renders)
const footageItems = ref<ProjectItem[]>([]);

// Solid items derived from layers in active composition
const solidItems = computed<ProjectItem[]>(() => {
  const layers = projectStore.getActiveCompLayers();
  return layers
    .filter((l) => l.type === "solid")
    .map((l) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const data = l.data as { width?: number; height?: number; color?: string };
      const width = (data != null && typeof data === "object" && "width" in data && typeof data.width === "number") ? data.width : undefined;
      const height = (data != null && typeof data === "object" && "height" in data && typeof data.height === "number") ? data.height : undefined;
      const color = (data != null && typeof data === "object" && "color" in data && typeof data.color === "string") ? data.color : undefined;
      return {
        id: l.id,
        name: l.name,
        type: "solid" as const,
        width: width || projectStore.getWidth(),
        height: height || projectStore.getHeight(),
        color: color || "#808080",
      };
    });
});

// Folders computed from store - reactively updates when compositions change
const folders = computed<Folder[]>(() => {
  // Get all compositions from the store
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || {}
  const compositionsRaw = projectStore.project.compositions;
  const compositionsObj = (compositionsRaw !== null && compositionsRaw !== undefined && typeof compositionsRaw === "object" && compositionsRaw !== null) ? compositionsRaw : {};
  const compositions = Object.values(compositionsObj).map(
    (comp) => ({
      id: comp.id,
      name: comp.name,
      type: "composition" as const,
      width: comp.settings.width,
      height: comp.settings.height,
      fps: comp.settings.fps,
      duration: comp.settings.frameCount,
    }),
  );

  const systemFolders: Folder[] = [
    {
      id: "compositions",
      name: "Compositions",
      items:
        compositions.length > 0
          ? compositions
          : [
              {
                id: "comp-main",
                // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
                name: (() => {
                  const activeComp = projectStore.getActiveComp();
                  return (activeComp != null && typeof activeComp === "object" && "name" in activeComp && typeof activeComp.name === "string") ? activeComp.name : "Main Comp";
                })(),
                type: "composition" as const,
                width: projectStore.getWidth(),
                height: projectStore.getHeight(),
                fps: projectStore.getFps(),
                duration: projectStore.getFrameCount(),
              },
            ],
    },
    {
      id: "footage",
      name: "Footage",
      items: footageItems.value,
    },
    {
      id: "solids",
      name: "Solids",
      items: solidItems.value, // Now computed from projectStore.getActiveCompLayers()
    },
  ];

  return [...systemFolders, ...customFolders.value];
});

const items = ref<ProjectItem[]>([]);

// Computed
const filteredFolders = computed(() => {
  if (!searchQuery.value) return folders.value;

  const query = searchQuery.value.toLowerCase();
  return folders.value
    .map((folder) => ({
      ...folder,
      items: folder.items.filter((item) =>
        item.name.toLowerCase().includes(query),
      ),
    }))
    .filter(
      (folder) =>
        folder.items.length > 0 || folder.name.toLowerCase().includes(query),
    );
});

const filteredRootItems = computed(() => {
  if (!searchQuery.value) return items.value;

  const query = searchQuery.value.toLowerCase();
  return items.value.filter((item) => item.name.toLowerCase().includes(query));
});

// System F/Omega: Computed property that throws explicit errors instead of returning null
const selectedPreviewRaw = computed(() => {
  if (!selectedItem.value) {
    throw new Error(
      `[ProjectPanel] Cannot get selected preview: No item selected. ` +
      `Select an item first to view its preview.`
    );
  }

  // Find the item
  let item: ProjectItem | null = null;
  for (const folder of folders.value) {
    const found = folder.items.find((i) => i.id === selectedItem.value);
    if (found) {
      item = found;
      break;
    }
  }
  if (!item) {
    item = items.value.find((i) => i.id === selectedItem.value) || null;
  }
  
  // System F/Omega: Throw explicit error when item not found
  if (!item) {
    throw new Error(
      `[ProjectPanel] Cannot get selected preview: Item not found. ` +
      `Selected item ID: ${selectedItem.value}. ` +
      `Item must exist in folders or root items.`
    );
  }

  // Get asset data if available
  const asset = projectStore.project.assets[item.id];

  if (item.type === "footage" && asset) {
    if (asset.type === "image") {
      return {
        type: "image",
        url: asset.data as string,
        name: item.name,
        details:
          asset.width && asset.height
            ? `${asset.width} × ${asset.height}`
            : "Image",
        icon: "🖼",
      };
    } else if (asset.type === "video") {
      return {
        type: "video",
        url: asset.data as string,
        name: item.name,
        details: `${item.width || "?"} × ${item.height || "?"} • ${item.fps || "?"}fps`,
        icon: "🎬",
      };
    }
  } else if (item.type === "composition") {
    const comp = compositionStore.getComposition(getCompositionStoreAccess(), item.id);
    return {
      type: "composition",
      url: null,
      name: item.name,
      details: comp
        ? `${comp.settings.width} × ${comp.settings.height} • ${comp.settings.fps}fps`
        : "Composition",
      icon: "🎬",
    };
  } else if (item.type === "solid") {
    return {
      type: "solid",
      url: null,
      name: item.name,
      details: "Solid Layer",
      icon: "⬜",
    };
  } else if (item.type === "audio") {
    return {
      type: "audio",
      url: null,
      name: item.name,
      details: "Audio File",
      icon: "🔊",
    };
  }

  // System F/Omega: Throw explicit error for unknown item types
  throw new Error(
    `[ProjectPanel] Cannot get selected preview: Unknown item type. ` +
    `Item type: "${item.type}", item ID: ${item.id}, name: ${item.name}. ` +
    `Item type must be footage, composition, solid, or audio. Wrap in try/catch if "unknown type" is an expected state.`
  );
});

// Wrapper computed property for template use - catches errors and returns null for conditional rendering
// System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
// Template uses v-if="selectedPreview" which requires null for conditional rendering
const selectedPreview = computed(() => {
  try {
    return selectedPreviewRaw.value;
  } catch {
    // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
    // Template uses v-if which requires null for conditional rendering
    // This is the ONLY place where null is returned - all other code throws explicit errors
    return null;
  }
});

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
// Computed properties for FpsMismatchDialog props
const pendingFpsMismatchFileName = computed(() => {
  const mismatch = pendingFpsMismatch.value;
  return (mismatch !== null && typeof mismatch === "object" && "fileName" in mismatch && typeof mismatch.fileName === "string") ? mismatch.fileName : "";
});
const pendingFpsMismatchImportedFps = computed(() => {
  const mismatch = pendingFpsMismatch.value;
  return (mismatch !== null && typeof mismatch === "object" && "importedFps" in mismatch && typeof mismatch.importedFps === "number" && Number.isFinite(mismatch.importedFps)) ? mismatch.importedFps : 30;
});
const pendingFpsMismatchCompositionFps = computed(() => {
  const mismatch = pendingFpsMismatch.value;
  return (mismatch !== null && typeof mismatch === "object" && "compositionFps" in mismatch && typeof mismatch.compositionFps === "number" && Number.isFinite(mismatch.compositionFps)) ? mismatch.compositionFps : 16;
});
const pendingFpsMismatchVideoDuration = computed(() => {
  const mismatch = pendingFpsMismatch.value;
  return (mismatch !== null && typeof mismatch === "object" && "videoDuration" in mismatch && typeof mismatch.videoDuration === "number" && Number.isFinite(mismatch.videoDuration)) ? mismatch.videoDuration : 0;
});

// Computed properties for FpsSelectDialog props
const pendingFpsUnknownFileName = computed(() => {
  const unknown = pendingFpsUnknown.value;
  return (unknown !== null && typeof unknown === "object" && "fileName" in unknown && typeof unknown.fileName === "string") ? unknown.fileName : "";
});
const pendingFpsUnknownVideoDuration = computed(() => {
  const unknown = pendingFpsUnknown.value;
  return (unknown !== null && typeof unknown === "object" && "videoDuration" in unknown && typeof unknown.videoDuration === "number" && Number.isFinite(unknown.videoDuration)) ? unknown.videoDuration : 0;
});

// Computed property for selectedPreview.url
const selectedPreviewUrl = computed(() => {
  const preview = selectedPreview.value;
  if (preview === null || typeof preview !== "object" || !("url" in preview)) {
    return undefined;
  }
  const url = preview.url;
  return (typeof url === "string" && url.length > 0) ? url : undefined;
});

// System F/Omega: Computed property that throws explicit errors instead of returning null
const selectedItemDetailsRaw = computed(() => {
  if (!selectedItem.value) {
    throw new Error(
      `[ProjectPanel] Cannot get selected item details: No item selected. ` +
      `Select an item first to view its details.`
    );
  }

  // Find in folders
  for (const folder of folders.value) {
    const item = folder.items.find((i) => i.id === selectedItem.value);
    if (item) {
      return {
        name: item.name,
        info: getItemInfo(item),
      };
    }
  }

  // Find in root items
  const item = items.value.find((i) => i.id === selectedItem.value);
  if (item) {
    return {
      name: item.name,
      info: getItemInfo(item),
    };
  }

  // System F/Omega: Throw explicit error when item not found
  throw new Error(
    `[ProjectPanel] Cannot get selected item details: Item not found. ` +
    `Selected item ID: ${selectedItem.value}. ` +
    `Item must exist in folders or root items.`
  );
});

// Wrapper computed property for template use - catches errors and returns null for conditional rendering
// System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
// Template uses v-if="selectedItemDetails" which requires null for conditional rendering
const selectedItemDetails = computed(() => {
  try {
    return selectedItemDetailsRaw.value;
  } catch {
    // System F/Omega EXCEPTION: Returning null here is necessary for Vue template compatibility
    // Template uses v-if which requires null for conditional rendering
    // This is the ONLY place where null is returned - all other code throws explicit errors
    return null;
  }
});

// Methods
function toggleFolder(folderId: string) {
  const index = expandedFolders.value.indexOf(folderId);
  if (index >= 0) {
    expandedFolders.value.splice(index, 1);
  } else {
    expandedFolders.value.push(folderId);
  }
}

function selectItem(itemId: string) {
  selectedItem.value = itemId;
}

function openItem(item: ProjectItem) {
  if (item.type === "composition") {
    // Switch to composition (opens in timeline and viewer)
    compositionStore.switchComposition(getCompositionStoreAccess(), item.id);
  } else if (item.type === "folder") {
    // Toggle folder expansion
    toggleFolder(item.id);
  } else if (item.type === "footage" || item.type === "solid") {
    // Add footage/solid as a new layer at the current frame
    const asset = projectStore.project.assets[item.id];
    if (asset) {
      const layerType = item.type === "solid" ? "solid" : "image";
      const layer = layerStore.createLayer(layerType, item.name);
      if (layer && asset.data) {
        // Link the asset to the layer AND provide the source URL
        layerStore.updateLayerData(layer.id, {
          assetId: item.id,
          source: asset.data, // The actual image/video URL
        });
      }
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const layerId = (layer != null && typeof layer === "object" && "id" in layer && typeof layer.id === "string") ? layer.id : undefined;
      console.log(
        "[ProjectPanel] Created layer from asset:",
        layerId,
        item.name,
      );
    }
  } else if (item.type === "audio") {
    // Load audio into the audio panel
    const asset = projectStore.project.assets[item.id];
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const assetData = (asset != null && typeof asset === "object" && "data" in asset && asset.data != null) ? asset.data : undefined;
    if (assetData) {
      // Fetch the audio data and load it
      fetch(assetData as string)
        .then((response) => response.blob())
        .then((blob) => {
          const file = new File([blob], item.name, {
            type: blob.type || "audio/mpeg",
          });
          const activeComp = projectStore.getActiveComp();
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const fps = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object" && "fps" in activeComp.settings && typeof activeComp.settings.fps === "number") ? activeComp.settings.fps : 16;
          audioStore.loadAudio(file, fps);
        })
        .catch((err) =>
          console.error("[ProjectPanel] Failed to load audio:", err),
        );
    }
  }
}

function createNewComposition() {
  showNewMenu.value = false;
  emit("openCompositionSettings");
}

function createNewFolder() {
  showNewMenu.value = false;
  const folderNumber = customFolders.value.length + 1;
  const newFolder: Folder = {
    id: `folder_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`,
    name: `Folder ${folderNumber}`,
    items: [],
  };
  customFolders.value.push(newFolder);
  expandedFolders.value.push(newFolder.id);
  selectedItem.value = newFolder.id;
  console.log("[ProjectPanel] Created folder:", newFolder.name);
}

function createNewSolid() {
  showNewMenu.value = false;
  const layer = layerStore.createLayer("solid", "Solid");
  console.log("[ProjectPanel] Created solid layer:", layer.id);
}

function createNewText() {
  showNewMenu.value = false;
  const layer = layerStore.createTextLayer("Text");
  console.log("[ProjectPanel] Created text layer:", layer.id);
}

function createNewControl() {
  showNewMenu.value = false;
  const layer = layerStore.createLayer("control", "Control");
  console.log("[ProjectPanel] Created control layer:", layer.id);
}

function createNewSpline() {
  showNewMenu.value = false;
  const layer = layerStore.createSplineLayer();
  console.log("[ProjectPanel] Created spline layer:", layer.id);
}

function createNewModel() {
  showNewMenu.value = false;
  const layer = layerStore.createLayer("model", "3D Model");
  console.log("[ProjectPanel] Created model layer:", layer.id);
}

function createNewPointCloud() {
  showNewMenu.value = false;
  const layer = layerStore.createLayer("pointcloud", "Point Cloud");
  console.log("[ProjectPanel] Created point cloud layer:", layer.id);
}

function openDecomposeDialog() {
  showNewMenu.value = false;
  showDecomposeDialog.value = true;
}

function openVectorizeDialog() {
  showNewMenu.value = false;
  showVectorizeDialog.value = true;
}

function onDecomposed(layers: DecomposedLayer[]) {
  console.log("[ProjectPanel] Image decomposed into", layers.length, "layers");
}

function onVectorized(layerIds: string[]) {
  console.log("[ProjectPanel] Created", layerIds.length, "vectorized layers");
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                              // fps // mismatch // handlers
// ═══════════════════════════════════════════════════════════════════════════

async function handleFpsMismatchMatch() {
  if (!pendingFpsMismatch.value) return;

  const result = pendingFpsMismatch.value;
  console.log(
    "[ProjectPanel] FPS mismatch: User chose MATCH -",
    result.importedFps,
    "fps",
  );

  // Complete import with match (precomp existing, change comp fps)
  const videoStore = useVideoStore();
  const layer = await videoStore.completeVideoImportWithMatch(
    result.pendingImport,
    result.fileName,
  );

  if (layer) {
    // Add to footage items
    footageItems.value.push({
      id: layer.id,
      name: result.fileName,
      type: "footage",
      width: projectStore.getWidth(),
      height: projectStore.getHeight(),
      duration: projectStore.getFrameCount(),
      fps: projectStore.getFps(),
    });
    console.log("[ProjectPanel] Video layer created after match:", layer.id);
  }

  // Close dialog and clear pending
  showFpsMismatchDialog.value = false;
  pendingFpsMismatch.value = null;
}

function handleFpsMismatchConform() {
  if (!pendingFpsMismatch.value) return;

  const result = pendingFpsMismatch.value;
  console.log(
    "[ProjectPanel] FPS mismatch: User chose CONFORM -",
    result.compositionFps,
    "fps",
  );

  // Complete import with conform (time-stretch video)
  const videoStore = useVideoStore();
  const layer = videoStore.completeVideoImportWithConform(
    result.pendingImport,
    result.fileName,
    result.compositionFps,
  );

  // Add to footage items
  footageItems.value.push({
    id: layer.id,
    name: result.fileName,
    type: "footage",
    width: projectStore.getWidth(),
    height: projectStore.getHeight(),
    duration: projectStore.getFrameCount(),
    fps: projectStore.getFps(),
  });
  console.log("[ProjectPanel] Video layer created after conform:", layer.id);

  // Close dialog and clear pending
  showFpsMismatchDialog.value = false;
  pendingFpsMismatch.value = null;
}

function handleFpsMismatchCancel() {
  if (!pendingFpsMismatch.value) return;

  console.log("[ProjectPanel] FPS mismatch: User cancelled");

  // Clean up the pending import
  const videoStore = useVideoStore();
  videoStore.cancelVideoImport(pendingFpsMismatch.value.pendingImport);

  // Close dialog and clear pending
  showFpsMismatchDialog.value = false;
  pendingFpsMismatch.value = null;
}

// ═══════════════════════════════════════════════════════════════════════════
// FPS SELECT HANDLERS (for unknown fps)
// ═══════════════════════════════════════════════════════════════════════════

async function handleFpsSelected(fps: number) {
  if (!pendingFpsUnknown.value) return;

  const pending = pendingFpsUnknown.value;
  console.log(
    "[ProjectPanel] FPS selected by user:",
    fps,
    "for",
    pending.fileName,
  );

  // Complete import with user-specified fps
  const videoStore = useVideoStore();
  const result = await videoStore.completeVideoImportWithUserFps(
    pending.pendingImport,
    pending.fileName,
    fps,
    true, // autoResizeComposition
  );

  // Close fps select dialog
  showFpsSelectDialog.value = false;
  pendingFpsUnknown.value = null;

  // Handle the result - may trigger fps_mismatch dialog
  if (result.status === "fps_mismatch") {
    // Chain to fps mismatch dialog
    pendingFpsMismatch.value = result;
    showFpsMismatchDialog.value = true;
    console.log(
      "[ProjectPanel] FPS mismatch after selection:",
      result.importedFps,
      "vs",
      result.compositionFps,
    );
    return;
  }

  if (result.status === "success") {
    // Add to footage items
    footageItems.value.push({
      id: result.layer.id,
      name: pending.fileName,
      type: "footage",
      width: projectStore.getWidth(),
      height: projectStore.getHeight(),
      duration: projectStore.getFrameCount(),
      fps: projectStore.getFps(),
    });
    console.log(
      "[ProjectPanel] Video layer created after fps selection:",
      result.layer.id,
    );
  }
}

function handleFpsSelectCancel() {
  if (!pendingFpsUnknown.value) return;

  console.log("[ProjectPanel] FPS select: User cancelled");

  // Clean up the pending import
  const videoStore = useVideoStore();
  videoStore.cancelVideoImport(pendingFpsUnknown.value.pendingImport);

  // Close dialog and clear pending
  showFpsSelectDialog.value = false;
  pendingFpsUnknown.value = null;
}

function getProjectStoreAccess(): ProjectStoreAccess {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    openCompositionIds: projectStore.openCompositionIds,
    compositionBreadcrumbs: projectStore.compositionBreadcrumbs,
    selectedAssetId: projectStore.selectedAssetId,
    comfyuiNodeId: projectStore.comfyuiNodeId,
    sourceImage: projectStore.sourceImage,
    depthMap: projectStore.depthMap,
    lastSaveProjectId: projectStore.lastSaveProjectId,
    lastSaveTime: projectStore.lastSaveTime,
    hasUnsavedChanges: projectStore.hasUnsavedChanges,
    getActiveComp: () => projectStore.getActiveComp(),
    getActiveCompLayers: () => projectStore.getActiveCompLayers(),
    pushHistory: () => projectStore.pushHistory(),
  };
}

function cleanupUnusedAssets() {
  showNewMenu.value = false;
  const result = projectStore.removeUnusedAssets(getProjectStoreAccess());
  if (result.removed > 0) {
    console.log(
      `[ProjectPanel] Removed ${result.removed} unused assets:`,
      result.assetNames,
    );
    // Could show a toast notification here
  } else {
    console.log("[ProjectPanel] No unused assets to remove");
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                               // svg // export // functions
// ═══════════════════════════════════════════════════════════════════════════

// System F/Omega EXCEPTION: Returning null here is valid - this is a query function
// Callers check for null and handle gracefully (console.warn) - this is not an error condition but a "no selection" state
function getSelectedSplineLayer() {
  const selectedLayerIds = selectionStore.selectedLayerIds;
  if (selectedLayerIds.length === 0) return null;

  const layers = projectStore.getActiveCompLayers();
  const layer = layers.find((l) => l.id === selectedLayerIds[0]);
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  return (layer != null && typeof layer === "object" && "type" in layer && layer.type === "spline") ? layer : null;
}

function exportSelectedLayerSVG() {
  const layer = getSelectedSplineLayer();
  if (!layer) {
    console.warn("[ProjectPanel] No spline layer selected");
    return;
  }

  try {
    const svg = exportSplineLayer(layer);
    // Copy to clipboard
    navigator.clipboard
      .writeText(svg)
      .then(() => {
        console.log("[ProjectPanel] SVG copied to clipboard");
      })
      .catch((err) => {
        console.error("[ProjectPanel] Failed to copy SVG:", err);
      });
  } catch (error) {
    console.error("[ProjectPanel] Failed to export SVG:", error);
  }
}

function exportCompositionSVG() {
  const comp = projectStore.getActiveComp();
  if (!comp) {
    console.warn("[ProjectPanel] No active composition");
    return;
  }

  try {
    const svg = exportLayers(comp.layers, {
      viewBox: {
        x: 0,
        y: 0,
        width: comp.settings.width,
        height: comp.settings.height,
      },
    });
    // Copy to clipboard
    navigator.clipboard
      .writeText(svg)
      .then(() => {
        console.log("[ProjectPanel] Composition SVG copied to clipboard");
      })
      .catch((err) => {
        console.error("[ProjectPanel] Failed to copy SVG:", err);
      });
  } catch (error) {
    console.error("[ProjectPanel] Failed to export composition SVG:", error);
  }
}

function downloadSVG(svgContent: string, filename: string) {
  const blob = new Blob([svgContent], { type: "image/svg+xml" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

function exportSelectedLayerSVGDownload() {
  const layer = getSelectedSplineLayer();
  if (!layer) {
    console.warn("[ProjectPanel] No spline layer selected");
    return;
  }

  try {
    const svg = exportSplineLayer(layer);
    const filename = `${layer.name.replace(/[^a-z0-9]/gi, "_")}.svg`;
    downloadSVG(svg, filename);
    console.log("[ProjectPanel] SVG downloaded:", filename);
  } catch (error) {
    console.error("[ProjectPanel] Failed to export SVG:", error);
  }
}

function exportCompositionSVGDownload() {
  const comp = projectStore.getActiveComp();
  if (!comp) {
    console.warn("[ProjectPanel] No active composition");
    return;
  }

  try {
    const svg = exportLayers(comp.layers, {
      viewBox: {
        x: 0,
        y: 0,
        width: comp.settings.width,
        height: comp.settings.height,
      },
    });
    const filename = `${comp.name.replace(/[^a-z0-9]/gi, "_")}.svg`;
    downloadSVG(svg, filename);
    console.log("[ProjectPanel] Composition SVG downloaded:", filename);
  } catch (error) {
    console.error("[ProjectPanel] Failed to export composition SVG:", error);
  }
}

function triggerFileImport() {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const fileInputRefVal = fileInputRef.value;
  if (fileInputRefVal != null && typeof fileInputRefVal === "object" && typeof fileInputRefVal.click === "function") {
    fileInputRefVal.click();
  }
}

async function handleFileImport(event: Event) {
  const input = event.target as HTMLInputElement;
  const files = input.files;
  if (!files || files.length === 0) return;

  for (const file of Array.from(files)) {
    // Check if it's a data file first
    if (isSupportedDataFile(file.name)) {
      const result = await importDataFromFile(file);
      if (result.success && result.asset) {
        // System F/Omega proof: File already validated by isSupportedDataFile, so getDataFileType will succeed
        // Type proof: file.name ∈ string → DataFileType
        // Mathematical proof: isSupportedDataFile ensures file type is supported
        const dataType = getDataFileType(file.name);
        let dataInfo = "";

        if (isCSVAsset(result.asset)) {
          dataInfo = `${result.asset.rows.length} rows, ${result.asset.numColumns} columns`;
        } else if (isJSONAsset(result.asset)) {
          const data = result.asset.sourceData;
          if (Array.isArray(data)) {
            dataInfo = `Array with ${data.length} items`;
          } else if (typeof data === "object" && data !== null) {
            dataInfo = `Object with ${Object.keys(data).length} properties`;
          }
        }

        // Store data asset in project for expression access via footage()
        if (!projectStore.project.dataAssets) {
          projectStore.project.dataAssets = {};
        }
        projectStore.project.dataAssets[result.asset.name] = {
          id: result.asset.id,
          name: result.asset.name,
          type: result.asset.type,
          rawContent: result.asset.rawContent,
          lastModified: result.asset.lastModified,
          sourceData: isJSONAsset(result.asset)
            ? result.asset.sourceData
            : undefined,
          headers: isCSVAsset(result.asset) ? result.asset.headers : undefined,
          rows: isCSVAsset(result.asset) ? result.asset.rows : undefined,
          numRows: isCSVAsset(result.asset) ? result.asset.numRows : undefined,
          numColumns: isCSVAsset(result.asset)
            ? result.asset.numColumns
            : undefined,
        };

        const newItem: ProjectItem = {
          id: result.asset.id,
          name: file.name,
          type: "data",
          dataType: dataType || undefined,
          dataInfo,
        };

        footageItems.value.push(newItem);
        console.log(
          "[ProjectPanel] Data file imported and stored in project:",
          file.name,
          dataType,
          dataInfo,
        );
      } else {
        console.error(
          "[ProjectPanel] Failed to import data file:",
          result.error,
        );
      }
      continue;
    }

    const type = getFileType(file);
    const newItem: ProjectItem = {
      id: `item-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`,
      name: file.name,
      type,
    };

    // Handle different file types
    if (type === "audio") {
      // Handle audio loading through store
      const activeComp = projectStore.getActiveComp();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const fps = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object" && "fps" in activeComp.settings && typeof activeComp.settings.fps === "number") ? activeComp.settings.fps : 16;
      await audioStore.loadAudio(file, fps);
    } else if (file.type.startsWith("video/")) {
      // Handle video import - creates video layer with auto-resize
      // May return fps_mismatch requiring user decision
      const result = await layerStore.createVideoLayer(file, true);

      if (result.status === "error") {
        console.error("[ProjectPanel] Failed to import video:", result.error);
        continue;
      }

      if (result.status === "fps_mismatch") {
        // Show fps mismatch dialog
        pendingFpsMismatch.value = result;
        showFpsMismatchDialog.value = true;
        console.log(
          "[ProjectPanel] FPS mismatch detected:",
          result.importedFps,
          "vs",
          result.compositionFps,
        );
        // Don't add to footage items yet - wait for user decision
        continue;
      }

      if (result.status === "fps_unknown") {
        // Show fps select dialog - user must specify video fps
        pendingFpsUnknown.value = result;
        showFpsSelectDialog.value = true;
        console.log(
          "[ProjectPanel] FPS unknown - user must specify:",
          result.fileName,
        );
        // Don't add to footage items yet - wait for user selection
        continue;
      }

      // Success - layer was created
      if (result.status === "success") {
        newItem.id = result.layer.id;
        newItem.width = projectStore.getWidth();
        newItem.height = projectStore.getHeight();
        newItem.duration = projectStore.getFrameCount();
        newItem.fps = projectStore.getFps();
        console.log(
          "[ProjectPanel] Video layer created:",
          result.layer.id,
          result.layer.name,
        );
      }
    } else if (file.type.startsWith("image/")) {
      // Handle image import - add to project assets only (no layer creation)
      // User double-clicks in project panel to add to timeline
      const imageUrl = URL.createObjectURL(file);
      const assetId = `image_${Date.now()}_${Math.random().toString(36).slice(2, 11)}`;

      // Load image to get dimensions
      const img = new Image();
      img.onload = () => {
        // Update asset with actual dimensions
        const asset = projectStore.project.assets[assetId];
        if (asset) {
          asset.width = img.naturalWidth;
          asset.height = img.naturalHeight;
          // Also update the project item
          const projItem = footageItems.value.find((i) => i.id === assetId);
          if (projItem) {
            projItem.width = img.naturalWidth;
            projItem.height = img.naturalHeight;
          }
          console.log(
            "[ProjectPanel] Image dimensions loaded:",
            img.naturalWidth,
            "x",
            img.naturalHeight,
          );
        }
      };
      img.src = imageUrl;

      // Add to assets (dimensions will be updated when image loads)
      projectStore.project.assets[assetId] = {
        id: assetId,
        type: "image",
        source: "file",
        width: 0, // Updated in onload
        height: 0,
        data: imageUrl,
      };

      // Use assetId as item ID so openItem() can find it
      newItem.id = assetId;
      console.log(
        "[ProjectPanel] Image added to project assets:",
        assetId,
        file.name,
      );
    }

    // Add to footage items (reactive ref)
    footageItems.value.push(newItem);
    console.log(
      "[ProjectPanel] Imported:",
      file.name,
      type,
      "total footage:",
      footageItems.value.length,
    );
  }

  // Reset input
  input.value = "";
}

function getFileType(file: File): ProjectItem["type"] {
  const mime = file.type;
  if (mime.startsWith("audio/")) return "audio";
  if (mime.startsWith("video/")) return "footage";
  if (mime.startsWith("image/")) return "footage";
  return "footage";
}

function getItemIcon(type: ProjectItem["type"]): string {
  const icons: Record<ProjectItem["type"], string> = {
    composition: "▶",
    footage: "▧",
    solid: "■",
    audio: "♪",
    folder: "▣",
    data: "⊟",
  };
  return icons[type] || "○";
}

function getItemInfo(item: ProjectItem): string {
  if (item.type === "composition" || item.type === "footage") {
    const parts: string[] = [];
    if (item.width && item.height) {
      parts.push(`${item.width}×${item.height}`);
    }
    if (item.fps) {
      parts.push(`${item.fps}fps`);
    }
    if (item.duration) {
      const seconds = item.duration / (item.fps || 30);
      parts.push(`${seconds.toFixed(1)}s`);
    }
    return parts.join(" • ");
  }
  if (item.type === "data") {
    // Show data type and info for data files
    const parts: string[] = [];
    if (item.dataType) {
      parts.push(item.dataType.toUpperCase());
    }
    if (item.dataInfo) {
      parts.push(item.dataInfo);
    }
    return parts.join(" • ");
  }
  return "";
}

function onDragStart(item: ProjectItem, event: DragEvent) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const dataTransfer = (event != null && typeof event === "object" && "dataTransfer" in event && event.dataTransfer != null && typeof event.dataTransfer === "object") ? event.dataTransfer : undefined;
  if (dataTransfer != null && typeof dataTransfer === "object" && typeof dataTransfer.setData === "function") {
    dataTransfer.setData("application/project-item", JSON.stringify(item));
  }
}
</script>

<style scoped>
.project-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #0f0f0f);
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 13px;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 10px;
  background: var(--lattice-surface-2, #161616);
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.panel-title {
  font-weight: 600;
  font-size: 13px;
  color: var(--lattice-text-primary, #E5E5E5);
}

.header-actions {
  display: flex;
  gap: 6px;
}

.header-actions button {
  width: 28px;
  height: 28px;
  padding: 0;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6B7280);
  border-radius: 4px;
  cursor: pointer;
  font-size: 16px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.header-actions button:hover {
  background: var(--lattice-surface-3, #1e1e1e);
  color: var(--lattice-text-primary, #e0e0e0);
}

.dropdown-container {
  position: relative;
}

.dropdown-menu {
  position: absolute;
  top: 100%;
  right: 0;
  background: var(--lattice-surface-2, #161616);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  border-radius: 6px;
  box-shadow: 0 4px 16px rgba(0, 0, 0, 0.5);
  z-index: 1000;
  min-width: 200px;
  white-space: nowrap;
  padding: 8px 0;
}

.dropdown-menu button {
  display: flex;
  align-items: center;
  justify-content: flex-start;
  gap: 12px;
  width: 100%;
  padding: 10px 16px;
  border: none;
  background: transparent;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 13px;
  text-align: left;
  cursor: pointer;
  line-height: 1.4;
}

.dropdown-menu button:hover {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
}

.menu-icon {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  width: 20px;
  font-size: 14px;
  flex-shrink: 0;
}

.menu-divider {
  border: none;
  border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);
  margin: 8px 12px;
}

.search-bar {
  padding: 6px 8px;
  background: var(--lattice-surface-2, #161616);
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.search-input {
  width: 100%;
  padding: 5px 8px;
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  background: var(--lattice-surface-0, #080808);
  color: var(--lattice-text-primary, #e0e0e0);
  border-radius: 4px;
  font-size: 13px;
}

.search-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

/* Asset Preview Area */
.preview-area {
  background: var(--lattice-surface-0, #080808);
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
  padding: 16px;
  display: flex;
  flex-direction: column;
  gap: 10px;
  align-items: center;
}

.preview-thumbnail {
  width: 100%;
  max-width: 200px;
  height: 150px;
  background: var(--lattice-void, #0a0a0a);
  border-radius: 6px;
  overflow: hidden;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
  border: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.preview-thumbnail img,
.preview-thumbnail video {
  width: 100%;
  height: 100%;
  object-fit: contain;
}

.preview-placeholder {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 100%;
  height: 100%;
}

.preview-icon {
  font-size: 24px;
  opacity: 0.6;
}

.preview-info {
  text-align: center;
  width: 100%;
}

.preview-name {
  font-size: 12px;
  font-weight: 500;
  color: var(--lattice-text-primary, #e0e0e0);
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.preview-details {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  margin-top: 4px;
}

.panel-content {
  flex: 1;
  overflow-y: auto;
}

.folder-tree {
  padding: 4px 0;
}

.folder-item {
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.folder-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
}

.folder-header:hover {
  background: var(--lattice-surface-2, #161616);
}

.folder-header.selected {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  border-left: 3px solid var(--lattice-accent, #8B5CF6);
}

.expand-icon {
  width: 12px;
  font-size: 11px;
  color: var(--lattice-text-secondary, #9CA3AF);
}

.folder-icon {
  font-size: 12px;
}

.folder-name {
  flex: 1;
  color: var(--lattice-text-primary, #E5E5E5);
  font-weight: 500;
}

.item-count {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
  background: var(--lattice-surface-3, #1e1e1e);
  padding: 1px 6px;
  border-radius: 8px;
}

.folder-contents {
  background: var(--lattice-surface-0, #080808);
}

.project-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px 8px 28px;
  cursor: pointer;
  user-select: none;
  border-radius: 4px;
  margin: 2px 4px;
}

.project-item:hover {
  background: var(--lattice-surface-2, #161616);
}

.project-item.selected {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.15));
  border-left: 3px solid var(--lattice-accent, #8B5CF6);
}

.item-icon {
  font-size: 12px;
  width: 18px;
  text-align: center;
}

.item-name {
  flex: 1;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  color: var(--lattice-text-primary, #E5E5E5);
}

.item-info {
  font-size: 11px;
  color: var(--lattice-text-muted, #6B7280);
}

.empty-state {
  padding: 24px;
  text-align: center;
  color: var(--lattice-text-muted, #6B7280);
}

.empty-state .hint {
  font-size: 12px;
  margin-top: 4px;
}

.panel-footer {
  padding: 8px 12px;
  background: var(--lattice-surface-2, #161616);
  border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.item-details {
  display: flex;
  justify-content: space-between;
  align-items: center;
}

.detail-label {
  font-weight: 500;
}

.detail-info {
  font-size: 12px;
  color: var(--lattice-text-muted, #6B7280);
}
</style>
