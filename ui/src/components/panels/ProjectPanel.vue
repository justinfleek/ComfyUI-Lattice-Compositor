<template>
  <div class="project-panel">
    <div class="panel-header">
      <span class="panel-title">Project</span>
      <div class="header-actions">
        <button @click="triggerFileImport" title="Import File (Ctrl+I)">📥</button>
        <div class="dropdown-container">
          <button @click="showNewMenu = !showNewMenu" title="New Item">+</button>
          <div v-if="showNewMenu" class="dropdown-menu">
            <button @click="createNewComposition"><span class="menu-icon">🎬</span> New Composition</button>
            <button @click="createNewFolder"><span class="menu-icon">📁</span> New Folder</button>
            <hr class="menu-divider" />
            <button @click="createNewSolid"><span class="menu-icon">⬜</span> New Solid</button>
            <button @click="createNewText"><span class="menu-icon">🔤</span> New Text</button>
            <button @click="createNewControl"><span class="menu-icon">⊕</span> New Control</button>
            <button @click="createNewSpline"><span class="menu-icon">✏️</span> New Spline</button>
            <button @click="createNewModel"><span class="menu-icon">🧊</span> New 3D Model</button>
            <button @click="createNewPointCloud"><span class="menu-icon">☁️</span> New Point Cloud</button>
            <hr class="menu-divider" />
            <button @click="openDecomposeDialog"><span class="menu-icon">✨</span> AI Layer Decompose</button>
            <button @click="openVectorizeDialog"><span class="menu-icon">✒️</span> Vectorize Image</button>
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

    <!-- Hidden file input -->
    <input
      ref="fileInputRef"
      type="file"
      multiple
      accept="image/*,video/*,audio/*,.json"
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
          :src="selectedPreview.url"
          :alt="selectedPreview.name"
        />
        <video
          v-else-if="selectedPreview.type === 'video'"
          :src="selectedPreview.url"
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
            <span class="folder-icon">📁</span>
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
import { ref, computed, type Ref } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { useSelectionStore } from '@/stores/selectionStore';
import DecomposeDialog from '@/components/dialogs/DecomposeDialog.vue';
import VectorizeDialog from '@/components/dialogs/VectorizeDialog.vue';
import type { DecomposedLayer } from '@/services/layerDecomposition';
import { exportSplineLayer, exportLayers } from '@/services/svgExport';

const emit = defineEmits<{
  (e: 'openCompositionSettings'): void;
}>();

interface ProjectItem {
  id: string;
  name: string;
  type: 'composition' | 'footage' | 'solid' | 'audio' | 'folder';
  width?: number;
  height?: number;
  duration?: number;
  fps?: number;
}

interface Folder {
  id: string;
  name: string;
  items: ProjectItem[];
}

const store = useCompositorStore();
const selectionStore = useSelectionStore();

// Refs
const fileInputRef = ref<HTMLInputElement | null>(null);

// State
const showSearch = ref(false);
const showNewMenu = ref(false);
const showDecomposeDialog = ref(false);
const showVectorizeDialog = ref(false);
const searchQuery = ref('');
const selectedItem = ref<string | null>(null);
const expandedFolders = ref<string[]>(['compositions', 'footage']);
const customFolders = ref<Folder[]>([]);

// Check if selected layer is a spline layer
const hasSelectedSplineLayer = computed(() => {
  const selectedLayerIds = selectionStore.selectedLayerIds;
  if (selectedLayerIds.length === 0) return false;

  const layers = store.getActiveCompLayers();
  const selectedLayer = layers.find(l => l.id === selectedLayerIds[0]);
  return selectedLayer?.type === 'spline';
});

// Reactive storage for footage and solids items (persists across re-renders)
const footageItems = ref<ProjectItem[]>([]);
const solidItems = ref<ProjectItem[]>([]);

// Folders computed from store - reactively updates when compositions change
const folders = computed<Folder[]>(() => {
  // Get all compositions from the store
  const compositions = Object.values(store.project.compositions || {}).map(comp => ({
    id: comp.id,
    name: comp.name,
    type: 'composition' as const,
    width: comp.settings.width,
    height: comp.settings.height,
    fps: comp.settings.fps,
    duration: comp.settings.frameCount
  }));

  const systemFolders: Folder[] = [
    {
      id: 'compositions',
      name: 'Compositions',
      items: compositions.length > 0 ? compositions : [{
        id: 'comp-main',
        name: store.activeComposition?.name || 'Main Comp',
        type: 'composition' as const,
        width: store.width,
        height: store.height,
        fps: store.fps,
        duration: store.frameCount
      }]
    },
    {
      id: 'footage',
      name: 'Footage',
      items: footageItems.value
    },
    {
      id: 'solids',
      name: 'Solids',
      items: solidItems.value
    }
  ];

  return [...systemFolders, ...customFolders.value];
});

const items = ref<ProjectItem[]>([]);

// Computed
const filteredFolders = computed(() => {
  if (!searchQuery.value) return folders.value;

  const query = searchQuery.value.toLowerCase();
  return folders.value.map(folder => ({
    ...folder,
    items: folder.items.filter(item =>
      item.name.toLowerCase().includes(query)
    )
  })).filter(folder => folder.items.length > 0 || folder.name.toLowerCase().includes(query));
});

const filteredRootItems = computed(() => {
  if (!searchQuery.value) return items.value;

  const query = searchQuery.value.toLowerCase();
  return items.value.filter(item =>
    item.name.toLowerCase().includes(query)
  );
});

// Preview data for the selected item
const selectedPreview = computed(() => {
  if (!selectedItem.value) return null;

  // Find the item
  let item: ProjectItem | null = null;
  for (const folder of folders.value) {
    const found = folder.items.find(i => i.id === selectedItem.value);
    if (found) {
      item = found;
      break;
    }
  }
  if (!item) {
    item = items.value.find(i => i.id === selectedItem.value) || null;
  }
  if (!item) return null;

  // Get asset data if available
  const asset = store.project.assets[item.id];

  if (item.type === 'footage' && asset) {
    if (asset.type === 'image') {
      return {
        type: 'image',
        url: asset.data as string,
        name: item.name,
        details: asset.width && asset.height ? `${asset.width} × ${asset.height}` : 'Image',
        icon: '🖼'
      };
    } else if (asset.type === 'video') {
      return {
        type: 'video',
        url: asset.data as string,
        name: item.name,
        details: `${item.width || '?'} × ${item.height || '?'} • ${item.fps || '?'}fps`,
        icon: '🎬'
      };
    }
  } else if (item.type === 'composition') {
    const comp = store.getComposition(item.id);
    return {
      type: 'composition',
      url: null,
      name: item.name,
      details: comp ? `${comp.settings.width} × ${comp.settings.height} • ${comp.settings.frameRate}fps` : 'Composition',
      icon: '🎬'
    };
  } else if (item.type === 'solid') {
    return {
      type: 'solid',
      url: null,
      name: item.name,
      details: 'Solid Layer',
      icon: '⬜'
    };
  } else if (item.type === 'audio') {
    return {
      type: 'audio',
      url: null,
      name: item.name,
      details: 'Audio File',
      icon: '🔊'
    };
  }

  return null;
});

const selectedItemDetails = computed(() => {
  if (!selectedItem.value) return null;

  // Find in folders
  for (const folder of folders.value) {
    const item = folder.items.find(i => i.id === selectedItem.value);
    if (item) {
      return {
        name: item.name,
        info: getItemInfo(item)
      };
    }
  }

  // Find in root items
  const item = items.value.find(i => i.id === selectedItem.value);
  if (item) {
    return {
      name: item.name,
      info: getItemInfo(item)
    };
  }

  return null;
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
  if (item.type === 'composition') {
    // Switch to composition (opens in timeline and viewer)
    store.switchComposition(item.id);
  } else if (item.type === 'folder') {
    // Toggle folder expansion
    toggleFolder(item.id);
  } else if (item.type === 'footage' || item.type === 'solid') {
    // Add footage/solid as a new layer at the current frame
    const asset = store.project.assets[item.id];
    if (asset) {
      const layerType = item.type === 'solid' ? 'solid' : 'image';
      const layer = store.createLayer(layerType, item.name);
      if (layer && asset.data) {
        // Link the asset to the layer AND provide the source URL
        store.updateLayerData(layer.id, {
          assetId: item.id,
          source: asset.data  // The actual image/video URL
        });
      }
      console.log('[ProjectPanel] Created layer from asset:', layer?.id, item.name);
    }
  } else if (item.type === 'audio') {
    // Load audio into the audio panel
    const asset = store.project.assets[item.id];
    if (asset && asset.data) {
      // Fetch the audio data and load it
      fetch(asset.data as string)
        .then(response => response.blob())
        .then(blob => {
          const file = new File([blob], item.name, { type: blob.type || 'audio/mpeg' });
          import('@/stores/audioStore').then(({ useAudioStore }) => {
            const audioStore = useAudioStore();
            const fps = store.activeComposition?.settings.frameRate || 16;
            audioStore.loadAudio(file, fps);
          });
        })
        .catch(err => console.error('[ProjectPanel] Failed to load audio:', err));
    }
  }
}

function createNewComposition() {
  showNewMenu.value = false;
  emit('openCompositionSettings');
}

function createNewFolder() {
  showNewMenu.value = false;
  const folderNumber = customFolders.value.length + 1;
  const newFolder: Folder = {
    id: `folder_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
    name: `Folder ${folderNumber}`,
    items: []
  };
  customFolders.value.push(newFolder);
  expandedFolders.value.push(newFolder.id);
  selectedItem.value = newFolder.id;
  console.log('[ProjectPanel] Created folder:', newFolder.name);
}

function createNewSolid() {
  showNewMenu.value = false;
  const layer = store.createLayer('solid', 'Solid');
  console.log('[ProjectPanel] Created solid layer:', layer.id);
}

function createNewText() {
  showNewMenu.value = false;
  const layer = store.createTextLayer('Text');
  console.log('[ProjectPanel] Created text layer:', layer.id);
}

function createNewControl() {
  showNewMenu.value = false;
  const layer = store.createLayer('control', 'Control');
  console.log('[ProjectPanel] Created control layer:', layer.id);
}

function createNewSpline() {
  showNewMenu.value = false;
  const layer = store.createSplineLayer();
  console.log('[ProjectPanel] Created spline layer:', layer.id);
}

function createNewModel() {
  showNewMenu.value = false;
  const layer = store.createLayer('model', '3D Model');
  console.log('[ProjectPanel] Created model layer:', layer.id);
}

function createNewPointCloud() {
  showNewMenu.value = false;
  const layer = store.createLayer('pointcloud', 'Point Cloud');
  console.log('[ProjectPanel] Created point cloud layer:', layer.id);
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
  console.log('[ProjectPanel] Image decomposed into', layers.length, 'layers');
}

function onVectorized(layerIds: string[]) {
  console.log('[ProjectPanel] Created', layerIds.length, 'vectorized layers');
}

// ============================================================
// SVG EXPORT FUNCTIONS
// ============================================================

function getSelectedSplineLayer() {
  const selectedLayerIds = selectionStore.selectedLayerIds;
  if (selectedLayerIds.length === 0) return null;

  const layers = store.getActiveCompLayers();
  const layer = layers.find(l => l.id === selectedLayerIds[0]);
  return layer?.type === 'spline' ? layer : null;
}

function exportSelectedLayerSVG() {
  const layer = getSelectedSplineLayer();
  if (!layer) {
    console.warn('[ProjectPanel] No spline layer selected');
    return;
  }

  try {
    const svg = exportSplineLayer(layer);
    // Copy to clipboard
    navigator.clipboard.writeText(svg).then(() => {
      console.log('[ProjectPanel] SVG copied to clipboard');
    }).catch(err => {
      console.error('[ProjectPanel] Failed to copy SVG:', err);
    });
  } catch (error) {
    console.error('[ProjectPanel] Failed to export SVG:', error);
  }
}

function exportCompositionSVG() {
  const comp = store.activeComposition;
  if (!comp) {
    console.warn('[ProjectPanel] No active composition');
    return;
  }

  try {
    const svg = exportLayers(comp.layers, {
      viewBox: { x: 0, y: 0, width: comp.settings.width, height: comp.settings.height }
    });
    // Copy to clipboard
    navigator.clipboard.writeText(svg).then(() => {
      console.log('[ProjectPanel] Composition SVG copied to clipboard');
    }).catch(err => {
      console.error('[ProjectPanel] Failed to copy SVG:', err);
    });
  } catch (error) {
    console.error('[ProjectPanel] Failed to export composition SVG:', error);
  }
}

function downloadSVG(svgContent: string, filename: string) {
  const blob = new Blob([svgContent], { type: 'image/svg+xml' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
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
    console.warn('[ProjectPanel] No spline layer selected');
    return;
  }

  try {
    const svg = exportSplineLayer(layer);
    const filename = `${layer.name.replace(/[^a-z0-9]/gi, '_')}.svg`;
    downloadSVG(svg, filename);
    console.log('[ProjectPanel] SVG downloaded:', filename);
  } catch (error) {
    console.error('[ProjectPanel] Failed to export SVG:', error);
  }
}

function exportCompositionSVGDownload() {
  const comp = store.activeComposition;
  if (!comp) {
    console.warn('[ProjectPanel] No active composition');
    return;
  }

  try {
    const svg = exportLayers(comp.layers, {
      viewBox: { x: 0, y: 0, width: comp.settings.width, height: comp.settings.height }
    });
    const filename = `${comp.name.replace(/[^a-z0-9]/gi, '_')}.svg`;
    downloadSVG(svg, filename);
    console.log('[ProjectPanel] Composition SVG downloaded:', filename);
  } catch (error) {
    console.error('[ProjectPanel] Failed to export composition SVG:', error);
  }
}

function triggerFileImport() {
  fileInputRef.value?.click();
}

async function handleFileImport(event: Event) {
  const input = event.target as HTMLInputElement;
  const files = input.files;
  if (!files || files.length === 0) return;

  for (const file of Array.from(files)) {
    const type = getFileType(file);
    const newItem: ProjectItem = {
      id: `item-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`,
      name: file.name,
      type,
    };

    // Handle different file types
    if (type === 'audio') {
      // Handle audio loading through store
      store.loadAudio(file);
    } else if (file.type.startsWith('video/')) {
      // Handle video import - creates video layer with auto-resize
      try {
        const layer = await store.createVideoLayer(file, true);
        newItem.id = layer.id;
        newItem.width = store.width;
        newItem.height = store.height;
        newItem.duration = store.frameCount;
        newItem.fps = store.fps;
        console.log('[ProjectPanel] Video layer created:', layer.id, layer.name);
      } catch (error) {
        console.error('[ProjectPanel] Failed to import video:', error);
        continue;
      }
    } else if (file.type.startsWith('image/')) {
      // Handle image import - add to project assets only (no layer creation)
      // User double-clicks in project panel to add to timeline
      const imageUrl = URL.createObjectURL(file);
      const assetId = `image_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

      // Add to assets
      store.project.assets[assetId] = {
        id: assetId,
        type: 'image',
        source: 'file',
        width: 0, // Will be updated when image loads
        height: 0,
        data: imageUrl
      };

      // Use assetId as item ID so openItem() can find it
      newItem.id = assetId;
      console.log('[ProjectPanel] Image added to project assets:', assetId, file.name);
    }

    // Add to footage items (reactive ref)
    footageItems.value.push(newItem);
    console.log('[ProjectPanel] Imported:', file.name, type, 'total footage:', footageItems.value.length);
  }

  // Reset input
  input.value = '';
}

function getFileType(file: File): ProjectItem['type'] {
  const mime = file.type;
  if (mime.startsWith('audio/')) return 'audio';
  if (mime.startsWith('video/')) return 'footage';
  if (mime.startsWith('image/')) return 'footage';
  return 'footage';
}

function getItemIcon(type: ProjectItem['type']): string {
  const icons: Record<ProjectItem['type'], string> = {
    composition: '🎬',
    footage: '🎞',
    solid: '⬜',
    audio: '🔊',
    folder: '📁'
  };
  return icons[type] || '📄';
}

function getItemInfo(item: ProjectItem): string {
  if (item.type === 'composition' || item.type === 'footage') {
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
    return parts.join(' • ');
  }
  return '';
}

function onDragStart(item: ProjectItem, event: DragEvent) {
  event.dataTransfer?.setData('application/project-item', JSON.stringify(item));
}
</script>

<style scoped>
.project-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 13px;
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 10px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-title {
  font-weight: 600;
  font-size: 12px;
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
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  font-size: 16px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.header-actions button:hover {
  background: #3a3a3a;
  color: #e0e0e0;
}

.dropdown-container {
  position: relative;
}

.dropdown-menu {
  position: absolute;
  top: 100%;
  right: 0;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 6px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
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
  color: #e0e0e0;
  font-size: 13px;
  text-align: left;
  cursor: pointer;
  line-height: 1.4;
}

.dropdown-menu button:hover {
  background: #3a5070;
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
  border-top: 1px solid #444;
  margin: 8px 12px;
}

.search-bar {
  padding: 6px 8px;
  background: #222;
  border-bottom: 1px solid #333;
}

.search-input {
  width: 100%;
  padding: 5px 8px;
  border: 1px solid #3a3a3a;
  background: #1a1a1a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}

.search-input:focus {
  outline: none;
  border-color: #4a90d9;
}

/* Asset Preview Area */
.preview-area {
  background: #1a1a1a;
  border-bottom: 1px solid #333;
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
  background: #0a0a0a;
  border-radius: 4px;
  overflow: hidden;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
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
  color: #e0e0e0;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.preview-details {
  font-size: 11px;
  color: #888;
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
  border-bottom: 1px solid #2a2a2a;
}

.folder-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  cursor: pointer;
  user-select: none;
}

.folder-header:hover {
  background: #2a2a2a;
}

.folder-header.selected {
  background: #3a5070;
}

.expand-icon {
  width: 12px;
  font-size: 11px;
  color: #666;
}

.folder-icon {
  font-size: 12px;
}

.folder-name {
  flex: 1;
}

.item-count {
  font-size: 11px;
  color: #666;
  background: #333;
  padding: 1px 5px;
  border-radius: 8px;
}

.folder-contents {
  background: #1a1a1a;
}

.project-item {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 5px 8px 5px 24px;
  cursor: pointer;
  user-select: none;
}

.project-item:hover {
  background: #2a2a2a;
}

.project-item.selected {
  background: #3a5070;
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
}

.item-info {
  font-size: 11px;
  color: #666;
}

.empty-state {
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-state .hint {
  font-size: 12px;
  margin-top: 4px;
}

.panel-footer {
  padding: 6px 10px;
  background: #222;
  border-top: 1px solid #333;
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
  color: #888;
}
</style>
