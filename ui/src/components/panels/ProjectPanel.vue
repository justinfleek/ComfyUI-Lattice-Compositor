<template>
  <div class="project-panel">
    <div class="panel-header">
      <span class="panel-title">Project</span>
      <div class="header-actions">
        <button @click="triggerFileImport" title="Import File (Ctrl+I)">📥</button>
        <div class="dropdown-container">
          <button @click="showNewMenu = !showNewMenu" title="New Item">+</button>
          <div v-if="showNewMenu" class="dropdown-menu">
            <button @click="createNewComposition">🎬 New Composition</button>
            <button @click="createNewSolid">⬜ New Solid</button>
            <button @click="createNewText">T New Text</button>
            <button @click="createNewNull">◇ New Null</button>
            <button @click="createNewSpline">✏ New Spline</button>
          </div>
        </div>
        <button @click="showSearch = !showSearch" title="Search">🔍</button>
      </div>
    </div>

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
import { ref, computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';

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

// Refs
const fileInputRef = ref<HTMLInputElement | null>(null);

// State
const showSearch = ref(false);
const showNewMenu = ref(false);
const searchQuery = ref('');
const selectedItem = ref<string | null>(null);
const expandedFolders = ref<string[]>(['compositions', 'footage']);

// Demo data - in real app this would come from store
const folders = ref<Folder[]>([
  {
    id: 'compositions',
    name: 'Compositions',
    items: [
      { id: 'comp-1', name: 'Main Comp', type: 'composition', width: 1920, height: 1080, fps: 30, duration: 300 }
    ]
  },
  {
    id: 'footage',
    name: 'Footage',
    items: []
  },
  {
    id: 'solids',
    name: 'Solids',
    items: []
  }
]);

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
    // Open composition in viewer
    console.log('Opening composition:', item.name);
  }
}

function createNewComposition() {
  showNewMenu.value = false;
  // TODO: Show composition settings dialog
  console.log('Create new composition');
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

function createNewNull() {
  showNewMenu.value = false;
  const layer = store.createLayer('null', 'Null');
  console.log('[ProjectPanel] Created null layer:', layer.id);
}

function createNewSpline() {
  showNewMenu.value = false;
  const layer = store.createSplineLayer();
  console.log('[ProjectPanel] Created spline layer:', layer.id);
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
      // Handle image import - create image layer
      const imageUrl = URL.createObjectURL(file);
      const assetId = `image_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;

      // Add to assets (use type assertion since width/height will be set asynchronously)
      store.project.assets[assetId] = {
        id: assetId,
        type: 'image',
        source: 'file',
        width: 0, // Will be updated when image loads
        height: 0,
        data: imageUrl
      };

      // Create image layer
      const layer = store.createLayer('image', file.name.replace(/\.[^.]+$/, ''));
      (layer.data as any) = { assetId };
      newItem.id = layer.id;
    }

    // Add to footage folder
    const folder = folders.value.find(f => f.id === 'footage');
    if (folder) {
      folder.items.push(newItem);
    } else {
      items.value.push(newItem);
    }

    console.log('[ProjectPanel] Imported:', file.name, type);
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
  font-size: 11px;
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
  gap: 4px;
}

.header-actions button {
  width: 22px;
  height: 22px;
  padding: 0;
  border: none;
  background: transparent;
  color: #888;
  border-radius: 3px;
  cursor: pointer;
  font-size: 12px;
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
  left: 0;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  z-index: 100;
  min-width: 140px;
}

.dropdown-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: #e0e0e0;
  font-size: 11px;
  text-align: left;
  cursor: pointer;
}

.dropdown-menu button:hover {
  background: #3a5070;
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
  font-size: 11px;
}

.search-input:focus {
  outline: none;
  border-color: #4a90d9;
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
  font-size: 8px;
  color: #666;
}

.folder-icon {
  font-size: 12px;
}

.folder-name {
  flex: 1;
}

.item-count {
  font-size: 9px;
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
  font-size: 9px;
  color: #666;
}

.empty-state {
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-state .hint {
  font-size: 10px;
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
  font-size: 10px;
  color: #888;
}
</style>
