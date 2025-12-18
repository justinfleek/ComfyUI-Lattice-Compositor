<template>
  <div class="assets-panel">
    <!-- Sub-tabs for different asset types -->
    <div class="asset-tabs">
      <button
        v-for="tab in tabs"
        :key="tab.id"
        :class="{ active: activeTab === tab.id }"
        @click="activeTab = tab.id"
        :title="tab.tooltip"
      >
        <span class="tab-icon">{{ tab.icon }}</span>
        <span class="tab-label">{{ tab.label }}</span>
      </button>
    </div>

    <!-- Tab Content -->
    <div class="asset-content">
      <!-- Materials Tab -->
      <div v-if="activeTab === 'materials'" class="tab-panel">
        <div class="panel-toolbar">
          <button @click="createMaterial" title="New Material">
            <span class="icon">+</span> New
          </button>
          <select v-model="selectedPreset" @change="createFromPreset" class="preset-select">
            <option value="">From Preset...</option>
            <option v-for="preset in materialPresets" :key="preset" :value="preset">
              {{ preset }}
            </option>
          </select>
        </div>

        <div class="material-list">
          <div
            v-for="mat in materials"
            :key="mat.id"
            :class="['material-item', { selected: mat.id === assetStore.selectedMaterialId }]"
            @click="selectMaterial(mat.id)"
          >
            <div class="material-preview" :style="getMaterialPreviewStyle(mat)"></div>
            <span class="material-name">{{ mat.name }}</span>
            <button class="delete-btn" @click.stop="deleteMaterial(mat.id)" title="Delete">
              <span class="icon">×</span>
            </button>
          </div>
        </div>

        <!-- Material Editor (inline) -->
        <MaterialEditor
          v-if="selectedMaterial"
          :material-id="selectedMaterial.id"
          :config="selectedMaterial.config"
          @update="onMaterialUpdate"
          @texture-upload="onTextureUpload"
        />
      </div>

      <!-- SVG/Logos Tab -->
      <div v-if="activeTab === 'svg'" class="tab-panel">
        <div class="panel-toolbar">
          <AssetUploader
            accept=".svg"
            :asset-type="'svg'"
            @upload="onSvgUpload"
            button-text="Import SVG"
          />
        </div>

        <div class="svg-list">
          <div
            v-for="svg in svgDocuments"
            :key="svg.id"
            :class="['svg-item', { selected: svg.id === assetStore.selectedSvgId }]"
            @click="selectSvg(svg.id)"
          >
            <div class="svg-preview">
              <span class="path-count">{{ svg.document.paths.length }} paths</span>
            </div>
            <span class="svg-name">{{ svg.name }}</span>
            <div class="svg-actions">
              <button @click.stop="createLayersFromSvg(svg.id)" title="Create Layers">
                <span class="icon">↗</span>
              </button>
              <button @click.stop="registerSvgAsMesh(svg.id)" title="Use as Particle">
                <span class="icon">✦</span>
              </button>
              <button class="delete-btn" @click.stop="deleteSvg(svg.id)" title="Delete">
                <span class="icon">×</span>
              </button>
            </div>
          </div>
        </div>

        <!-- SVG Path Details -->
        <div v-if="selectedSvg" class="svg-details">
          <h4>{{ selectedSvg.name }}</h4>
          <div class="path-list">
            <div
              v-for="(path, i) in selectedSvg.document.paths"
              :key="path.id"
              class="path-item"
            >
              <span class="path-name">{{ path.id }}</span>
              <div
                class="path-color"
                :style="{ backgroundColor: path.fill || path.stroke || '#888' }"
              ></div>
              <div class="path-config">
                <label>
                  Depth
                  <input
                    type="number"
                    :value="selectedSvg.layerConfigs[i]?.depth || 0"
                    @input="updatePathDepth(i, $event)"
                    step="1"
                  />
                </label>
                <label>
                  Extrusion
                  <input
                    type="number"
                    :value="selectedSvg.layerConfigs[i]?.extrusionDepth || 2"
                    @input="updatePathExtrusion(i, $event)"
                    step="0.5"
                  />
                </label>
              </div>
            </div>
          </div>
        </div>
      </div>

      <!-- Mesh Particles Tab -->
      <div v-if="activeTab === 'meshes'" class="tab-panel">
        <div class="panel-toolbar">
          <select v-model="selectedPrimitive" @change="addPrimitiveMesh" class="primitive-select">
            <option value="">Add Primitive...</option>
            <option value="cube">Cube</option>
            <option value="sphere">Sphere</option>
            <option value="cone">Cone</option>
            <option value="cylinder">Cylinder</option>
            <option value="torus">Torus</option>
            <option value="tetrahedron">Tetrahedron</option>
            <option value="octahedron">Octahedron</option>
            <option value="icosahedron">Icosahedron</option>
          </select>
        </div>

        <div class="mesh-list">
          <div
            v-for="mesh in meshParticles"
            :key="mesh.id"
            :class="['mesh-item', { selected: mesh.id === assetStore.selectedMeshParticleId }]"
            @click="selectMesh(mesh.id)"
          >
            <div class="mesh-icon">
              <span v-if="mesh.source === 'primitive'">◇</span>
              <span v-else-if="mesh.source === 'svg'">◈</span>
              <span v-else>◆</span>
            </div>
            <div class="mesh-info">
              <span class="mesh-name">{{ mesh.name }}</span>
              <span class="mesh-verts">{{ mesh.registration.vertexCount }} verts</span>
            </div>
            <button class="delete-btn" @click.stop="deleteMesh(mesh.id)" title="Delete">
              <span class="icon">×</span>
            </button>
          </div>
        </div>

        <div v-if="selectedMesh" class="mesh-details">
          <h4>{{ selectedMesh.name }}</h4>
          <div class="detail-row">
            <span class="label">Source:</span>
            <span class="value">{{ selectedMesh.source }}</span>
          </div>
          <div class="detail-row">
            <span class="label">Vertices:</span>
            <span class="value">{{ selectedMesh.registration.vertexCount }}</span>
          </div>
          <div class="detail-row">
            <span class="label">Bounding Radius:</span>
            <span class="value">{{ selectedMesh.registration.boundingSphere.radius.toFixed(2) }}</span>
          </div>
          <button class="action-btn" @click="useAsEmitterShape">
            Use as Emitter Shape
          </button>
        </div>
      </div>

      <!-- Sprite Sheets Tab -->
      <div v-if="activeTab === 'sprites'" class="tab-panel">
        <div class="panel-toolbar">
          <button @click="showSpriteImport = true" title="Import Sprite Sheet">
            <span class="icon">+</span> Import
          </button>
        </div>

        <div class="sprite-list">
          <div
            v-for="sprite in spriteSheets"
            :key="sprite.id"
            :class="['sprite-item', { selected: sprite.id === assetStore.selectedSpriteSheetId }]"
            @click="selectSprite(sprite.id)"
          >
            <img :src="sprite.textureUrl" class="sprite-preview" />
            <div class="sprite-info">
              <span class="sprite-name">{{ sprite.name }}</span>
              <span class="sprite-frames">{{ sprite.config.totalFrames }} frames</span>
            </div>
            <button class="delete-btn" @click.stop="deleteSprite(sprite.id)" title="Delete">
              <span class="icon">×</span>
            </button>
          </div>
        </div>

        <!-- Sprite Import Dialog -->
        <div v-if="showSpriteImport" class="sprite-import-dialog">
          <h4>Import Sprite Sheet</h4>
          <AssetUploader
            accept="image/*"
            asset-type="sprite"
            @upload="onSpriteFileSelect"
            button-text="Select Image"
          />
          <div v-if="pendingSpriteFile" class="sprite-config">
            <label>
              Columns
              <input v-model.number="spriteColumns" type="number" min="1" />
            </label>
            <label>
              Rows
              <input v-model.number="spriteRows" type="number" min="1" />
            </label>
            <label>
              Frame Rate
              <input v-model.number="spriteFrameRate" type="number" min="1" />
            </label>
            <div class="dialog-actions">
              <button @click="importSpriteSheet" class="confirm-btn">Import</button>
              <button @click="cancelSpriteImport" class="cancel-btn">Cancel</button>
            </div>
          </div>
        </div>
      </div>

      <!-- Environment Tab -->
      <div v-if="activeTab === 'environment'" class="tab-panel">
        <EnvironmentSettings
          :config="environment"
          @update="onEnvironmentUpdate"
          @load="onEnvironmentLoad"
          @clear="onEnvironmentClear"
        />
      </div>
    </div>

    <!-- Loading Overlay -->
    <div v-if="assetStore.isLoading" class="loading-overlay">
      <div class="spinner"></div>
      <span>Loading...</span>
    </div>

    <!-- Error Toast -->
    <div v-if="assetStore.lastError" class="error-toast" @click="assetStore.clearError">
      {{ assetStore.lastError }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, watch } from 'vue';
import { useAssetStore } from '@/stores/assetStore';
import { useCompositorStore } from '@/stores/compositorStore';
import MaterialEditor from '@/components/materials/MaterialEditor.vue';
import AssetUploader from '@/components/materials/AssetUploader.vue';
import EnvironmentSettings from '@/components/materials/EnvironmentSettings.vue';
import type { PBRMaterialConfig } from '@/services/materialSystem';

const assetStore = useAssetStore();
const compositorStore = useCompositorStore();

// Tab configuration
const tabs = [
  { id: 'materials', label: 'Materials', icon: '◉', tooltip: 'PBR Materials' },
  { id: 'svg', label: 'SVG', icon: '✎', tooltip: 'SVG Logos & Shapes' },
  { id: 'meshes', label: 'Meshes', icon: '◇', tooltip: 'Mesh Particles' },
  { id: 'sprites', label: 'Sprites', icon: '▦', tooltip: 'Sprite Sheets' },
  { id: 'environment', label: 'Env', icon: '☀', tooltip: 'Environment Map' },
];

const activeTab = ref('materials');

// Material presets
const materialPresets = [
  'chrome', 'gold', 'silver', 'copper', 'brass',
  'glass', 'plastic', 'rubber', 'wood', 'concrete',
  'emissive', 'holographic',
];
const selectedPreset = ref('');

// Computed lists
const materials = computed(() => assetStore.materialList);
const svgDocuments = computed(() => assetStore.svgDocumentList);
const meshParticles = computed(() => assetStore.meshParticleList);
const spriteSheets = computed(() => assetStore.spriteSheetList);
const environment = computed(() => assetStore.environment);

// Selected items
const selectedMaterial = computed(() => assetStore.selectedMaterial);
const selectedSvg = computed(() => assetStore.selectedSvgDocument);
const selectedMesh = computed(() => assetStore.selectedMeshParticle);

// Primitive selection
const selectedPrimitive = ref('');

// Sprite import state
const showSpriteImport = ref(false);
const pendingSpriteFile = ref<File | null>(null);
const spriteColumns = ref(4);
const spriteRows = ref(4);
const spriteFrameRate = ref(24);

// ========================================================================
// MATERIALS
// ========================================================================

function createMaterial() {
  assetStore.createEmptyMaterial('New Material');
}

function createFromPreset() {
  if (selectedPreset.value) {
    assetStore.createMaterialFromPreset(selectedPreset.value);
    selectedPreset.value = '';
  }
}

function selectMaterial(id: string) {
  assetStore.selectedMaterialId = id;
}

function deleteMaterial(id: string) {
  assetStore.deleteMaterial(id);
}

function onMaterialUpdate(updates: Partial<PBRMaterialConfig>) {
  if (assetStore.selectedMaterialId) {
    assetStore.updateMaterial(assetStore.selectedMaterialId, updates);
  }
}

function onTextureUpload(textureType: string, file: File) {
  if (assetStore.selectedMaterialId) {
    assetStore.setMaterialTexture(assetStore.selectedMaterialId, textureType as keyof PBRMaterialConfig, file);
  }
}

function getMaterialPreviewStyle(mat: typeof materials.value[0]) {
  return {
    backgroundColor: mat.config.color || '#808080',
    backgroundImage: mat.config.albedoMap ? `url(${mat.config.albedoMap})` : 'none',
    backgroundSize: 'cover',
  };
}

// ========================================================================
// SVG
// ========================================================================

async function onSvgUpload(file: File) {
  await assetStore.importSvgFromFile(file);
}

function selectSvg(id: string) {
  assetStore.selectedSvgId = id;
}

function deleteSvg(id: string) {
  assetStore.deleteSvgDocument(id);
}

function updatePathDepth(pathIndex: number, event: Event) {
  if (!assetStore.selectedSvgId) return;
  const value = parseFloat((event.target as HTMLInputElement).value) || 0;
  assetStore.updateSvgLayerConfig(assetStore.selectedSvgId, pathIndex, { depth: value });
}

function updatePathExtrusion(pathIndex: number, event: Event) {
  if (!assetStore.selectedSvgId) return;
  const value = parseFloat((event.target as HTMLInputElement).value) || 2;
  assetStore.updateSvgLayerConfig(assetStore.selectedSvgId, pathIndex, { extrusionDepth: value });
}

function createLayersFromSvg(svgId: string) {
  // Emit event for parent to handle layer creation
  emit('create-layers-from-svg', svgId);
}

function registerSvgAsMesh(svgId: string) {
  const svg = assetStore.svgDocuments.get(svgId);
  if (!svg) return;

  // Register each path as a mesh particle
  svg.document.paths.forEach((_, i) => {
    assetStore.registerSvgPathAsMesh(svgId, i);
  });

  // Switch to meshes tab
  activeTab.value = 'meshes';
}

// ========================================================================
// MESH PARTICLES
// ========================================================================

function addPrimitiveMesh() {
  if (selectedPrimitive.value) {
    assetStore.registerPrimitiveMesh(selectedPrimitive.value as any);
    selectedPrimitive.value = '';
  }
}

function selectMesh(id: string) {
  assetStore.selectedMeshParticleId = id;
}

function deleteMesh(id: string) {
  assetStore.deleteMeshParticle(id);
}

function useAsEmitterShape() {
  if (assetStore.selectedMeshParticleId) {
    emit('use-mesh-as-emitter', assetStore.selectedMeshParticleId);
  }
}

// ========================================================================
// SPRITE SHEETS
// ========================================================================

function onSpriteFileSelect(file: File) {
  pendingSpriteFile.value = file;
}

async function importSpriteSheet() {
  if (!pendingSpriteFile.value) return;

  await assetStore.importSpriteSheet(
    pendingSpriteFile.value,
    spriteColumns.value,
    spriteRows.value,
    { frameRate: spriteFrameRate.value }
  );

  cancelSpriteImport();
}

function cancelSpriteImport() {
  showSpriteImport.value = false;
  pendingSpriteFile.value = null;
  spriteColumns.value = 4;
  spriteRows.value = 4;
  spriteFrameRate.value = 24;
}

function selectSprite(id: string) {
  assetStore.selectedSpriteSheetId = id;
}

function deleteSprite(id: string) {
  assetStore.deleteSpriteSheet(id);
}

// ========================================================================
// ENVIRONMENT
// ========================================================================

function onEnvironmentUpdate(settings: any) {
  assetStore.updateEnvironment(settings);
  emit('environment-update', settings);
}

async function onEnvironmentLoad(file: File) {
  await assetStore.loadEnvironment(file);
  emit('environment-load', assetStore.environment);
}

function onEnvironmentClear() {
  assetStore.clearEnvironment();
  emit('environment-clear');
}

// ========================================================================
// EVENTS
// ========================================================================

const emit = defineEmits<{
  (e: 'create-layers-from-svg', svgId: string): void;
  (e: 'use-mesh-as-emitter', meshId: string): void;
  (e: 'environment-update', settings: any): void;
  (e: 'environment-load', settings: any): void;
  (e: 'environment-clear'): void;
}>();
</script>

<style scoped>
.assets-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 13px;
  position: relative;
}

/* Tabs */
.asset-tabs {
  display: flex;
  background: #252525;
  border-bottom: 1px solid #333;
  overflow-x: auto;
}

.asset-tabs button {
  flex: 1;
  min-width: 50px;
  padding: 6px 4px;
  border: none;
  background: transparent;
  color: #888;
  cursor: pointer;
  border-bottom: 2px solid transparent;
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: 2px;
  font-size: 12px;
}

.asset-tabs button:hover {
  color: #e0e0e0;
  background: #2a2a2a;
}

.asset-tabs button.active {
  color: #4a90d9;
  border-bottom-color: #4a90d9;
}

.tab-icon {
  font-size: 14px;
}

.tab-label {
  font-size: 11px;
}

/* Content */
.asset-content {
  flex: 1;
  overflow: hidden;
}

.tab-panel {
  height: 100%;
  display: flex;
  flex-direction: column;
  overflow: hidden;
}

/* Toolbar */
.panel-toolbar {
  display: flex;
  gap: 4px;
  padding: 6px;
  background: #252525;
  border-bottom: 1px solid #333;
}

.panel-toolbar button {
  padding: 4px 8px;
  background: #3a3a3a;
  border: none;
  color: #e0e0e0;
  border-radius: 3px;
  cursor: pointer;
  font-size: 12px;
}

.panel-toolbar button:hover {
  background: #4a90d9;
}

.preset-select,
.primitive-select {
  flex: 1;
  padding: 4px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
}

/* Lists */
.material-list,
.svg-list,
.mesh-list,
.sprite-list {
  flex: 1;
  overflow-y: auto;
  padding: 4px;
}

.material-item,
.svg-item,
.mesh-item,
.sprite-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px;
  background: #2a2a2a;
  border-radius: 4px;
  margin-bottom: 4px;
  cursor: pointer;
}

.material-item:hover,
.svg-item:hover,
.mesh-item:hover,
.sprite-item:hover {
  background: #333;
}

.material-item.selected,
.svg-item.selected,
.mesh-item.selected,
.sprite-item.selected {
  background: #3a4a5a;
  border: 1px solid #4a90d9;
}

.material-preview {
  width: 32px;
  height: 32px;
  border-radius: 4px;
  border: 1px solid #444;
}

.material-name,
.svg-name,
.mesh-name,
.sprite-name {
  flex: 1;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}

.delete-btn {
  padding: 2px 6px;
  background: transparent;
  border: none;
  color: #666;
  cursor: pointer;
  border-radius: 3px;
}

.delete-btn:hover {
  background: #ff4444;
  color: white;
}

/* SVG specific */
.svg-preview {
  width: 40px;
  height: 40px;
  background: #1a1a1a;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.path-count {
  font-size: 11px;
  color: #888;
}

.svg-actions {
  display: flex;
  gap: 2px;
}

.svg-actions button {
  padding: 2px 6px;
  background: #3a3a3a;
  border: none;
  color: #aaa;
  cursor: pointer;
  border-radius: 3px;
  font-size: 12px;
}

.svg-actions button:hover {
  background: #4a90d9;
  color: white;
}

/* SVG Details */
.svg-details,
.mesh-details {
  padding: 8px;
  background: #252525;
  border-top: 1px solid #333;
}

.svg-details h4,
.mesh-details h4 {
  margin: 0 0 8px;
  font-size: 13px;
  color: #aaa;
}

.path-list {
  max-height: 200px;
  overflow-y: auto;
}

.path-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 4px;
  background: #2a2a2a;
  border-radius: 3px;
  margin-bottom: 4px;
}

.path-name {
  flex: 1;
  font-size: 12px;
  color: #888;
}

.path-color {
  width: 16px;
  height: 16px;
  border-radius: 2px;
  border: 1px solid #444;
}

.path-config {
  display: flex;
  gap: 8px;
}

.path-config label {
  display: flex;
  flex-direction: column;
  font-size: 11px;
  color: #666;
}

.path-config input {
  width: 50px;
  padding: 2px 4px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #e0e0e0;
  border-radius: 2px;
  font-size: 12px;
}

/* Mesh specific */
.mesh-icon {
  width: 32px;
  height: 32px;
  background: #1a1a1a;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 18px;
  color: #4a90d9;
}

.mesh-info {
  flex: 1;
  display: flex;
  flex-direction: column;
}

.mesh-verts {
  font-size: 11px;
  color: #666;
}

.detail-row {
  display: flex;
  justify-content: space-between;
  padding: 4px 0;
  border-bottom: 1px solid #333;
}

.detail-row .label {
  color: #888;
}

.detail-row .value {
  color: #e0e0e0;
}

.action-btn {
  width: 100%;
  margin-top: 8px;
  padding: 8px;
  background: #4a90d9;
  border: none;
  color: white;
  border-radius: 4px;
  cursor: pointer;
}

.action-btn:hover {
  background: #5aa0e9;
}

/* Sprite specific */
.sprite-preview {
  width: 48px;
  height: 48px;
  object-fit: contain;
  background: #1a1a1a;
  border-radius: 4px;
}

.sprite-info {
  flex: 1;
  display: flex;
  flex-direction: column;
}

.sprite-frames {
  font-size: 11px;
  color: #666;
}

/* Sprite Import Dialog */
.sprite-import-dialog {
  padding: 12px;
  background: #252525;
  border-top: 1px solid #333;
}

.sprite-import-dialog h4 {
  margin: 0 0 12px;
  font-size: 12px;
}

.sprite-config {
  margin-top: 12px;
}

.sprite-config label {
  display: block;
  margin-bottom: 8px;
}

.sprite-config input {
  display: block;
  width: 100%;
  margin-top: 4px;
  padding: 6px;
  background: #1a1a1a;
  border: 1px solid #333;
  color: #e0e0e0;
  border-radius: 3px;
}

.dialog-actions {
  display: flex;
  gap: 8px;
  margin-top: 12px;
}

.confirm-btn {
  flex: 1;
  padding: 8px;
  background: #4a90d9;
  border: none;
  color: white;
  border-radius: 4px;
  cursor: pointer;
}

.cancel-btn {
  flex: 1;
  padding: 8px;
  background: #3a3a3a;
  border: none;
  color: #e0e0e0;
  border-radius: 4px;
  cursor: pointer;
}

/* Loading Overlay */
.loading-overlay {
  position: absolute;
  inset: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  gap: 12px;
  z-index: 100;
}

.spinner {
  width: 32px;
  height: 32px;
  border: 3px solid #333;
  border-top-color: #4a90d9;
  border-radius: 50%;
  animation: spin 1s linear infinite;
}

@keyframes spin {
  to { transform: rotate(360deg); }
}

/* Error Toast */
.error-toast {
  position: absolute;
  bottom: 12px;
  left: 12px;
  right: 12px;
  padding: 12px;
  background: #c62828;
  color: white;
  border-radius: 4px;
  cursor: pointer;
  z-index: 101;
}
</style>
