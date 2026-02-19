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
                    :value="getLayerDepth(i)"
                    @input="updatePathDepth(i, $event)"
                    step="1"
                  />
                </label>
                <label>
                  Extrusion
                  <input
                    type="number"
                    :value="getLayerExtrusionDepth(i)"
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
          <h4>Import Sprite / Sprite Sheet</h4>

          <!-- Import Mode Toggle -->
          <div class="import-mode-toggle">
            <button
              :class="{ active: spriteImportMode === 'sprite' }"
              @click="spriteImportMode = 'sprite'"
            >
              Single Sprite
            </button>
            <button
              :class="{ active: spriteImportMode === 'spritesheet' }"
              @click="spriteImportMode = 'spritesheet'"
            >
              Sprite Sheet
            </button>
          </div>

          <AssetUploader
            accept="image/*"
            :asset-type="spriteImportMode"
            @upload="onSpriteFileSelect"
            button-text="Select Image"
          />

          <div v-if="pendingSpriteFile" class="sprite-config">
            <!-- Image Preview -->
            <div class="sprite-preview-container">
              <img v-if="spritePreview" :src="spritePreview" class="sprite-preview-image" />
              <div v-if="spriteImageDimensions" class="sprite-dimensions">
                {{ spriteImageDimensions.width }} x {{ spriteImageDimensions.height }}px
              </div>
            </div>

            <!-- Grid Settings (spritesheet mode only) -->
            <div v-if="spriteImportMode === 'spritesheet'" class="grid-settings">
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
            </div>

            <!-- Frame Preview Info (spritesheet mode only) -->
            <div v-if="spriteImportMode === 'spritesheet' && framePreviewInfo" class="frame-preview-info">
              <div class="frame-info-row">
                <span class="label">Frame Size:</span>
                <span class="value">{{ framePreviewInfo.frameWidth }} x {{ framePreviewInfo.frameHeight }}px</span>
              </div>
              <div class="frame-info-row">
                <span class="label">Total Frames:</span>
                <span class="value">{{ framePreviewInfo.totalFrames }}</span>
              </div>
              <div v-if="!framePreviewInfo.framesAlign" class="frame-warning">
                Image doesn't divide evenly into grid
              </div>
            </div>

            <!-- Validation Issues -->
            <div v-if="validationIssues.length > 0" class="validation-issues">
              <div
                v-for="(issue, i) in validationIssues"
                :key="i"
                :class="['validation-issue', issue.severity]"
              >
                <span class="issue-icon">{{ issue.severity === 'error' ? '✕' : '⚠' }}</span>
                <span class="issue-message">{{ issue.message }}</span>
              </div>
            </div>

            <div class="dialog-actions">
              <button
                @click="performImport"
                class="confirm-btn"
                :disabled="hasBlockingErrors"
                :title="hasBlockingErrors ? 'Fix errors before importing' : ''"
              >
                Import
              </button>
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
import { computed, ref, watch } from "vue";
import { safeCoordinateDefault, safeNonNegativeDefault } from "@/utils/typeGuards";
import type { PBRMaterialConfig } from "@/services/materialSystem";
import {
  loadImageFromFile,
  type SpriteValidationIssue,
  validateLoadedSprite,
  validateLoadedSpritesheet,
} from "@/services/spriteValidation";
import { useAssetStore, type EnvironmentState } from "@/stores/assetStore";
import type { AssetType } from "@/types/assets";

const assetStore = useAssetStore();

// Tab configuration
const tabs = [
  { id: "materials", label: "Materials", icon: "◉", tooltip: "PBR Materials" },
  { id: "svg", label: "SVG", icon: "✎", tooltip: "SVG Logos & Shapes" },
  { id: "meshes", label: "Meshes", icon: "◇", tooltip: "Mesh Particles" },
  { id: "sprites", label: "Sprites", icon: "▦", tooltip: "Sprite Sheets" },
  { id: "environment", label: "Env", icon: "☀", tooltip: "Environment Map" },
];

const activeTab = ref("materials");

// Material presets
const materialPresets = [
  "chrome",
  "gold",
  "silver",
  "copper",
  "brass",
  "glass",
  "plastic",
  "rubber",
  "wood",
  "concrete",
  "emissive",
  "holographic",
];
const selectedPreset = ref("");

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
const selectedPrimitive = ref("");

// Sprite import state
const showSpriteImport = ref(false);
const pendingSpriteFile = ref<File | null>(null);
const spriteColumns = ref(4);
const spriteRows = ref(4);
const spriteFrameRate = ref(24);

// Enhanced sprite import state
const spriteImportMode = ref<AssetType>("spritesheet");
const spritePreview = ref<string | null>(null);
const spriteImage = ref<HTMLImageElement | null>(null);
const spriteImageDimensions = ref<{ width: number; height: number } | null>(
  null,
);
const framePreviewInfo = ref<{
  frameWidth: number;
  frameHeight: number;
  totalFrames: number;
  framesAlign: boolean;
} | null>(null);
const validationIssues = ref<SpriteValidationIssue[]>([]);
const hasBlockingErrors = ref(false);

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                // materials
// ═══════════════════════════════════════════════════════════════════════════

function createMaterial() {
  assetStore.createEmptyMaterial("New Material");
}

function createFromPreset() {
  if (selectedPreset.value) {
    assetStore.createMaterialFromPreset(selectedPreset.value);
    selectedPreset.value = "";
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
    assetStore.setMaterialTexture(
      assetStore.selectedMaterialId,
      textureType as keyof PBRMaterialConfig,
      file,
    );
  }
}

function getMaterialPreviewStyle(mat: (typeof materials.value)[0]) {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const maps = (mat != null && typeof mat === "object" && "config" in mat && mat.config != null && typeof mat.config === "object" && "maps" in mat.config && mat.config.maps != null && typeof mat.config.maps === "object") ? mat.config.maps : undefined;
  const albedo = (maps != null && typeof maps === "object" && "albedo" in maps && typeof maps.albedo === "string") ? maps.albedo : undefined;
  return {
    backgroundColor: mat.config.color || "#808080",
    backgroundImage: albedo != null ? `url(${albedo})` : "none",
    backgroundSize: "cover",
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                      // svg
// ═══════════════════════════════════════════════════════════════════════════

async function onSvgUpload(file: File) {
  await assetStore.importSvgFromFile(file);
}

function selectSvg(id: string) {
  assetStore.selectedSvgId = id;
}

function deleteSvg(id: string) {
  assetStore.deleteSvgDocument(id);
}

// Type proof: depth/z coordinate ∈ number | undefined → number (coordinate-like, can be negative)
function getLayerDepth(index: number): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const selectedSvg = assetStore.selectedSvgDocument;
  const layerConfigs = (selectedSvg != null && typeof selectedSvg === "object" && "layerConfigs" in selectedSvg && selectedSvg.layerConfigs != null && Array.isArray(selectedSvg.layerConfigs)) ? selectedSvg.layerConfigs : undefined;
  const layerConfig = (layerConfigs != null && index >= 0 && index < layerConfigs.length) ? layerConfigs[index] : undefined;
  const depth = (layerConfig != null && typeof layerConfig === "object" && "depth" in layerConfig && typeof layerConfig.depth === "number") ? layerConfig.depth : undefined;
  return safeCoordinateDefault(depth, 0, `layerConfigs[${index}].depth`);
}

// Type proof: extrusionDepth ∈ number | undefined → number (≥ 0, extrusion depth)
function getLayerExtrusionDepth(index: number): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const selectedSvgValue = selectedSvg.value;
  const layerConfigs = (selectedSvgValue != null && typeof selectedSvgValue === "object" && "layerConfigs" in selectedSvgValue && selectedSvgValue.layerConfigs != null && Array.isArray(selectedSvgValue.layerConfigs)) ? selectedSvgValue.layerConfigs : undefined;
  const layerConfig = (layerConfigs != null && index >= 0 && index < layerConfigs.length) ? layerConfigs[index] : undefined;
  const extrusionDepth = (layerConfig != null && typeof layerConfig === "object" && "extrusionDepth" in layerConfig && typeof layerConfig.extrusionDepth === "number") ? layerConfig.extrusionDepth : undefined;
  return extrusionDepth != null ? extrusionDepth : 2;
}

function updatePathDepth(pathIndex: number, event: Event) {
  if (!assetStore.selectedSvgId) return;
  // Type proof: depth value ∈ number | NaN → number (coordinate-like, can be negative)
  const parsedValue = parseFloat((event.target as HTMLInputElement).value);
  const value = Number.isFinite(parsedValue) ? parsedValue : 0;
  assetStore.updateSvgLayerConfig(assetStore.selectedSvgId, pathIndex, {
    depth: value,
  });
}

function updatePathExtrusion(pathIndex: number, event: Event) {
  if (!assetStore.selectedSvgId) return;
  const value = parseFloat((event.target as HTMLInputElement).value) || 2;
  assetStore.updateSvgLayerConfig(assetStore.selectedSvgId, pathIndex, {
    extrusionDepth: value,
  });
}

function createLayersFromSvg(svgId: string) {
  // Emit event for parent to handle layer creation
  emit("create-layers-from-svg", svgId);
}

function registerSvgAsMesh(svgId: string) {
  const svg = assetStore.svgDocuments.get(svgId);
  if (!svg) return;

  // Register each path as a mesh particle
  svg.document.paths.forEach((_, i) => {
    assetStore.registerSvgPathAsMesh(svgId, i);
  });

  // Switch to meshes tab
  activeTab.value = "meshes";
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                        // mesh // particles
// ═══════════════════════════════════════════════════════════════════════════

// Type-safe primitive mesh type from registerPrimitiveMesh signature
type PrimitiveMeshType =
  | "cube"
  | "sphere"
  | "cone"
  | "cylinder"
  | "torus"
  | "tetrahedron"
  | "octahedron"
  | "icosahedron";

function addPrimitiveMesh() {
  if (selectedPrimitive.value) {
    // Type-safe assertion - selectedPrimitive.value should be one of the valid primitive types
    const primitiveType = selectedPrimitive.value as PrimitiveMeshType;
    assetStore.registerPrimitiveMesh(primitiveType);
    selectedPrimitive.value = "";
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
    emit("use-mesh-as-emitter", assetStore.selectedMeshParticleId);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                         // sprite // sheets
// ═══════════════════════════════════════════════════════════════════════════

async function onSpriteFileSelect(file: File) {
  pendingSpriteFile.value = file;

  // Create preview URL
  if (spritePreview.value) {
    URL.revokeObjectURL(spritePreview.value);
  }
  spritePreview.value = URL.createObjectURL(file);

  // Load the image to get dimensions
  try {
    const img = await loadImageFromFile(file);
    spriteImage.value = img;
    spriteImageDimensions.value = { width: img.width, height: img.height };

    // Run initial validation
    runValidation();
  } catch (error) {
    console.error("Failed to load sprite image:", error);
    validationIssues.value = [
      {
        severity: "error",
        code: "LOAD_ERROR",
        message: "Failed to load image file",
      },
    ];
    hasBlockingErrors.value = true;
  }
}

function runValidation() {
  if (!spriteImage.value || !pendingSpriteFile.value) return;

  const filename = pendingSpriteFile.value.name;

  if (spriteImportMode.value === "sprite") {
    // Single sprite validation (1x1 grid)
    const result = validateLoadedSprite(spriteImage.value, filename);
    validationIssues.value = result.issues;
    hasBlockingErrors.value = !result.canImport;
    framePreviewInfo.value = null;
  } else {
    // Spritesheet validation
    const result = validateLoadedSpritesheet(
      spriteImage.value,
      filename,
      spriteColumns.value,
      spriteRows.value,
    );
    validationIssues.value = result.issues;
    hasBlockingErrors.value = !result.canImport;

    if (result.metadata) {
      framePreviewInfo.value = {
        frameWidth: result.metadata.frameWidth,
        frameHeight: result.metadata.frameHeight,
        totalFrames: result.metadata.totalFrames,
        framesAlign: result.metadata.framesAlign,
      };
    }
  }
}

function updateFramePreview() {
  if (!spriteImageDimensions.value) return;

  const cols = spriteColumns.value || 1;
  const rows = spriteRows.value || 1;
  const frameWidth = spriteImageDimensions.value.width / cols;
  const frameHeight = spriteImageDimensions.value.height / rows;
  const framesAlign =
    Number.isInteger(frameWidth) && Number.isInteger(frameHeight);

  framePreviewInfo.value = {
    frameWidth: Math.floor(frameWidth),
    frameHeight: Math.floor(frameHeight),
    totalFrames: cols * rows,
    framesAlign,
  };

  // Re-run validation when grid changes
  runValidation();
}

// Watch for grid changes to update preview
watch([spriteColumns, spriteRows], () => {
  if (spriteImportMode.value === "spritesheet" && spriteImage.value) {
    updateFramePreview();
  }
});

// Watch for mode changes to re-run validation
watch(spriteImportMode, () => {
  if (spriteImage.value) {
    runValidation();
  }
});

async function performImport() {
  if (!pendingSpriteFile.value || hasBlockingErrors.value) return;

  if (spriteImportMode.value === "sprite") {
    // Import as single sprite
    await assetStore.importSprite(pendingSpriteFile.value, {
      name: pendingSpriteFile.value.name.replace(/\.[^.]+$/, ""),
    });
  } else {
    // Import as spritesheet with validation
    await assetStore.importSpriteSheetValidated(
      pendingSpriteFile.value,
      spriteColumns.value,
      spriteRows.value,
      { frameRate: spriteFrameRate.value },
    );
  }

  cancelSpriteImport();
}

async function _importSpriteSheet() {
  // Legacy function - redirect to performImport
  await performImport();
}

function cancelSpriteImport() {
  showSpriteImport.value = false;
  pendingSpriteFile.value = null;

  // Cleanup preview URL
  if (spritePreview.value) {
    URL.revokeObjectURL(spritePreview.value);
    spritePreview.value = null;
  }

  // Reset state
  spriteImage.value = null;
  spriteImageDimensions.value = null;
  framePreviewInfo.value = null;
  validationIssues.value = [];
  hasBlockingErrors.value = false;
  spriteImportMode.value = "spritesheet";
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

// ═══════════════════════════════════════════════════════════════════════════
//                                                              // environment
// ═══════════════════════════════════════════════════════════════════════════

function onEnvironmentUpdate(settings: Partial<EnvironmentState>) {
  assetStore.updateEnvironment(settings);
  emit("environment-update", settings);
}

async function onEnvironmentLoad(file: File) {
  await assetStore.loadEnvironment(file);
  emit("environment-load", assetStore.environment);
}

function onEnvironmentClear() {
  assetStore.clearEnvironment();
  emit("environment-clear");
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                                   // events
// ═══════════════════════════════════════════════════════════════════════════

const emit = defineEmits<{
  (e: "create-layers-from-svg", svgId: string): void;
  (e: "use-mesh-as-emitter", meshId: string): void;
  (e: "environment-update", settings: Partial<EnvironmentState>): void;
  (e: "environment-load", settings: Partial<EnvironmentState>): void;
  (e: "environment-clear"): void;
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

/* Import Mode Toggle */
.import-mode-toggle {
  display: flex;
  gap: 4px;
  margin-bottom: 12px;
}

.import-mode-toggle button {
  flex: 1;
  padding: 8px;
  background: #2a2a2a;
  border: 1px solid #333;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  font-size: 12px;
}

.import-mode-toggle button:hover {
  background: #333;
  color: #e0e0e0;
}

.import-mode-toggle button.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: white;
}

/* Sprite Preview */
.sprite-preview-container {
  margin: 12px 0;
  text-align: center;
}

.sprite-preview-image {
  max-width: 100%;
  max-height: 120px;
  object-fit: contain;
  background: #1a1a1a;
  border: 1px solid #333;
  border-radius: 4px;
}

.sprite-dimensions {
  margin-top: 4px;
  font-size: 11px;
  color: #888;
}

/* Grid Settings */
.grid-settings {
  display: flex;
  gap: 8px;
}

.grid-settings label {
  flex: 1;
}

/* Frame Preview Info */
.frame-preview-info {
  background: #1a1a1a;
  border: 1px solid #333;
  border-radius: 4px;
  padding: 8px;
  margin: 12px 0;
}

.frame-info-row {
  display: flex;
  justify-content: space-between;
  padding: 4px 0;
}

.frame-info-row .label {
  color: #888;
  font-size: 12px;
}

.frame-info-row .value {
  color: #e0e0e0;
  font-size: 12px;
}

.frame-warning {
  margin-top: 8px;
  padding: 4px 8px;
  background: rgba(255, 170, 0, 0.15);
  border: 1px solid #996600;
  border-radius: 3px;
  color: #ffaa00;
  font-size: 11px;
}

/* Validation Issues */
.validation-issues {
  margin: 12px 0;
}

.validation-issue {
  display: flex;
  align-items: flex-start;
  gap: 8px;
  padding: 8px;
  border-radius: 4px;
  margin-bottom: 4px;
  font-size: 12px;
}

.validation-issue.error {
  background: rgba(220, 53, 69, 0.15);
  border: 1px solid #dc3545;
  color: #ff6b6b;
}

.validation-issue.warning {
  background: rgba(255, 170, 0, 0.15);
  border: 1px solid #996600;
  color: #ffaa00;
}

.issue-icon {
  font-size: 14px;
  flex-shrink: 0;
}

.issue-message {
  flex: 1;
  line-height: 1.4;
}

.confirm-btn:disabled {
  background: #555;
  color: #888;
  cursor: not-allowed;
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
