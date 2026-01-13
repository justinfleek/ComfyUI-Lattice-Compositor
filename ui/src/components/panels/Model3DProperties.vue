<template>
  <div class="model-3d-properties">
    <div class="property-section">
      <div class="section-header">
        <span>3D Model Properties</span>
      </div>

      <!-- Model Info -->
      <div class="property-group" v-if="layerData">
        <div class="info-row">
          <span class="label">Source</span>
          <span class="value">{{ layerData.sourceFile || 'Unknown' }}</span>
        </div>
        <div class="info-row" v-if="layerData.vertexCount">
          <span class="label">Vertices</span>
          <span class="value">{{ formatNumber(layerData.vertexCount) }}</span>
        </div>
        <div class="info-row" v-if="layerData.faceCount">
          <span class="label">Faces</span>
          <span class="value">{{ formatNumber(layerData.faceCount) }}</span>
        </div>
      </div>
    </div>

    <!-- Transform -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('transform')">
        <i :class="['icon', sections.transform ? 'expanded' : '']">▸</i>
        <span>Transform</span>
      </div>
      <div v-show="sections.transform" class="section-content">
        <!-- Position -->
        <div class="property-group">
          <label>Position</label>
          <div class="vector3-input">
            <div class="input-item">
              <span class="axis x">X</span>
              <ScrubableNumber
                :modelValue="position.x"
                @update:modelValue="updatePosition('x', $event)"
                :step="1"
              />
            </div>
            <div class="input-item">
              <span class="axis y">Y</span>
              <ScrubableNumber
                :modelValue="position.y"
                @update:modelValue="updatePosition('y', $event)"
                :step="1"
              />
            </div>
            <div class="input-item">
              <span class="axis z">Z</span>
              <ScrubableNumber
                :modelValue="position.z"
                @update:modelValue="updatePosition('z', $event)"
                :step="1"
              />
            </div>
          </div>
        </div>

        <!-- Rotation -->
        <div class="property-group">
          <label>Rotation</label>
          <div class="vector3-input">
            <div class="input-item">
              <span class="axis x">X</span>
              <ScrubableNumber
                :modelValue="rotation.x"
                @update:modelValue="updateRotation('x', $event)"
                :step="1"
                unit="°"
              />
            </div>
            <div class="input-item">
              <span class="axis y">Y</span>
              <ScrubableNumber
                :modelValue="rotation.y"
                @update:modelValue="updateRotation('y', $event)"
                :step="1"
                unit="°"
              />
            </div>
            <div class="input-item">
              <span class="axis z">Z</span>
              <ScrubableNumber
                :modelValue="rotation.z"
                @update:modelValue="updateRotation('z', $event)"
                :step="1"
                unit="°"
              />
            </div>
          </div>
        </div>

        <!-- Scale -->
        <div class="property-group">
          <label>Scale</label>
          <div class="vector3-input">
            <div class="input-item">
              <span class="axis x">X</span>
              <ScrubableNumber
                :modelValue="scale.x"
                @update:modelValue="updateScale('x', $event)"
                :step="1"
                unit="%"
              />
            </div>
            <div class="input-item">
              <span class="axis y">Y</span>
              <ScrubableNumber
                :modelValue="scale.y"
                @update:modelValue="updateScale('y', $event)"
                :step="1"
                unit="%"
              />
            </div>
            <div class="input-item">
              <span class="axis z">Z</span>
              <ScrubableNumber
                :modelValue="scale.z"
                @update:modelValue="updateScale('z', $event)"
                :step="1"
                unit="%"
              />
            </div>
          </div>
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="uniformScale"
              @change="toggleUniformScale"
            />
            Uniform Scale
          </label>
        </div>
      </div>
    </div>

    <!-- Material Assignment -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('material')">
        <i :class="['icon', sections.material ? 'expanded' : '']">▸</i>
        <span>Material</span>
      </div>
      <div v-show="sections.material" class="section-content">
        <div class="property-group">
          <label>Assigned Material</label>
          <select v-model="selectedMaterialId" @change="assignMaterial" class="material-select">
            <option value="">None (Use Model Default)</option>
            <option v-for="mat in materials" :key="mat.id" :value="mat.id">
              {{ mat.name }}
            </option>
          </select>
        </div>

        <button class="action-btn" @click="openMaterialEditor">
          <i class="icon">⬚</i>
          Open Material Editor
        </button>
      </div>
    </div>

    <!-- Display Options -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('display')">
        <i :class="['icon', sections.display ? 'expanded' : '']">▸</i>
        <span>Display</span>
      </div>
      <div v-show="sections.display" class="section-content">
        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="showWireframe"
              @change="toggleWireframe"
            />
            Show Wireframe
          </label>
        </div>

        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="showBoundingBox"
              @change="toggleBoundingBox"
            />
            Show Bounding Box
          </label>
        </div>

        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="castShadows"
              @change="toggleCastShadows"
            />
            Cast Shadows
          </label>
        </div>

        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="receiveShadows"
              @change="toggleReceiveShadows"
            />
            Receive Shadows
          </label>
        </div>
      </div>
    </div>

    <!-- Point Cloud Specific -->
    <div class="property-section" v-if="isPointCloud">
      <div class="section-header" @click="toggleSection('pointCloud')">
        <i :class="['icon', sections.pointCloud ? 'expanded' : '']">▸</i>
        <span>Point Cloud</span>
      </div>
      <div v-show="sections.pointCloud" class="section-content">
        <div class="property-group">
          <label>Point Size</label>
          <SliderInput
            :modelValue="pointSize"
            @update:modelValue="updatePointSize"
            :min="0.1"
            :max="20"
            :step="0.1"
          />
        </div>

        <div class="property-group">
          <label>Point Color</label>
          <ColorPicker
            :modelValue="pointColor"
            @update:modelValue="updatePointColor"
          />
        </div>

        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="useVertexColors"
              @change="toggleVertexColors"
            />
            Use Vertex Colors
          </label>
        </div>

        <div class="property-row">
          <label class="checkbox-label">
            <input
              type="checkbox"
              :checked="sizeAttenuation"
              @change="toggleSizeAttenuation"
            />
            Size Attenuation
          </label>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, reactive, ref, watch } from "vue";
import { useAssetStore } from "@/stores/assetStore";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";

const props = defineProps<{
  layerId: string;
}>();

const emit = defineEmits<{
  "open-material-editor": [];
}>();

const store = useCompositorStore();
const layerStore = useLayerStore();
const assetStore = useAssetStore();

// Section visibility
const sections = reactive({
  transform: true,
  material: true,
  display: false,
  pointCloud: true,
});

// Get layer data
const layer = computed(() => store.layers.find((l) => l.id === props.layerId));
const layerData = computed(() => layer.value?.data as any);

// Check if point cloud
const isPointCloud = computed(() => layer.value?.type === "pointcloud");

// Transform values
const position = computed(() => {
  const val = layer.value?.transform.position.value;
  return val
    ? { x: val.x || 0, y: val.y || 0, z: val.z || 0 }
    : { x: 0, y: 0, z: 0 };
});

const rotation = computed(() => {
  // 3D models use rotationX/Y/Z properties
  const transform = layer.value?.transform;
  if (!transform) return { x: 0, y: 0, z: 0 };

  return {
    x: transform.rotationX?.value || 0,
    y: transform.rotationY?.value || 0,
    z: transform.rotationZ?.value || transform.rotation?.value || 0,
  };
});

const scale = computed(() => {
  const val = layer.value?.transform.scale.value;
  return val
    ? { x: val.x || 100, y: val.y || 100, z: val.z || 100 }
    : { x: 100, y: 100, z: 100 };
});

// Material
const selectedMaterialId = ref<string>("");
const materials = computed(() => assetStore.materialList);

// Display options
const uniformScale = ref(true);
const showWireframe = ref(false);
const showBoundingBox = ref(false);
const castShadows = ref(true);
const receiveShadows = ref(true);

// Point cloud options
const pointSize = ref(2);
const pointColor = ref("#ffffff");
const useVertexColors = ref(true);
const sizeAttenuation = ref(true);

// Initialize from layer data
watch(
  () => props.layerId,
  () => {
    if (layerData.value) {
      selectedMaterialId.value = layerData.value.materialId || "";
      showWireframe.value = layerData.value.wireframe || false;
      showBoundingBox.value = layerData.value.showBoundingBox || false;
      castShadows.value = layerData.value.castShadows ?? true;
      receiveShadows.value = layerData.value.receiveShadows ?? true;

      if (isPointCloud.value) {
        pointSize.value = layerData.value.pointSize || 2;
        pointColor.value = layerData.value.pointColor || "#ffffff";
        useVertexColors.value = layerData.value.useVertexColors ?? true;
        sizeAttenuation.value = layerData.value.sizeAttenuation ?? true;
      }
    }
  },
  { immediate: true },
);

// Methods
function toggleSection(section: keyof typeof sections) {
  sections[section] = !sections[section];
}

function updatePosition(axis: "x" | "y" | "z", value: number) {
  const current = { ...position.value };
  current[axis] = value;
  layerStore.updateLayerTransform(store, props.layerId, { position: current });
}

function updateRotation(axis: "x" | "y" | "z", value: number) {
  // 3D models use rotationX/Y/Z properties, not the single 'rotation' property
  const targetLayer = layer.value;
  if (!targetLayer?.transform) return;

  const propMap = {
    x: targetLayer.transform.rotationX,
    y: targetLayer.transform.rotationY,
    z: targetLayer.transform.rotationZ,
  };

  const prop = propMap[axis];
  if (prop) {
    prop.value = value;
  }
}

function updateScale(axis: "x" | "y" | "z", value: number) {
  if (uniformScale.value) {
    layerStore.updateLayerTransform(store, props.layerId, {
      scale: { x: value, y: value, z: value },
    });
  } else {
    const current = { ...scale.value };
    current[axis] = value;
    layerStore.updateLayerTransform(store, props.layerId, { scale: current });
  }
}

function toggleUniformScale() {
  uniformScale.value = !uniformScale.value;
}

function assignMaterial() {
  layerStore.updateLayerData(store, props.layerId, {
    materialId: selectedMaterialId.value || null,
  });
}

function openMaterialEditor() {
  emit("open-material-editor");
}

function toggleWireframe() {
  showWireframe.value = !showWireframe.value;
  layerStore.updateLayerData(store, props.layerId, { wireframe: showWireframe.value });
}

function toggleBoundingBox() {
  showBoundingBox.value = !showBoundingBox.value;
  layerStore.updateLayerData(store, props.layerId, {
    showBoundingBox: showBoundingBox.value,
  });
}

function toggleCastShadows() {
  castShadows.value = !castShadows.value;
  layerStore.updateLayerData(store, props.layerId, { castShadows: castShadows.value });
}

function toggleReceiveShadows() {
  receiveShadows.value = !receiveShadows.value;
  layerStore.updateLayerData(store, props.layerId, {
    receiveShadows: receiveShadows.value,
  });
}

// Point cloud methods
function updatePointSize(value: number) {
  pointSize.value = value;
  layerStore.updateLayerData(store, props.layerId, { pointSize: value });
}

function updatePointColor(value: string) {
  pointColor.value = value;
  layerStore.updateLayerData(store, props.layerId, { pointColor: value });
}

function toggleVertexColors() {
  useVertexColors.value = !useVertexColors.value;
  layerStore.updateLayerData(store, props.layerId, {
    useVertexColors: useVertexColors.value,
  });
}

function toggleSizeAttenuation() {
  sizeAttenuation.value = !sizeAttenuation.value;
  layerStore.updateLayerData(store, props.layerId, {
    sizeAttenuation: sizeAttenuation.value,
  });
}

function formatNumber(num: number): string {
  return num.toLocaleString();
}
</script>

<style scoped>
.model-3d-properties {
  display: flex;
  flex-direction: column;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 13px;
}

.property-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 12px;
  background: #222;
  cursor: pointer;
  user-select: none;
  font-size: 13px;
  font-weight: 500;
  color: #ccc;
}

.section-header:hover {
  background: #282828;
}

.icon {
  font-size: 11px;
  color: #666;
  transition: transform 0.2s;
}

.icon.expanded {
  transform: rotate(90deg);
}

.section-content {
  padding: 12px;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.property-group {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.property-group > label {
  color: #888;
  font-size: 12px;
  text-transform: uppercase;
}

.property-row {
  display: flex;
  align-items: center;
  justify-content: space-between;
}

.info-row {
  display: flex;
  justify-content: space-between;
  padding: 4px 12px;
}

.info-row .label {
  color: #888;
}

.info-row .value {
  color: #e0e0e0;
}

.vector3-input {
  display: flex;
  gap: 8px;
}

.input-item {
  flex: 1;
  display: flex;
  align-items: center;
  gap: 4px;
}

.axis {
  font-size: 12px;
  font-weight: 600;
  width: 14px;
}

.axis.x { color: #ff6b6b; }
.axis.y { color: #69db7c; }
.axis.z { color: #74c0fc; }

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  color: #ccc;
}

.material-select {
  width: 100%;
  padding: 6px 8px;
  background: #111;
  border: 1px solid #333;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}

.action-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 8px 12px;
  background: #333;
  border: 1px solid #444;
  color: #ccc;
  border-radius: 4px;
  cursor: pointer;
}

.action-btn:hover {
  background: #444;
}
</style>
