<template>
  <div class="track-wrapper" v-if="layer">
    <template v-if="layoutMode === 'sidebar'">
      <div class="sidebar-row" :class="{ selected: isSelected }" @mousedown="selectLayer" @contextmenu.prevent="showContextMenu">
        <!-- AV Features (visibility, audio, solo, lock) -->
        <div class="av-features">
          <div class="icon-col" @mousedown.stop="toggleVis" :title="layer.visible ? 'Hide' : 'Show'">
            <span :class="{ inactive: !layer.visible }">👁</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleAudio" :title="layer.audioEnabled !== false ? 'Mute Audio' : 'Enable Audio'">
            <span :class="{ inactive: layer.audioEnabled === false }">🔊</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleSolo" :title="layer.solo ? 'Unsolo' : 'Solo'">
            <span :class="{ active: layer.solo }">●</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleLock" :title="layer.locked ? 'Unlock' : 'Lock'">
            <span :class="{ active: layer.locked }">🔒</span>
          </div>
        </div>

        <!-- Layer info: label color, number, expand arrow, name -->
        <div class="layer-info">
          <div class="label-box" @mousedown.stop="toggleColorPicker" :style="{ background: layer.labelColor || '#999' }"></div>
          <div class="layer-id">{{ index }}</div>
          <div class="arrow-col" @mousedown.stop="toggleExpand">
            <span class="arrow">{{ isExpanded ? '▼' : '▶' }}</span>
          </div>
          <div class="layer-name-col" @dblclick.stop="handleDoubleClick">
            <span class="type-icon">{{ getLayerIcon(layer.type) }}</span>
            <span v-if="!isRenaming" class="name-text">{{ layer.name }}</span>
            <input v-else v-model="renameVal" @blur="saveRename" @keydown.enter="saveRename" class="rename-input" ref="renameInput" />
          </div>
        </div>

        <!-- Switches (shy, collapse, quality, fx, frame blend, motion blur, adjustment, 3D) -->
        <div class="layer-switches">
          <div class="icon-col" @mousedown.stop="toggleShy" :title="layer.shy ? 'Unhide when shy enabled' : 'Hide when shy enabled'">
            <span :class="{ active: layer.shy }">🙈</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleCollapse" :title="layer.collapseTransform ? 'Disable Collapse' : 'Collapse Transformations'">
            <span :class="{ active: layer.collapseTransform }">☀</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleQuality" :title="layer.quality === 'best' ? 'Draft Quality' : 'Best Quality'">
            <span :class="{ active: layer.quality === 'best' }">◐</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleEffects" :title="layer.effectsEnabled !== false ? 'Disable Effects' : 'Enable Effects'">
            <span :class="{ active: layer.effectsEnabled !== false, inactive: layer.effectsEnabled === false }">fx</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleFrameBlend" :title="layer.frameBlending ? 'Disable Frame Blending' : 'Enable Frame Blending'">
            <span :class="{ active: layer.frameBlending }">⊞</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleMotionBlur" :title="layer.motionBlur ? 'Disable Motion Blur' : 'Enable Motion Blur'">
            <span :class="{ active: layer.motionBlur }">◔</span>
          </div>
          <div class="icon-col" @mousedown.stop="toggleAdjustment" :title="layer.adjustmentLayer ? 'Disable Adjustment Layer' : 'Make Adjustment Layer'">
            <span :class="{ active: layer.adjustmentLayer }">◐</span>
          </div>
          <div class="icon-col" @mousedown.stop="store.toggleLayer3D(layer.id)" :title="layer.threeD ? 'Make 2D Layer' : 'Make 3D Layer'">
            <span :class="{ active: layer.threeD }">⬡</span>
          </div>
        </div>

        <!-- Parent & Link -->
        <div class="col-parent">
          <select :value="layer.parentId || ''" class="mini-select" @change="setParent" @mousedown.stop>
            <option value="">None</option>
            <option v-for="p in availableParents" :key="p.id" :value="p.id">{{ p.index }}. {{ p.name }}</option>
          </select>
        </div>
      </div>

      <div v-if="isExpanded" class="children-container">
        <div v-for="(groupProps, groupName) in groupedProperties" :key="groupName" class="property-group">
          <div class="group-header sidebar-row" :style="gridStyle" @mousedown.stop="toggleGroup(groupName)">
             <div class="arrow-col"><span class="arrow">{{ expandedGroups.includes(groupName) ? '▼' : '▶' }}</span></div>
             <div class="group-label">
               {{ groupName }}
               <span v-if="groupName === 'Transform'" class="reset-link" @click.stop="resetTransform">Reset</span>
             </div>
          </div>
          <div v-if="expandedGroups.includes(groupName)">
             <PropertyTrack v-for="prop in groupProps" :key="prop.path"
               :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
               layoutMode="sidebar" :gridStyle="gridStyle" :pixelsPerFrame="pixelsPerFrame"
             />
          </div>
        </div>
      </div>
    </template>

    <template v-else>
      <div class="layer-row track-bg" @mousedown="selectLayer">
        <div class="duration-bar" :style="barStyle" @mousedown.stop="startDrag">
           <div class="bar-fill" :style="{ background: layer.labelColor || '#777' }"></div>
        </div>
      </div>
      <div v-if="isExpanded" class="children-container">
        <div v-for="(groupProps, groupName) in groupedProperties" :key="groupName" class="property-group">
           <div class="group-header track-bg"></div>
           <div v-if="expandedGroups.includes(groupName)">
              <PropertyTrack v-for="prop in groupProps" :key="prop.path"
               :layerId="layer.id" :propertyPath="prop.path" :name="prop.name" :property="prop.property"
               layoutMode="track" :pixelsPerFrame="pixelsPerFrame"
             />
           </div>
        </div>
      </div>
    </template>

    <!-- Context Menu -->
    <Teleport to="body">
      <div
        v-if="contextMenuVisible"
        class="layer-context-menu"
        :style="{ left: contextMenuX + 'px', top: contextMenuY + 'px' }"
        @click.stop
      >
        <button @click="duplicateLayer">Duplicate Layer</button>
        <button @click="renameFromMenu">Rename</button>
        <hr />
        <button @click="toggleLayerVisibility">{{ layer.visible ? 'Hide' : 'Show' }} Layer</button>
        <button @click="toggleLayerLock">{{ layer.locked ? 'Unlock' : 'Lock' }} Layer</button>
        <button @click="toggleLayer3D">{{ layer.threeD ? 'Make 2D' : 'Make 3D' }}</button>
        <hr />
        <button @click="precomposeLayer">Pre-compose...</button>
        <hr />
        <button @click="deleteLayer" class="danger">Delete Layer</button>
      </div>
    </Teleport>

    <!-- Layer Color Picker -->
    <Teleport to="body">
      <div
        v-if="showColorPicker"
        class="layer-color-picker"
        :style="{ left: colorPickerX + 'px', top: colorPickerY + 'px' }"
        @click.stop
      >
        <div class="color-grid">
          <button
            v-for="color in labelColors"
            :key="color"
            class="color-swatch"
            :style="{ backgroundColor: color }"
            :class="{ active: layer.labelColor === color }"
            @click="setLabelColor(color)"
          />
        </div>
      </div>
    </Teleport>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, nextTick, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import PropertyTrack from './PropertyTrack.vue';

const props = defineProps(['layer', 'index', 'layoutMode', 'isExpandedExternal', 'allLayers', 'frameCount', 'pixelsPerFrame', 'gridStyle']);
const emit = defineEmits(['toggleExpand', 'select', 'updateLayer']);
const store = useCompositorStore();

const localExpanded = ref(false);
const isExpanded = computed(() => props.isExpandedExternal ?? localExpanded.value);
const isSelected = computed(() => store.selectedLayerIds.includes(props.layer.id));
const expandedGroups = ref<string[]>(['Transform', 'Text', 'More Options']);
const isRenaming = ref(false);
const renameVal = ref('');
const renameInput = ref<HTMLInputElement | null>(null);

// Context menu state
const contextMenuVisible = ref(false);
const contextMenuX = ref(0);
const contextMenuY = ref(0);

// Color picker state
const showColorPicker = ref(false);
const colorPickerX = ref(0);
const colorPickerY = ref(0);

// After Effects label colors
const labelColors = [
  '#999999', // None (gray)
  '#e24b4b', // Red
  '#f5c343', // Yellow
  '#c8e04d', // Lime
  '#4be08e', // Sea Green
  '#4bcde0', // Aqua
  '#5b8ef0', // Blue
  '#9d70e8', // Purple
  '#e070d0', // Pink
  '#e0a070', // Peach
  '#e07070', // Light Red
  '#70e0a0', // Mint
  '#7090e0', // Sky Blue
  '#a070e0', // Violet
  '#e07090', // Rose
  '#90c8e0', // Pale Blue
];

const availableParents = computed(() => props.allLayers?.filter((l: any) => l.id !== props.layer.id) || []);

// Grouping Logic
const groupedProperties = computed(() => {
  const groups: Record<string, any[]> = {};
  const t = props.layer.transform;
  const transformProps: any[] = [];

  // Helper to safely add props
  const add = (path: string, name: string, prop: any) => {
    if (prop) transformProps.push({ path, name, property: prop });
  };

  add('transform.anchorPoint', 'Anchor Point', t.anchorPoint);
  add('transform.position', 'Position', t.position);

  // Z Position: Trust the layer.threeD flag. Pass the position property for Z extraction.
  if (props.layer.threeD) {
    transformProps.push({
      path: 'transform.position.z',
      name: 'Z Position',
      property: t.position // Pass full position property, PropertyTrack handles .z
    });
  }

  add('transform.scale', 'Scale', t.scale);

  if (props.layer.threeD) {
    if (t.orientation) transformProps.push({ path: 'transform.orientation', name: 'Orientation', property: t.orientation });
    if (t.rotationX) transformProps.push({ path: 'transform.rotationX', name: 'X Rotation', property: t.rotationX });
    if (t.rotationY) transformProps.push({ path: 'transform.rotationY', name: 'Y Rotation', property: t.rotationY });
    if (t.rotationZ) transformProps.push({ path: 'transform.rotationZ', name: 'Z Rotation', property: t.rotationZ });
  } else {
    if (t.rotation) transformProps.push({ path: 'transform.rotation', name: 'Rotation', property: t.rotation });
  }
  if (props.layer.opacity) transformProps.push({ path: 'opacity', name: 'Opacity', property: props.layer.opacity });

  groups['Transform'] = transformProps;

  // Geometry Options (for 3D layers)
  if (props.layer.threeD) {
    groups['Geometry Options'] = [
      { path: 'geometry.renderer', name: 'Renderer', property: { value: 'Classic 3D', type: 'dropdown' } }
    ];
  }

  // Material Options (for 3D layers)
  if (props.layer.threeD) {
    const mat = props.layer.materialOptions || {
      castsShadows: 'off',
      lightTransmission: 0,
      acceptsShadows: true,
      acceptsLights: true,
      ambient: 100,
      diffuse: 50,
      specularIntensity: 50,
      specularShininess: 5,
      metal: 100
    };
    groups['Material Options'] = [
      { path: 'materialOptions.castsShadows', name: 'Casts Shadows', property: { value: mat.castsShadows, type: 'dropdown' } },
      { path: 'materialOptions.lightTransmission', name: 'Light Transmission', property: { value: mat.lightTransmission, type: 'percent' } },
      { path: 'materialOptions.acceptsShadows', name: 'Accepts Shadows', property: { value: mat.acceptsShadows, type: 'boolean' } },
      { path: 'materialOptions.acceptsLights', name: 'Accepts Lights', property: { value: mat.acceptsLights, type: 'boolean' } },
      { path: 'materialOptions.ambient', name: 'Ambient', property: { value: mat.ambient, type: 'percent' } },
      { path: 'materialOptions.diffuse', name: 'Diffuse', property: { value: mat.diffuse, type: 'percent' } },
      { path: 'materialOptions.specularIntensity', name: 'Specular Intensity', property: { value: mat.specularIntensity, type: 'percent' } },
      { path: 'materialOptions.specularShininess', name: 'Specular Shininess', property: { value: mat.specularShininess, type: 'percent' } },
      { path: 'materialOptions.metal', name: 'Metal', property: { value: mat.metal, type: 'percent' } }
    ];
  }

  // Custom Properties (Text, etc.)
  if (props.layer.properties) {
    props.layer.properties.forEach((p: any) => {
      const g = p.group || 'Properties';
      if (!groups[g]) groups[g] = [];
      groups[g].push({ path: p.name, name: p.name, property: p });
    });
  }
  return groups;
});

const barStyle = computed(() => {
  const frameCount = props.frameCount || 81;

  // Use CSS percentages - positions relative to parent container width
  // This ensures layer bar fills viewport when layer spans full composition
  const leftPct = (props.layer.inPoint / frameCount) * 100;
  const widthPct = ((props.layer.outPoint - props.layer.inPoint + 1) / frameCount) * 100;

  return {
    left: `${leftPct}%`,
    width: `${widthPct}%`
  };
});

function selectLayer() { emit('select', props.layer.id); }
function toggleExpand() { emit('toggleExpand', props.layer.id, !isExpanded.value); }
function toggleGroup(g: string) {
    if(expandedGroups.value.includes(g)) expandedGroups.value = expandedGroups.value.filter(x => x !== g);
    else expandedGroups.value.push(g);
}
function getLayerIcon(t: string) { return { text: 'T', solid: '■', camera: '📷', precomp: '📦', image: '🖼', video: '🎬' }[t] || '•'; }

// Double-click: enter precomp or start rename
function handleDoubleClick() {
  if (props.layer.type === 'precomp' && props.layer.data?.compositionId) {
    // Enter the precomp composition
    store.enterPrecomp(props.layer.data.compositionId);
  } else {
    // Start rename for other layer types
    startRename();
  }
}

function startRename() { isRenaming.value = true; renameVal.value = props.layer.name; nextTick(() => renameInput.value?.focus()); }
function saveRename() { emit('updateLayer', props.layer.id, { name: renameVal.value }); isRenaming.value = false; }
function setParent(e: Event) { emit('updateLayer', props.layer.id, { parentId: (e.target as HTMLSelectElement).value || null }); }
function setBlendMode(e: Event) { emit('updateLayer', props.layer.id, { blendMode: (e.target as HTMLSelectElement).value }); }
function startDrag() { /* Drag logic */ }
function toggleVis() { emit('updateLayer', props.layer.id, { visible: !props.layer.visible }); }
function toggleLock() { emit('updateLayer', props.layer.id, { locked: !props.layer.locked }); }
function toggleAudio() { emit('updateLayer', props.layer.id, { audioEnabled: props.layer.audioEnabled === false ? true : false }); }
function toggleSolo() { emit('updateLayer', props.layer.id, { solo: !props.layer.solo }); }
function toggleShy() { emit('updateLayer', props.layer.id, { shy: !props.layer.shy }); }
function toggleCollapse() { emit('updateLayer', props.layer.id, { collapseTransform: !props.layer.collapseTransform }); }
function toggleQuality() { emit('updateLayer', props.layer.id, { quality: props.layer.quality === 'best' ? 'draft' : 'best' }); }
function toggleEffects() { emit('updateLayer', props.layer.id, { effectsEnabled: props.layer.effectsEnabled === false ? true : false }); }
function toggleFrameBlend() { emit('updateLayer', props.layer.id, { frameBlending: !props.layer.frameBlending }); }
function toggleMotionBlur() { emit('updateLayer', props.layer.id, { motionBlur: !props.layer.motionBlur }); }
function toggleAdjustment() { emit('updateLayer', props.layer.id, { adjustmentLayer: !props.layer.adjustmentLayer }); }
function toggleColorPicker(e: MouseEvent) {
  const rect = (e.target as HTMLElement).getBoundingClientRect();
  colorPickerX.value = rect.left;
  colorPickerY.value = rect.bottom + 4;
  showColorPicker.value = !showColorPicker.value;
}

function setLabelColor(color: string) {
  emit('updateLayer', props.layer.id, { labelColor: color });
  showColorPicker.value = false;
}

function closeColorPicker() {
  showColorPicker.value = false;
}

// Reset transform to default values
function resetTransform() {
  const comp = store.getActiveComp();
  if (!comp) return;

  // Default values
  const defaultTransform = {
    anchorPoint: { x: comp.settings.width / 2, y: comp.settings.height / 2 },
    position: { x: comp.settings.width / 2, y: comp.settings.height / 2, z: 0 },
    scale: { x: 100, y: 100, z: 100 },
    rotation: 0,
    rotationX: 0,
    rotationY: 0,
    rotationZ: 0,
    orientation: { x: 0, y: 0, z: 0 },
    opacity: 100
  };

  // Reset each transform property value (keep keyframes but update current value)
  const t = props.layer.transform;
  if (t.anchorPoint) t.anchorPoint.value = { ...defaultTransform.anchorPoint };
  if (t.position) t.position.value = props.layer.threeD
    ? { ...defaultTransform.position }
    : { x: defaultTransform.position.x, y: defaultTransform.position.y };
  if (t.scale) t.scale.value = { x: defaultTransform.scale.x, y: defaultTransform.scale.y };
  if (t.rotation) t.rotation.value = defaultTransform.rotation;
  if (t.rotationX) t.rotationX.value = defaultTransform.rotationX;
  if (t.rotationY) t.rotationY.value = defaultTransform.rotationY;
  if (t.rotationZ) t.rotationZ.value = defaultTransform.rotationZ;
  if (t.orientation) t.orientation.value = { ...defaultTransform.orientation };
  if (props.layer.opacity) props.layer.opacity.value = defaultTransform.opacity;

  store.project.meta.modified = new Date().toISOString();
  console.log('[EnhancedLayerTrack] Reset transform for layer:', props.layer.name);
}

// Context menu functions
function showContextMenu(e: MouseEvent) {
  contextMenuX.value = e.clientX;
  contextMenuY.value = e.clientY;
  contextMenuVisible.value = true;
  // Select the layer when showing context menu
  if (!isSelected.value) {
    emit('select', props.layer.id);
  }
}

function hideContextMenu() {
  contextMenuVisible.value = false;
}

function duplicateLayer() {
  store.duplicateLayer(props.layer.id);
  hideContextMenu();
}

function renameFromMenu() {
  hideContextMenu();
  nextTick(() => {
    isRenaming.value = true;
    renameVal.value = props.layer.name;
    nextTick(() => renameInput.value?.focus());
  });
}

function toggleLayerVisibility() {
  emit('updateLayer', props.layer.id, { visible: !props.layer.visible });
  hideContextMenu();
}

function toggleLayerLock() {
  emit('updateLayer', props.layer.id, { locked: !props.layer.locked });
  hideContextMenu();
}

function toggleLayer3D() {
  store.toggleLayer3D(props.layer.id);
  hideContextMenu();
}

function precomposeLayer() {
  store.selectLayer(props.layer.id);
  store.precomposeSelectedLayers(props.layer.name + ' Precomp');
  hideContextMenu();
}

function deleteLayer() {
  store.deleteLayer(props.layer.id);
  hideContextMenu();
}

// Close context menu and color picker on outside click
function handleOutsideClick(e: MouseEvent) {
  if (contextMenuVisible.value) {
    hideContextMenu();
  }
  if (showColorPicker.value) {
    closeColorPicker();
  }
}

onMounted(() => {
  document.addEventListener('click', handleOutsideClick);
});

onUnmounted(() => {
  document.removeEventListener('click', handleOutsideClick);
});
</script>

<style scoped>
.track-wrapper { display: flex; flex-direction: column; width: 100%; }

/* Sidebar row - flex layout */
.sidebar-row {
  display: flex;
  align-items: stretch;
  height: 28px;
  border-bottom: 1px solid #2a2a2a;
  background: #1e1e1e;
  color: #ccc;
  font-size: 12px;
  user-select: none;
  cursor: pointer;
}
.sidebar-row.selected { background: #333; color: #fff; border-left: 2px solid #4a90d9; }

/* AV Features section (visibility, audio, solo, lock) */
.av-features {
  display: flex;
  align-items: center;
  border-right: 1px solid #333;
  flex-shrink: 0;
}

/* Layer info section (color, number, arrow, name) */
.layer-info {
  display: flex;
  align-items: center;
  flex: 1;
  min-width: 0;
  gap: 4px;
  padding: 0 4px;
}

/* Switches section */
.layer-switches {
  display: flex;
  align-items: center;
  border-left: 1px solid #333;
  flex-shrink: 0;
}

/* Icon columns */
.icon-col {
  display: flex;
  justify-content: center;
  align-items: center;
  width: 22px;
  height: 100%;
  cursor: pointer;
  font-size: 11px;
}
.icon-col span { color: #555; transition: color 0.15s; }
.icon-col:hover span { color: #ccc; }
.icon-col span.active { color: #4a90d9; }
.icon-col span.inactive { opacity: 0.3; }

/* Arrow column */
.arrow-col {
  display: flex;
  justify-content: center;
  align-items: center;
  width: 16px;
  cursor: pointer;
}
.arrow { color: #666; font-size: 8px; }
.arrow-col:hover .arrow { color: #ccc; }

/* Label color box */
.label-box {
  width: 12px;
  height: 12px;
  border: 1px solid rgba(0,0,0,0.4);
  border-radius: 2px;
  cursor: pointer;
  flex-shrink: 0;
}
.label-box:hover { border-color: #fff; }

/* Layer number */
.layer-id {
  font-size: 10px;
  color: #666;
  min-width: 16px;
  text-align: center;
  flex-shrink: 0;
}

/* Layer name */
.layer-name-col {
  display: flex;
  align-items: center;
  flex: 1;
  min-width: 0;
  overflow: hidden;
}
.type-icon { margin-right: 4px; font-size: 10px; opacity: 0.7; }
.name-text { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 12px; }
.rename-input { background: #111; border: 1px solid #4a90d9; color: #fff; padding: 2px 4px; font-size: 12px; width: 100%; }

/* Parent column */
.col-parent {
  display: flex;
  align-items: center;
  padding: 0 4px;
  border-left: 1px solid #333;
  min-width: 80px;
}
.mini-select {
  width: 100%;
  background: transparent;
  border: none;
  color: #888;
  font-size: 10px;
  cursor: pointer;
}
.mini-select:hover { color: #ccc; }

/* Children/properties container */
.children-container { background: #151515; }
.group-header { background: #222; font-weight: 600; color: #999; cursor: pointer; }
.group-label {
  grid-column: 7 / -1;
  padding-left: 4px;
  font-size: 12px;
  display: flex;
  align-items: center;
  gap: 12px;
}
.reset-link {
  font-size: 10px;
  color: #4a90d9;
  cursor: pointer;
  font-weight: normal;
}
.reset-link:hover {
  color: #6bb3ff;
  text-decoration: underline;
}

/* Track mode */
.track-bg { height: 28px; background: #191919; border-bottom: 1px solid #333; position: relative; width: 100%; }
.duration-bar { position: absolute; height: 20px; top: 4px; border: 1px solid rgba(0,0,0,0.5); border-radius: 2px; background: #888; opacity: 0.6; }
.bar-fill { width: 100%; height: 100%; }

/* Context Menu - must NOT be scoped to work with Teleport */
</style>

<style>
.layer-context-menu {
  position: fixed;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  z-index: 9999;
  min-width: 180px;
  padding: 4px 0;
}

.layer-context-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: #e0e0e0;
  font-size: 12px;
  text-align: left;
  cursor: pointer;
}

.layer-context-menu button:hover {
  background: #3a5070;
}

.layer-context-menu button.danger {
  color: #e57373;
}

.layer-context-menu button.danger:hover {
  background: #5a3030;
}

.layer-context-menu hr {
  border: none;
  border-top: 1px solid #444;
  margin: 4px 0;
}

/* Layer Color Picker */
.layer-color-picker {
  position: fixed;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  z-index: 9999;
  padding: 8px;
}

.layer-color-picker .color-grid {
  display: grid;
  grid-template-columns: repeat(8, 1fr);
  gap: 4px;
}

.layer-color-picker .color-swatch {
  width: 20px;
  height: 20px;
  border: 1px solid rgba(0, 0, 0, 0.3);
  border-radius: 2px;
  cursor: pointer;
  padding: 0;
}

.layer-color-picker .color-swatch:hover {
  transform: scale(1.15);
  border-color: #fff;
}

.layer-color-picker .color-swatch.active {
  border: 2px solid #fff;
  box-shadow: 0 0 4px rgba(255, 255, 255, 0.5);
}
</style>
