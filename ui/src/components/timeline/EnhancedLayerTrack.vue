<template>
  <div class="track-wrapper" v-if="layer">
    <template v-if="layoutMode === 'sidebar'">
      <div class="sidebar-row" :class="{ selected: isSelected }" :style="gridStyle" @mousedown="selectLayer">
        <div class="arrow-col" @mousedown.stop="toggleExpand">
          <span class="arrow">{{ isExpanded ? '▼' : '▶' }}</span>
        </div>
        <div class="label-box" @mousedown.stop="toggleColorPicker" :style="{ background: layer.labelColor || '#999' }"></div>
        <div class="layer-id">{{ index }}</div>
        <div class="icon-col" @mousedown.stop="toggleVis">{{ layer.visible ? '👁' : '•' }}</div>
        <div class="icon-col" @mousedown.stop="toggleLock">{{ layer.locked ? '🔒' : '🔓' }}</div>
        <div class="icon-col cube-icon" :class="{ active: layer.threeD }" @mousedown.stop="store.toggleLayer3D(layer.id)">⬡</div>
        <div class="layer-name-col" @dblclick.stop="startRename">
          <span class="type-icon">{{ getLayerIcon(layer.type) }}</span>
          <span v-if="!isRenaming" class="name-text">{{ layer.name }}</span>
          <input v-else v-model="renameVal" @blur="saveRename" @keydown.enter="saveRename" class="rename-input" ref="renameInput" />
        </div>
        <div class="col-mode">
          <select :value="layer.blendMode" class="mini-select" @change="setBlendMode" @mousedown.stop>
            <optgroup label="Normal">
              <option value="normal">Normal</option>
              <option value="dissolve">Dissolve</option>
            </optgroup>
            <optgroup label="Darken">
              <option value="darken">Darken</option>
              <option value="multiply">Multiply</option>
              <option value="colorBurn">Color Burn</option>
              <option value="linearBurn">Linear Burn</option>
            </optgroup>
            <optgroup label="Lighten">
              <option value="add">Add</option>
              <option value="lighten">Lighten</option>
              <option value="screen">Screen</option>
              <option value="colorDodge">Color Dodge</option>
              <option value="linearDodge">Linear Dodge</option>
            </optgroup>
            <optgroup label="Contrast">
              <option value="overlay">Overlay</option>
              <option value="softLight">Soft Light</option>
              <option value="hardLight">Hard Light</option>
              <option value="vividLight">Vivid Light</option>
              <option value="linearLight">Linear Light</option>
              <option value="pinLight">Pin Light</option>
              <option value="hardMix">Hard Mix</option>
            </optgroup>
            <optgroup label="Inversion">
              <option value="difference">Difference</option>
              <option value="exclusion">Exclusion</option>
              <option value="subtract">Subtract</option>
              <option value="divide">Divide</option>
            </optgroup>
            <optgroup label="Component">
              <option value="hue">Hue</option>
              <option value="saturation">Saturation</option>
              <option value="color">Color</option>
              <option value="luminosity">Luminosity</option>
            </optgroup>
          </select>
        </div>
        <div class="col-parent">
          <select :value="layer.parentId || ''" class="mini-select" @change="setParent" @mousedown.stop>
            <option value="">None</option>
            <option v-for="p in availableParents" :key="p.id" :value="p.id">{{ p.index }}</option>
          </select>
        </div>
      </div>

      <div v-if="isExpanded" class="children-container">
        <div v-for="(groupProps, groupName) in groupedProperties" :key="groupName" class="property-group">
          <div class="group-header sidebar-row" :style="gridStyle" @mousedown.stop="toggleGroup(groupName)">
             <div class="arrow-col"><span class="arrow">{{ expandedGroups.includes(groupName) ? '▼' : '▶' }}</span></div>
             <div class="group-label">{{ groupName }}</div>
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
  </div>
</template>

<script setup lang="ts">
import { ref, computed, nextTick } from 'vue';
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
  const ppf = props.pixelsPerFrame || 10;
  // Width includes both inPoint and outPoint frames (+1 for inclusive range)
  return { left: `${props.layer.inPoint * ppf}px`, width: `${(props.layer.outPoint - props.layer.inPoint + 1) * ppf}px` };
});

function selectLayer() { emit('select', props.layer.id); }
function toggleExpand() { emit('toggleExpand', props.layer.id, !isExpanded.value); }
function toggleGroup(g: string) {
    if(expandedGroups.value.includes(g)) expandedGroups.value = expandedGroups.value.filter(x => x !== g);
    else expandedGroups.value.push(g);
}
function getLayerIcon(t: string) { return { text: 'T', solid: '■', camera: '📷' }[t] || '•'; }
function startRename() { isRenaming.value = true; renameVal.value = props.layer.name; nextTick(() => renameInput.value?.focus()); }
function saveRename() { emit('updateLayer', props.layer.id, { name: renameVal.value }); isRenaming.value = false; }
function setParent(e: Event) { emit('updateLayer', props.layer.id, { parentId: (e.target as HTMLSelectElement).value || null }); }
function setBlendMode(e: Event) { emit('updateLayer', props.layer.id, { blendMode: (e.target as HTMLSelectElement).value }); }
function startDrag() { /* Drag logic */ }
function toggleVis() { emit('updateLayer', props.layer.id, { visible: !props.layer.visible }); }
function toggleLock() { emit('updateLayer', props.layer.id, { locked: !props.layer.locked }); }
function toggleColorPicker() { /* Color logic */ }
</script>

<style scoped>
.track-wrapper { display: flex; flex-direction: column; width: 100%; }
.sidebar-row { border-bottom: 1px solid #2a2a2a; background: #1e1e1e; color: #ccc; font-size: 13px; user-select: none; cursor: pointer; }
.sidebar-row.selected { background: #333; color: #fff; border-left: 2px solid #4a90d9; }
.arrow-col, .icon-col { display: flex; justify-content: center; align-items: center; cursor: pointer; color: #888; height: 100%; }
.arrow-col:hover, .icon-col:hover { color: #fff; }
.icon-col.active { color: #4a90d9; }
.label-box { width: 14px; height: 14px; border: 1px solid #000; margin: 0 auto; border-radius: 2px; }
.layer-id { text-align: center; font-size: 11px; color: #666; }
.layer-name-col { display: flex; align-items: center; padding: 0 8px; overflow: hidden; }
.type-icon { margin-right: 6px; font-size: 11px; }
.name-text { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; font-size: 13px; font-weight: 500; }
.mini-select { width: 100%; background: transparent; border: none; color: #aaa; font-size: 11px; }
.children-container { background: #151515; }
.group-header { background: #222; font-weight: 600; color: #999; cursor: pointer; }
.group-label { grid-column: 7 / -1; padding-left: 4px; font-size: 12px; }
.track-bg { height: 32px; background: #191919; border-bottom: 1px solid #333; position: relative; }
.duration-bar { position: absolute; height: 20px; top: 6px; border: 1px solid rgba(0,0,0,0.5); border-radius: 2px; background: #888; opacity: 0.6; }
.bar-fill { width: 100%; height: 100%; }
</style>
