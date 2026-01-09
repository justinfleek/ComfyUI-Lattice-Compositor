<template>
  <div class="prop-wrapper">
    <div v-if="layoutMode === 'sidebar'" class="prop-sidebar" :class="{ selected: isSelected }" :style="gridStyle" @click="selectProp">
      <div class="indent-spacer"></div>

      <!-- Animation toggle (left), then keyframe navigator - hidden if property is not animatable -->
      <template v-if="property.animatable !== false">
        <div class="icon-box" @click.stop="toggleAnim" title="Toggle Animation">
          <span class="keyframe-toggle" :class="{ active: property.animated }">◆</span>
        </div>

        <!-- Keyframe Navigator: ◀ ◆ ▶ -->
        <div class="keyframe-nav" v-if="property.animated">
          <button class="nav-btn" @click.stop="goToPrevKeyframe" :disabled="!hasPrevKeyframe" title="Previous Keyframe (J)">
            <span>◀</span>
          </button>
          <button class="nav-btn kf-indicator" @click.stop="addKeyframeAtCurrent" :class="{ active: hasKeyframeAtCurrent }" title="Add/Remove Keyframe">
            <span>◆</span>
          </button>
          <button class="nav-btn" @click.stop="goToNextKeyframe" :disabled="!hasNextKeyframe" title="Next Keyframe (K)">
            <span>▶</span>
          </button>
        </div>

        <!-- Simple add keyframe when not animated -->
        <div class="icon-box" v-else @click.stop="addKeyframeAtCurrent">
          <span class="kf-btn" :class="{ active: hasKeyframeAtCurrent }">◇</span>
        </div>
      </template>
      <!-- Empty spacer when not animatable to maintain alignment -->
      <template v-else>
        <div class="icon-box disabled"></div>
        <div class="icon-box disabled"></div>
      </template>

      <div class="prop-content">
        <span class="prop-name">{{ name }}</span>

        <div class="prop-inputs">
          <!-- Z Position only (special case for 3D layers) -->
          <template v-if="name === 'Z Position'">
            <div class="vec-item">
              <span class="label z-label">Z</span>
              <ScrubableNumber
                :modelValue="property.value?.z ?? 0"
                @update:modelValue="(v: number) => updateValByIndex('z', v)"
              />
            </div>
          </template>

          <!-- Boolean (checkbox) -->
          <template v-else-if="property.type === 'boolean'">
            <div class="checkbox-wrapper">
              <input type="checkbox" :checked="property.value" @change="e => updateValDirect((e.target as HTMLInputElement).checked)" />
            </div>
          </template>

          <!-- Dropdown (dynamic options from property.options or hardcoded for legacy) -->
          <template v-else-if="property.type === 'dropdown'">
            <select class="prop-dropdown" :value="property.value" @change="e => updateValDirect((e.target as HTMLSelectElement).value)" :title="getDropdownTitle()">
              <!-- Dynamic options from property.options array -->
              <template v-if="property.options && Array.isArray(property.options)">
                <option v-for="opt in property.options" :key="opt" :value="opt">{{ formatOptionLabel(opt) }}</option>
              </template>
              <!-- Legacy hardcoded options for backwards compatibility -->
              <template v-else>
                <option v-if="name === 'Casts Shadows'" value="off">Off</option>
                <option v-if="name === 'Casts Shadows'" value="on">On</option>
                <option v-if="name === 'Casts Shadows'" value="only">Only</option>
                <option v-if="name === 'Renderer'" value="Classic 3D">Classic 3D</option>
                <option v-if="name === 'Renderer'" value="CINEMA 4D">CINEMA 4D</option>
                <option v-if="name === 'Renderer'" value="Ray-traced 3D">Ray-traced 3D</option>
              </template>
            </select>
          </template>

          <!-- String input (for things like dash patterns) -->
          <template v-else-if="property.type === 'string'">
            <input
              type="text"
              class="prop-string-input"
              :value="property.value"
              :placeholder="property.placeholder || ''"
              :title="getStringTitle()"
              @change="e => updateValDirect((e.target as HTMLInputElement).value)"
            />
          </template>

          <!-- Percent (0-100) -->
          <template v-else-if="property.type === 'percent'">
            <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="0" :min="0" :max="100" suffix="%" />
          </template>

          <!-- Color input -->
          <template v-else-if="property.type === 'color'">
            <div class="color-input-wrapper">
              <input type="color" :value="property.value" @input="e => updateValDirect((e.target as HTMLInputElement).value)" />
              <span class="color-hex">{{ property.value }}</span>
            </div>
          </template>

          <!-- Vector (X/Y or X/Y/Z) -->
          <template v-else-if="typeof property.value === 'object'">
            <div class="vec-item">
              <span class="label x-label">X</span>
              <ScrubableNumber :modelValue="property.value.x" @update:modelValue="(v: number) => updateValByIndex('x', v)" />
            </div>
            <div class="vec-item">
              <span class="label y-label">Y</span>
              <ScrubableNumber :modelValue="property.value.y" @update:modelValue="(v: number) => updateValByIndex('y', v)" />
            </div>
          </template>

          <!-- Single number -->
          <template v-else-if="typeof property.value === 'number'">
            <ScrubableNumber :modelValue="property.value" @update:modelValue="updateValDirect" :precision="1" />
          </template>
        </div>
      </div>
    </div>

    <div v-else class="prop-track" @mousedown="handleTrackMouseDown" @contextmenu.prevent="showTrackContextMenu" ref="trackRef">
       <!-- Selection box for marquee select -->
       <div v-if="isBoxSelecting" class="selection-box" :style="selectionBoxStyle"></div>

       <div v-for="kf in property.keyframes" :key="kf.id"
            class="keyframe"
            :class="{ selected: selectedKeyframeIds.has(kf.id), [kf.interpolation || 'linear']: true }"
            :style="{ left: `${kf.frame * pixelsPerFrame}px` }"
            @mousedown.stop="startKeyframeDrag($event, kf)"
            @dblclick.stop="deleteKeyframe(kf.id)"
            @contextmenu.prevent.stop="showContextMenu($event, kf)"
       >
         <svg
           class="keyframe-shape"
           :viewBox="getKeyframeShapeViewBox(kf.interpolation)"
           preserveAspectRatio="xMidYMid meet"
         >
           <path
             :d="getKeyframeShapePath(kf.interpolation)"
             :fill="isStrokeShape(kf.interpolation) ? 'none' : 'currentColor'"
             :stroke="isStrokeShape(kf.interpolation) ? 'currentColor' : 'none'"
             stroke-width="1.5"
           />
         </svg>
       </div>

       <!-- Keyframe Context Menu -->
       <div v-if="contextMenu.visible" class="keyframe-context-menu" :style="contextMenuStyle">
         <div class="menu-header">Interpolation</div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'linear' }" @click="setInterpolation('linear')">
           <span class="icon">📈</span> Linear
         </div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'bezier' }" @click="setInterpolation('bezier')">
           <span class="icon">〰️</span> Bezier
         </div>
         <div class="menu-item" :class="{ active: contextMenu.keyframe?.interpolation === 'hold' }" @click="setInterpolation('hold')">
           <span class="icon">⏸️</span> Hold
         </div>
         <div class="menu-divider"></div>
         <div class="menu-item" @click="goToKeyframe">
           <span class="icon">➡️</span> Go to Frame
         </div>
         <div class="menu-item delete" @click="deleteSelectedKeyframes">
           <span class="icon">🗑️</span> Delete
         </div>
       </div>

       <!-- Track Context Menu (right-click on empty track area) -->
       <div v-if="trackContextMenu.visible" class="keyframe-context-menu" :style="trackContextMenuStyle">
         <div class="menu-header">Keyframe</div>
         <div class="menu-item" @click="addKeyframeAtFrame">
           <span class="icon">◆</span> Add Keyframe
         </div>
         <div v-if="isPositionProperty && hasMultipleKeyframes" class="menu-item" @click="insertKeyframeOnPath">
           <span class="icon">➕</span> Insert on Path
         </div>
         <div class="menu-divider"></div>
         <div class="menu-item" @click="goToClickedFrame">
           <span class="icon">➡️</span> Go to Frame {{ trackContextMenu.frame }}
         </div>
       </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, onUnmounted, ref } from "vue";
import { findNearestSnap } from "@/services/timelineSnap";
import { useCompositorStore } from "@/stores/compositorStore";
import { getShapeForEasing, KEYFRAME_SHAPES } from "@/styles/keyframe-shapes";
import type { Keyframe } from "@/types/project";

// Get keyframe shape path for a given interpolation type
function getKeyframeShapePath(interpolation: string = "linear"): string {
  const shapeKey = getShapeForEasing(interpolation);
  return KEYFRAME_SHAPES[shapeKey]?.path || KEYFRAME_SHAPES.diamond.path;
}

function getKeyframeShapeViewBox(interpolation: string = "linear"): string {
  const shapeKey = getShapeForEasing(interpolation);
  const shape = KEYFRAME_SHAPES[shapeKey] || KEYFRAME_SHAPES.diamond;
  return `0 0 ${shape.width} ${shape.height}`;
}

function isStrokeShape(interpolation: string = "linear"): boolean {
  const shapeKey = getShapeForEasing(interpolation);
  return KEYFRAME_SHAPES[shapeKey]?.stroke || false;
}

const props = defineProps([
  "name",
  "property",
  "layerId",
  "propertyPath",
  "layoutMode",
  "pixelsPerFrame",
  "gridStyle",
]);
const emit = defineEmits(["selectKeyframe", "deleteKeyframe", "moveKeyframe"]);
const store = useCompositorStore();

const selectedKeyframeIds = ref<Set<string>>(new Set());
const trackRef = ref<HTMLElement | null>(null);

// Box selection state
const isBoxSelecting = ref(false);
const boxStartX = ref(0);
const boxCurrentX = ref(0);

// Context menu state
const contextMenu = ref<{
  visible: boolean;
  x: number;
  y: number;
  keyframe: Keyframe<any> | null;
}>({
  visible: false,
  x: 0,
  y: 0,
  keyframe: null,
});

const contextMenuStyle = computed(() => ({
  left: `${contextMenu.value.x}px`,
  top: `${contextMenu.value.y}px`,
}));

// Track context menu (right-click on empty track area)
const trackContextMenu = ref<{
  visible: boolean;
  x: number;
  y: number;
  frame: number;
}>({
  visible: false,
  x: 0,
  y: 0,
  frame: 0,
});

const trackContextMenuStyle = computed(() => ({
  left: `${trackContextMenu.value.x}px`,
  top: `${trackContextMenu.value.y}px`,
}));

// Check if this is a position property (for "Insert on Path" option)
const isPositionProperty = computed(
  () =>
    props.propertyPath?.includes("position") ||
    props.name?.toLowerCase().includes("position"),
);

// Check if there are multiple keyframes (needed for path interpolation)
const hasMultipleKeyframes = computed(
  () => (props.property?.keyframes?.length || 0) >= 2,
);

const selectionBoxStyle = computed(() => {
  const left = Math.min(boxStartX.value, boxCurrentX.value);
  const width = Math.abs(boxCurrentX.value - boxStartX.value);
  return {
    left: `${left}px`,
    width: `${width}px`,
  };
});

const hasKeyframeAtCurrent = computed(() =>
  props.property.keyframes?.some((k: any) => k.frame === store.currentFrame),
);
const isSelected = computed(
  () => store.selectedPropertyPath === props.propertyPath,
);

// Keyframe navigator computed properties
const sortedKeyframes = computed(() => {
  const kfs = props.property.keyframes || [];
  return [...kfs].sort((a: any, b: any) => a.frame - b.frame);
});

const hasPrevKeyframe = computed(() => {
  return sortedKeyframes.value.some((kf: any) => kf.frame < store.currentFrame);
});

const hasNextKeyframe = computed(() => {
  return sortedKeyframes.value.some((kf: any) => kf.frame > store.currentFrame);
});

// Keyframe navigator functions
function goToPrevKeyframe() {
  const prevKfs = sortedKeyframes.value.filter(
    (kf: any) => kf.frame < store.currentFrame,
  );
  if (prevKfs.length > 0) {
    const prevKf = prevKfs[prevKfs.length - 1];
    store.setFrame(prevKf.frame);
  }
}

function goToNextKeyframe() {
  const nextKf = sortedKeyframes.value.find(
    (kf: any) => kf.frame > store.currentFrame,
  );
  if (nextKf) {
    store.setFrame(nextKf.frame);
  }
}

function toggleAnim() {
  store.setPropertyAnimated(
    props.layerId,
    props.propertyPath,
    !props.property.animated,
  );
}
function addKeyframeAtCurrent() {
  store.addKeyframe(props.layerId, props.propertyPath, props.property.value);
}
function updateValDirect(v: any) {
  // Handle data.* properties differently - they're stored directly on layer.data
  if (props.propertyPath.startsWith("data.")) {
    const dataKey = props.propertyPath.replace("data.", "");
    store.updateLayerData(props.layerId, { [dataKey]: v });
  } else {
    store.setPropertyValue(props.layerId, props.propertyPath, v);
  }
}
function updateValByIndex(axis: string, v: number) {
  const newVal = { ...props.property.value, [axis]: v };
  store.setPropertyValue(props.layerId, props.propertyPath, newVal);
}
function selectProp() {
  store.selectProperty(props.propertyPath);
}

// Format dropdown option label (capitalize first letter)
function formatOptionLabel(opt: string): string {
  return opt.charAt(0).toUpperCase() + opt.slice(1);
}

// Get tooltip for dropdown based on property name
function getDropdownTitle(): string {
  switch (props.name) {
    case "Line Cap":
      return "Butt: flat end, Round: rounded end, Square: extends end";
    case "Line Join":
      return "Miter: sharp corner, Round: rounded corner, Bevel: flat corner";
    default:
      return "";
  }
}

// Get tooltip for string input based on property name
function getStringTitle(): string {
  switch (props.name) {
    case "Dashes":
      return "Dash pattern: comma-separated values (e.g., 10, 5 for 10px dash, 5px gap)";
    default:
      return "";
  }
}

// Handle mouse down on track - start box selection or navigate
function handleTrackMouseDown(e: MouseEvent) {
  const rect = (e.currentTarget as HTMLElement).getBoundingClientRect();
  const x = e.clientX - rect.left;

  // Start box selection
  isBoxSelecting.value = true;
  boxStartX.value = x;
  boxCurrentX.value = x;

  // Clear selection unless Shift is held
  if (!e.shiftKey) {
    selectedKeyframeIds.value.clear();
  }

  const onMove = (ev: MouseEvent) => {
    const currentX = ev.clientX - rect.left;
    boxCurrentX.value = Math.max(0, currentX);

    // Select keyframes within the box
    const minFrame =
      Math.min(boxStartX.value, boxCurrentX.value) / props.pixelsPerFrame;
    const maxFrame =
      Math.max(boxStartX.value, boxCurrentX.value) / props.pixelsPerFrame;

    if (!ev.shiftKey) {
      selectedKeyframeIds.value.clear();
    }

    for (const kf of props.property.keyframes || []) {
      if (kf.frame >= minFrame && kf.frame <= maxFrame) {
        selectedKeyframeIds.value.add(kf.id);
      }
    }
  };

  const onUp = (_ev: MouseEvent) => {
    isBoxSelecting.value = false;

    // If it was just a click (no drag), navigate to that frame
    const dragDistance = Math.abs(boxCurrentX.value - boxStartX.value);
    if (dragDistance < 5) {
      const frame = Math.round(boxStartX.value / props.pixelsPerFrame);
      store.setFrame(Math.max(0, Math.min(store.frameCount - 1, frame)));
    }

    window.removeEventListener("mousemove", onMove);
    window.removeEventListener("mouseup", onUp);
  };

  window.addEventListener("mousemove", onMove);
  window.addEventListener("mouseup", onUp);
}

// Keyframe selection and dragging
function startKeyframeDrag(e: MouseEvent, kf: Keyframe<any>) {
  // Toggle selection with Shift, otherwise single select
  if (e.shiftKey) {
    if (selectedKeyframeIds.value.has(kf.id)) {
      selectedKeyframeIds.value.delete(kf.id);
    } else {
      selectedKeyframeIds.value.add(kf.id);
    }
  } else {
    selectedKeyframeIds.value.clear();
    selectedKeyframeIds.value.add(kf.id);
  }

  // Check for Ctrl+Alt (scale mode) at drag start
  const isScaleMode = e.ctrlKey && e.altKey;

  // Set up drag
  const startX = e.clientX;
  const startFrame = kf.frame;

  // For scale mode, capture original keyframe positions
  const originalKeyframes: { id: string; frame: number }[] = isScaleMode
    ? props.property?.keyframes?.map((k: { id: string; frame: number }) => ({
        id: k.id,
        frame: k.frame,
      })) || []
    : [];
  const anchorFrame = isScaleMode
    ? Math.min(
        ...originalKeyframes.map((k: { id: string; frame: number }) => k.frame),
      )
    : 0;

  const onMove = (ev: MouseEvent) => {
    const dx = ev.clientX - startX;

    // Ctrl+Alt+Drag = Scale keyframes (maintain spacing proportions)
    if (isScaleMode && originalKeyframes.length > 1) {
      // Calculate scale factor: how much the drag represents relative to original span
      const maxFrame = Math.max(
        ...originalKeyframes.map((k: { id: string; frame: number }) => k.frame),
      );
      const originalSpan = maxFrame - anchorFrame;
      if (originalSpan > 0) {
        // Pixel drag converts to scale factor (100px = 0.5x scale adjustment)
        const scaleDelta = dx / 100;
        const scaleFactor = Math.max(0.1, 1 + scaleDelta);

        // Apply new positions to all keyframes based on scale
        for (const orig of originalKeyframes) {
          const relativePos = orig.frame - anchorFrame;
          const newFrame = Math.max(
            0,
            Math.round(anchorFrame + relativePos * scaleFactor),
          );
          if (newFrame !== orig.frame) {
            // Find current keyframe position and update
            const currentKf = props.property?.keyframes?.find(
              (k: { id: string }) => k.id === orig.id,
            );
            if (currentKf && currentKf.frame !== newFrame) {
              store.moveKeyframe(
                props.layerId,
                props.propertyPath,
                orig.id,
                newFrame,
              );
            }
          }
        }
      }
      return;
    }

    // Normal drag mode - move keyframe
    const frameDelta = Math.round(dx / props.pixelsPerFrame);
    let newFrame = Math.max(
      0,
      Math.min(store.frameCount - 1, startFrame + frameDelta),
    );

    // Apply snapping if enabled (hold Alt/Option to disable temporarily)
    if (!ev.altKey && store.snapConfig.enabled) {
      const snap = findNearestSnap(
        newFrame,
        store.snapConfig,
        props.pixelsPerFrame,
        {
          layers: store.layers,
          selectedLayerId: props.layerId,
          currentFrame: store.currentFrame,
          audioAnalysis: store.audioAnalysis,
          peakData: store.peakData,
        },
      );
      if (snap) {
        newFrame = snap.frame;
      }
    }

    if (newFrame !== kf.frame) {
      store.moveKeyframe(props.layerId, props.propertyPath, kf.id, newFrame);
    }
  };

  const onUp = () => {
    window.removeEventListener("mousemove", onMove);
    window.removeEventListener("mouseup", onUp);
  };

  window.addEventListener("mousemove", onMove);
  window.addEventListener("mouseup", onUp);
}

// Delete keyframe
function deleteKeyframe(kfId: string) {
  store.removeKeyframe(props.layerId, props.propertyPath, kfId);
  selectedKeyframeIds.value.delete(kfId);
}

// Context menu functions
function showContextMenu(e: MouseEvent, kf: Keyframe<any>) {
  // Select the keyframe if not already selected
  if (!selectedKeyframeIds.value.has(kf.id)) {
    selectedKeyframeIds.value.clear();
    selectedKeyframeIds.value.add(kf.id);
  }

  // Position relative to track
  const trackRect = trackRef.value?.getBoundingClientRect();
  if (trackRect) {
    contextMenu.value = {
      visible: true,
      x: e.clientX - trackRect.left,
      y: e.clientY - trackRect.top,
      keyframe: kf,
    };
  }
}

function hideContextMenu() {
  contextMenu.value.visible = false;
  contextMenu.value.keyframe = null;
}

function hideTrackContextMenu() {
  trackContextMenu.value.visible = false;
}

// Show context menu on empty track area (right-click)
function showTrackContextMenu(e: MouseEvent) {
  // Don't show if clicking on a keyframe (that has its own context menu)
  const target = e.target as HTMLElement;
  if (target.closest(".keyframe")) return;

  const rect = trackRef.value?.getBoundingClientRect();
  if (!rect) return;

  // Calculate frame from click position
  const x = e.clientX - rect.left;
  const frame = Math.round(x / props.pixelsPerFrame);

  // Hide any existing keyframe context menu
  hideContextMenu();

  trackContextMenu.value = {
    visible: true,
    x: x,
    y: e.clientY - rect.top,
    frame: Math.max(0, Math.min(store.frameCount - 1, frame)),
  };
}

// Add a keyframe at the clicked frame with interpolated value
function addKeyframeAtFrame() {
  const frame = trackContextMenu.value.frame;
  const currentValue = props.property?.value ?? 0;
  store.addKeyframe(props.layerId, props.propertyPath, currentValue, frame);
  hideTrackContextMenu();
}

// Insert keyframe by interpolating the position motion path
function insertKeyframeOnPath() {
  const frame = trackContextMenu.value.frame;
  const newKfId = store.insertKeyframeOnPath(props.layerId, frame);
  if (newKfId) {
    console.log(`[Lattice] Inserted keyframe on path at frame ${frame}`);
  }
  hideTrackContextMenu();
}

// Navigate to the clicked frame
function goToClickedFrame() {
  store.setFrame(trackContextMenu.value.frame);
  hideTrackContextMenu();
}

function setInterpolation(type: "linear" | "bezier" | "hold") {
  // Apply to all selected keyframes
  for (const kfId of selectedKeyframeIds.value) {
    store.setKeyframeInterpolation(
      props.layerId,
      props.propertyPath,
      kfId,
      type,
    );
  }
  hideContextMenu();
}

function goToKeyframe() {
  if (contextMenu.value.keyframe) {
    store.setFrame(contextMenu.value.keyframe.frame);
  }
  hideContextMenu();
}

function deleteSelectedKeyframes() {
  for (const kfId of selectedKeyframeIds.value) {
    store.removeKeyframe(props.layerId, props.propertyPath, kfId);
  }
  selectedKeyframeIds.value.clear();
  hideContextMenu();
}

// Close context menus on click outside
function handleGlobalClick(_e: MouseEvent) {
  if (contextMenu.value.visible) {
    hideContextMenu();
  }
  if (trackContextMenu.value.visible) {
    hideTrackContextMenu();
  }
}

onMounted(() => {
  document.addEventListener("click", handleGlobalClick);
});

onUnmounted(() => {
  document.removeEventListener("click", handleGlobalClick);
});
</script>

<style scoped>
.prop-wrapper { width: 100%; display: flex; flex-direction: column; }
.prop-sidebar {
  display: flex;
  align-items: center;
  height: 28px;
  border-bottom: 1px solid #2a2a2a;
  background: #1a1a1a;
  font-size: 12px;
  color: #ccc;
  padding-left: 8px;
}
.indent-spacer { width: 20px; flex-shrink: 0; }
.icon-box {
  width: 20px;
  display: flex;
  justify-content: center;
  align-items: center;
  cursor: pointer;
  flex-shrink: 0;
}
.icon-box.disabled { visibility: hidden; }
.kf-btn { font-size: 10px; color: #666; }
.kf-btn.active { color: #f1c40f; }
.keyframe-toggle { font-size: 10px; color: #666; }
.keyframe-toggle.active { color: #3498db; }

/* Keyframe Navigator */
.keyframe-nav {
  display: flex;
  align-items: center;
  gap: 1px;
  margin-left: 4px;
}

.nav-btn {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 16px;
  height: 16px;
  padding: 0;
  border: none;
  background: transparent;
  color: #888;
  font-size: 8px;
  cursor: pointer;
  border-radius: 2px;
  transition: all 0.1s;
}

.nav-btn:hover:not(:disabled) {
  background: #333;
  color: #fff;
}

.nav-btn:disabled {
  color: #444;
  cursor: not-allowed;
}

.nav-btn.kf-indicator {
  font-size: 10px;
  color: #666;
}

.nav-btn.kf-indicator.active {
  color: #f1c40f;
}

.nav-btn.kf-indicator:hover {
  color: #f1c40f;
}

/* Content: property name + inputs */
.prop-content {
  display: flex;
  align-items: center;
  flex: 1;
  min-width: 0;
  padding: 0 8px;
  gap: 8px;
}
.prop-name { width: 100px; flex-shrink: 0; color: #999; font-size: 12px; }
.prop-inputs { display: flex; gap: 6px; flex: 1; align-items: center; justify-content: flex-end; }

.vec-item { display: flex; align-items: center; gap: 4px; }
.label { font-size: 12px; font-weight: bold; }
.x-label { color: #e74c3c; } .y-label { color: #2ecc71; } .z-label { color: #3498db; }

.color-input-wrapper { display: flex; align-items: center; gap: 8px; }
.color-hex { font-family: monospace; font-size: 13px; color: #aaa; }

/* Checkbox styling */
.checkbox-wrapper {
  display: flex;
  align-items: center;
}
.checkbox-wrapper input[type="checkbox"] {
  width: 14px;
  height: 14px;
  cursor: pointer;
  accent-color: #4a90d9;
}

/* Dropdown styling */
.prop-dropdown {
  padding: 2px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
  cursor: pointer;
  min-width: 60px;
  max-width: 80px;
}
.prop-dropdown:hover {
  border-color: #4a90d9;
}
.prop-dropdown:focus {
  outline: none;
  border-color: #4a90d9;
}

/* String input styling */
.prop-string-input {
  padding: 2px 6px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 12px;
  min-width: 60px;
  max-width: 80px;
}
.prop-string-input::placeholder {
  color: #666;
  font-size: 11px;
}
.prop-string-input:hover {
  border-color: #4a90d9;
}
.prop-string-input:focus {
  outline: none;
  border-color: #4a90d9;
  background: #222;
}

.prop-track {
  height: 32px;
  background: var(--lattice-surface-0, #0a0a0a);
  border-bottom: 1px solid var(--lattice-surface-3, #222222);
  position: relative;
  cursor: pointer;
}

.keyframe {
  position: absolute;
  width: 14px;
  height: 24px;
  top: 4px;
  transform: translateX(-7px);
  cursor: ew-resize;
  transition: transform 0.1s, filter 0.1s;
  color: var(--lattice-accent, #8B5CF6);
}

.keyframe-shape {
  width: 100%;
  height: 100%;
}

.keyframe:hover {
  transform: translateX(-7px) scale(1.15);
  filter: brightness(1.2);
}

.keyframe.selected {
  color: white;
  filter: drop-shadow(0 0 4px var(--lattice-accent, #8B5CF6));
}

/* Selection box for marquee select */
.selection-box {
  position: absolute;
  top: 2px;
  bottom: 2px;
  background: rgba(139, 92, 246, 0.2);
  border: 1px solid rgba(139, 92, 246, 0.6);
  pointer-events: none;
  z-index: 5;
}

/* Context Menu */
.keyframe-context-menu {
  position: absolute;
  background: var(--lattice-surface-1, #121212);
  border: none;
  border-radius: var(--lattice-radius-lg, 6px);
  box-shadow: var(--lattice-shadow-dropdown, 0 4px 16px rgba(0, 0, 0, 0.3));
  min-width: 150px;
  z-index: 100;
  padding: 6px 0;
  font-size: var(--lattice-text-sm, 11px);
}

.menu-header {
  padding: 6px 12px;
  color: var(--lattice-text-muted, #6B7280);
  font-size: var(--lattice-text-xs, 10px);
  text-transform: uppercase;
  letter-spacing: 0.5px;
  border-bottom: 1px solid var(--lattice-surface-3, #222222);
  margin-bottom: 4px;
}

.menu-item {
  padding: 8px 12px;
  cursor: pointer;
  display: flex;
  align-items: center;
  gap: 8px;
  color: var(--lattice-text-primary, #e5e5e5);
  transition: var(--lattice-transition-fast, 100ms ease);
}

.menu-item:hover {
  background: var(--lattice-surface-3, #222222);
}

.menu-item.active {
  background: var(--lattice-accent, #8B5CF6);
  color: white;
}

.menu-item.delete {
  color: var(--lattice-error, #F43F5E);
}

.menu-item.delete:hover {
  background: var(--lattice-error-bg, rgba(244, 63, 94, 0.15));
}

.menu-item .icon {
  font-size: var(--lattice-text-lg, 14px);
}

.menu-divider {
  height: 1px;
  background: var(--lattice-surface-3, #222222);
  margin: 4px 0;
}

/* Keyframe interpolation color variants */
.keyframe.hold {
  color: var(--lattice-error, #F43F5E);
}

.keyframe.bezier {
  color: var(--lattice-warning, #F59E0B);
}

.keyframe.spring,
.keyframe.elastic,
.keyframe.bounce {
  color: var(--lattice-success, #10B981);
}
</style>
