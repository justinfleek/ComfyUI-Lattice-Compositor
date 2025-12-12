<template>
  <div class="timeline-panel">
    <!-- Timeline header -->
    <div class="timeline-header">
      <div class="header-left">
        <span class="timeline-title">Timeline</span>
        <span class="timeline-info">
          {{ store.frameCount }} frames @ {{ store.fps }}fps
        </span>
      </div>

      <div class="header-center">
        <!-- Playback controls -->
        <div class="playback-controls">
          <button @click="goToStart" title="Go to Start (Home)">
            <span class="icon">|&lt;</span>
          </button>
          <button @click="stepBackward" title="Previous Frame (Page Up)">
            <span class="icon">&lt;</span>
          </button>
          <button @click="togglePlayback" :class="{ active: isPlaying }" title="Play/Pause (Space)">
            <span class="icon">{{ isPlaying ? '||' : '>' }}</span>
          </button>
          <button @click="stepForward" title="Next Frame (Page Down)">
            <span class="icon">&gt;</span>
          </button>
          <button @click="goToEnd" title="Go to End (End)">
            <span class="icon">&gt;|</span>
          </button>
        </div>

        <!-- Loop mode -->
        <button
          class="loop-btn"
          :class="{ active: loopMode !== 'none' }"
          @click="cycleLoopMode"
          :title="`Loop: ${loopMode}`"
        >
          <span class="icon">{{ loopMode === 'none' ? 'L-' : loopMode === 'loop' ? 'LP' : 'PP' }}</span>
        </button>
      </div>

      <div class="header-right">
        <!-- Search filter -->
        <input
          type="text"
          v-model="searchFilter"
          placeholder="Search layers..."
          class="search-input"
        />

        <!-- Add layer button -->
        <button class="add-layer-btn" @click="showAddLayerMenu = !showAddLayerMenu">
          <span class="icon">+</span>
          Add Layer
        </button>

        <!-- Add layer dropdown -->
        <div v-if="showAddLayerMenu" class="add-layer-menu">
          <button @click="addLayer('spline')">Spline Path</button>
          <button @click="addLayer('text')">Text</button>
          <button @click="addLayer('solid')">Solid</button>
          <button @click="addLayer('null')">Null Object</button>
          <button @click="addLayer('camera')">Camera</button>
          <button @click="addLayer('light')">Light</button>
        </div>
      </div>
    </div>

    <!-- Column headers -->
    <div class="column-headers">
      <div class="layer-columns-header">
        <span class="col-header col-label" title="Label Color">L</span>
        <span class="col-header col-av" title="Audio/Video">AV</span>
        <span class="col-header col-solo" title="Solo">S</span>
        <span class="col-header col-lock" title="Lock">Lk</span>
        <span class="col-header col-name">Layer Name</span>
        <span class="col-header col-parent" title="Parent & Link">Par</span>
        <span class="col-header col-switches" title="Layer Switches">Switches</span>
      </div>
      <div class="track-header">
        <!-- Work area indicator will be here -->
      </div>
    </div>

    <!-- Timeline content -->
    <div class="timeline-content" ref="timelineContentRef">
      <!-- Time ruler with work area -->
      <div class="time-ruler">
        <div class="ruler-sidebar" />
        <div class="ruler-track" ref="rulerTrackRef" @mousedown="startRulerScrub" @dblclick="setMarkerAtClick">
          <!-- Work area -->
          <div
            class="work-area"
            :style="workAreaStyle"
            @mousedown="startWorkAreaDrag"
          >
            <div class="work-area-handle start" @mousedown.stop="startWorkAreaTrim('start', $event)" />
            <div class="work-area-handle end" @mousedown.stop="startWorkAreaTrim('end', $event)" />
          </div>

          <!-- Markers -->
          <div
            v-for="marker in markers"
            :key="marker.id"
            class="marker"
            :style="{ left: `${(marker.frame / store.frameCount) * 100}%` }"
            :class="{ selected: selectedMarkerId === marker.id }"
            @click.stop="selectMarker(marker.id)"
            @dblclick.stop="editMarker(marker.id)"
            :title="`${marker.label} (Frame ${marker.frame})`"
          >
            <div class="marker-flag" :style="{ background: marker.color }" />
          </div>

          <!-- Time ruler marks -->
          <div
            v-for="mark in rulerMarks"
            :key="mark.frame"
            class="ruler-mark"
            :class="{ major: mark.major }"
            :style="{ left: `${mark.position}%` }"
          >
            <span v-if="mark.major" class="mark-label">{{ formatTimecode(mark.frame) }}</span>
          </div>
        </div>
      </div>

      <!-- Layer tracks -->
      <div class="layer-tracks" ref="layerTracksRef">
        <template v-for="layer in filteredLayers" :key="layer.id">
          <EnhancedLayerTrack
            :layer="layer"
            :frameCount="store.frameCount"
            :allLayers="store.layers"
            :soloedLayerIds="soloedLayerIds"
            :showSwitches="showLayerSwitches"
            @select="selectLayer"
            @updateLayer="updateLayer"
            @selectKeyframe="selectKeyframe"
            @setParent="setLayerParent"
            @toggleSolo="toggleSolo"
          />
        </template>

        <!-- Empty state -->
        <div v-if="filteredLayers.length === 0" class="empty-state">
          <p v-if="searchFilter">No layers match "{{ searchFilter }}"</p>
          <template v-else>
            <p>No layers yet</p>
            <p class="hint">Click "Add Layer" to create a layer</p>
          </template>
        </div>
      </div>

      <!-- Playhead -->
      <div
        class="playhead"
        :style="{ left: `${trackOffset + playheadPosition}px` }"
      >
        <div class="playhead-head" />
        <div class="playhead-line" />
      </div>
    </div>

    <!-- Timeline scrubber / mini-timeline -->
    <div class="timeline-scrubber">
      <div class="scrubber-sidebar">
        <!-- Layer switches toggle -->
        <button
          class="toggle-switches-btn"
          :class="{ active: showLayerSwitches }"
          @click="showLayerSwitches = !showLayerSwitches"
          title="Toggle Layer Switches"
        >
          Sw
        </button>
        <span class="frame-label">
          {{ formatTimecode(store.currentFrame) }}
        </span>
      </div>

      <div
        class="scrubber-track"
        @mousedown="startScrub"
        @click="scrubClick"
      >
        <!-- Work area preview -->
        <div class="scrubber-work-area" :style="scrubberWorkAreaStyle" />
        <div
          class="scrubber-progress"
          :style="{ width: `${scrubProgress}%` }"
        />
      </div>

      <div class="frame-input">
        <input
          type="number"
          :value="store.currentFrame"
          :min="0"
          :max="store.frameCount - 1"
          @change="setFrameFromInput"
        />
        <span class="frame-total">/ {{ store.frameCount - 1 }}</span>
      </div>
    </div>

    <!-- Marker edit dialog -->
    <div v-if="editingMarker" class="marker-dialog" @click.self="editingMarker = null">
      <div class="marker-dialog-content">
        <h3>Edit Marker</h3>
        <div class="form-row">
          <label>Label:</label>
          <input type="text" v-model="editingMarker.label" />
        </div>
        <div class="form-row">
          <label>Frame:</label>
          <input type="number" v-model.number="editingMarker.frame" />
        </div>
        <div class="form-row">
          <label>Color:</label>
          <input type="color" v-model="editingMarker.color" />
        </div>
        <div class="form-row">
          <label>Comment:</label>
          <textarea v-model="editingMarker.comment" rows="3" />
        </div>
        <div class="dialog-actions">
          <button @click="deleteMarker(editingMarker.id)">Delete</button>
          <button @click="editingMarker = null">Cancel</button>
          <button class="primary" @click="saveMarker">Save</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed, onMounted, onUnmounted, reactive, watch } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer } from '@/types/project';
import EnhancedLayerTrack from './EnhancedLayerTrack.vue';

const store = useCompositorStore();

const timelineContentRef = ref<HTMLDivElement | null>(null);
const rulerTrackRef = ref<HTMLDivElement | null>(null);
const layerTracksRef = ref<HTMLDivElement | null>(null);
const showAddLayerMenu = ref(false);

// Track dimensions
const trackOffset = 220; // Width of layer info sidebar (increased for switches)
const trackWidth = ref(600);

// Search filter
const searchFilter = ref('');

// Layer switches visibility
const showLayerSwitches = ref(true);

// Playback state
const isPlaying = ref(false);
const loopMode = ref<'none' | 'loop' | 'pingpong'>('loop');
let playbackInterval: number | null = null;
let playDirection = 1;

// Work area
const workArea = reactive({
  start: 0,
  end: store.frameCount - 1
});

// Markers
interface Marker {
  id: string;
  frame: number;
  label: string;
  color: string;
  comment: string;
}

const markers = ref<Marker[]>([]);
const selectedMarkerId = ref<string | null>(null);
const editingMarker = ref<Marker | null>(null);

// Soloed layers
const soloedLayerIds = ref<string[]>([]);

// Computed
const filteredLayers = computed(() => {
  if (!searchFilter.value) return store.layers;
  const filter = searchFilter.value.toLowerCase();
  return store.layers.filter(layer =>
    layer.name.toLowerCase().includes(filter)
  );
});

const playheadPosition = computed(() => {
  return (store.currentFrame / store.frameCount) * trackWidth.value;
});

const scrubProgress = computed(() => {
  return (store.currentFrame / (store.frameCount - 1)) * 100;
});

const workAreaStyle = computed(() => {
  const startPercent = (workArea.start / store.frameCount) * 100;
  const endPercent = ((workArea.end + 1) / store.frameCount) * 100;
  return {
    left: `${startPercent}%`,
    width: `${endPercent - startPercent}%`
  };
});

const scrubberWorkAreaStyle = computed(() => {
  return workAreaStyle.value;
});

// Ruler marks with timecode
const rulerMarks = computed(() => {
  const marks: Array<{ frame: number; position: number; major: boolean }> = [];
  const frameCount = store.frameCount;

  // Calculate step based on zoom
  const step = Math.max(1, Math.floor(frameCount / 20));
  const majorStep = step * 2;

  for (let i = 0; i <= frameCount; i += step) {
    marks.push({
      frame: i,
      position: (i / frameCount) * 100,
      major: i % majorStep === 0
    });
  }

  return marks;
});

// Format frame as timecode
function formatTimecode(frame: number): string {
  const fps = store.fps;
  const totalSeconds = frame / fps;
  const minutes = Math.floor(totalSeconds / 60);
  const seconds = Math.floor(totalSeconds % 60);
  const frames = frame % fps;

  return `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}:${frames.toString().padStart(2, '0')}`;
}

// Update track width on mount and resize
function updateTrackWidth() {
  if (rulerTrackRef.value) {
    trackWidth.value = rulerTrackRef.value.offsetWidth;
  }
}

// Playback controls
function togglePlayback() {
  isPlaying.value = !isPlaying.value;

  if (isPlaying.value) {
    playDirection = 1;
    playbackInterval = window.setInterval(() => {
      let nextFrame = store.currentFrame + playDirection;

      // Handle work area bounds
      if (nextFrame > workArea.end) {
        if (loopMode.value === 'loop') {
          nextFrame = workArea.start;
        } else if (loopMode.value === 'pingpong') {
          playDirection = -1;
          nextFrame = store.currentFrame - 1;
        } else {
          stopPlayback();
          return;
        }
      } else if (nextFrame < workArea.start) {
        if (loopMode.value === 'pingpong') {
          playDirection = 1;
          nextFrame = store.currentFrame + 1;
        }
      }

      store.setFrame(Math.max(workArea.start, Math.min(workArea.end, nextFrame)));
    }, 1000 / store.fps);
  } else {
    stopPlayback();
  }
}

function stopPlayback() {
  isPlaying.value = false;
  if (playbackInterval) {
    clearInterval(playbackInterval);
    playbackInterval = null;
  }
}

function goToStart() {
  store.setFrame(workArea.start);
}

function goToEnd() {
  store.setFrame(workArea.end);
}

function stepForward() {
  store.setFrame(Math.min(store.currentFrame + 1, workArea.end));
}

function stepBackward() {
  store.setFrame(Math.max(store.currentFrame - 1, workArea.start));
}

function cycleLoopMode() {
  const modes: typeof loopMode.value[] = ['none', 'loop', 'pingpong'];
  const currentIndex = modes.indexOf(loopMode.value);
  loopMode.value = modes[(currentIndex + 1) % modes.length];
}

// Layer actions
function selectLayer(layerId: string) {
  store.selectLayer(layerId);
}

function updateLayer(layerId: string, updates: Partial<Layer>) {
  store.updateLayer(layerId, updates);
}

function selectKeyframe(keyframeId: string) {
  const index = store.selectedKeyframeIds.indexOf(keyframeId);
  if (index >= 0) {
    store.selectedKeyframeIds.splice(index, 1);
  } else {
    store.selectedKeyframeIds.push(keyframeId);
  }
}

function addLayer(type: string) {
  store.createLayer(type as any);
  showAddLayerMenu.value = false;
}

function setLayerParent(childId: string, parentId: string | null) {
  store.updateLayer(childId, { parentId });
}

function toggleSolo(layerId: string) {
  const index = soloedLayerIds.value.indexOf(layerId);
  if (index >= 0) {
    soloedLayerIds.value.splice(index, 1);
  } else {
    soloedLayerIds.value.push(layerId);
  }
}

// Work area
let workAreaDragType: 'move' | 'start' | 'end' | null = null;
let workAreaDragStart = 0;

function startWorkAreaDrag(event: MouseEvent) {
  workAreaDragType = 'move';
  workAreaDragStart = event.clientX;
  document.addEventListener('mousemove', handleWorkAreaDrag);
  document.addEventListener('mouseup', stopWorkAreaDrag);
}

function startWorkAreaTrim(type: 'start' | 'end', event: MouseEvent) {
  workAreaDragType = type;
  document.addEventListener('mousemove', handleWorkAreaDrag);
  document.addEventListener('mouseup', stopWorkAreaDrag);
}

function handleWorkAreaDrag(event: MouseEvent) {
  if (!rulerTrackRef.value || !workAreaDragType) return;

  const rect = rulerTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const frame = Math.round((x / rect.width) * store.frameCount);

  if (workAreaDragType === 'start') {
    workArea.start = Math.max(0, Math.min(frame, workArea.end - 1));
  } else if (workAreaDragType === 'end') {
    workArea.end = Math.min(store.frameCount - 1, Math.max(frame, workArea.start + 1));
  } else if (workAreaDragType === 'move') {
    const dx = event.clientX - workAreaDragStart;
    const frameShift = Math.round((dx / rect.width) * store.frameCount);

    const newStart = workArea.start + frameShift;
    const newEnd = workArea.end + frameShift;

    if (newStart >= 0 && newEnd <= store.frameCount - 1) {
      workArea.start = newStart;
      workArea.end = newEnd;
    }

    workAreaDragStart = event.clientX;
  }
}

function stopWorkAreaDrag() {
  workAreaDragType = null;
  document.removeEventListener('mousemove', handleWorkAreaDrag);
  document.removeEventListener('mouseup', stopWorkAreaDrag);
}

// Markers
function setMarkerAtClick(event: MouseEvent) {
  if (!rulerTrackRef.value) return;

  const rect = rulerTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const frame = Math.round((x / rect.width) * store.frameCount);

  const newMarker: Marker = {
    id: `marker-${Date.now()}`,
    frame,
    label: `Marker ${markers.value.length + 1}`,
    color: '#ffc107',
    comment: ''
  };

  markers.value.push(newMarker);
  editingMarker.value = { ...newMarker };
}

function selectMarker(markerId: string) {
  selectedMarkerId.value = selectedMarkerId.value === markerId ? null : markerId;
}

function editMarker(markerId: string) {
  const marker = markers.value.find(m => m.id === markerId);
  if (marker) {
    editingMarker.value = { ...marker };
  }
}

function saveMarker() {
  if (!editingMarker.value) return;

  const index = markers.value.findIndex(m => m.id === editingMarker.value!.id);
  if (index >= 0) {
    markers.value[index] = { ...editingMarker.value };
  }
  editingMarker.value = null;
}

function deleteMarker(markerId: string) {
  markers.value = markers.value.filter(m => m.id !== markerId);
  if (selectedMarkerId.value === markerId) {
    selectedMarkerId.value = null;
  }
  editingMarker.value = null;
}

// Scrubbing
let isScrubbing = false;
let isRulerScrubbing = false;

function startScrub(event: MouseEvent) {
  isScrubbing = true;
  scrubClick(event);
  document.addEventListener('mousemove', handleScrub);
  document.addEventListener('mouseup', stopScrub);
}

// Ruler track scrubbing (main timeline)
function startRulerScrub(event: MouseEvent) {
  // Don't start scrub if clicking on work area handles
  const target = event.target as HTMLElement;
  if (target.classList.contains('work-area-handle') || target.classList.contains('work-area')) {
    return;
  }

  isRulerScrubbing = true;
  rulerScrubClick(event);
  document.addEventListener('mousemove', handleRulerScrub);
  document.addEventListener('mouseup', stopRulerScrub);
}

function rulerScrubClick(event: MouseEvent) {
  if (!rulerTrackRef.value) return;

  const rect = rulerTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const progress = Math.max(0, Math.min(1, x / rect.width));
  const frame = Math.round(progress * (store.frameCount - 1));
  store.setFrame(frame);
}

function handleRulerScrub(event: MouseEvent) {
  if (!isRulerScrubbing || !rulerTrackRef.value) return;

  const rect = rulerTrackRef.value.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const progress = Math.max(0, Math.min(1, x / rect.width));
  const frame = Math.round(progress * (store.frameCount - 1));
  store.setFrame(frame);
}

function stopRulerScrub() {
  isRulerScrubbing = false;
  document.removeEventListener('mousemove', handleRulerScrub);
  document.removeEventListener('mouseup', stopRulerScrub);
}

function scrubClick(event: MouseEvent) {
  const target = event.currentTarget as HTMLElement;
  const rect = target.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const progress = Math.max(0, Math.min(1, x / rect.width));
  const frame = Math.round(progress * (store.frameCount - 1));
  store.setFrame(frame);
}

function handleScrub(event: MouseEvent) {
  if (!isScrubbing) return;

  const scrubberTrack = document.querySelector('.scrubber-track');
  if (!scrubberTrack) return;

  const rect = scrubberTrack.getBoundingClientRect();
  const x = event.clientX - rect.left;
  const progress = Math.max(0, Math.min(1, x / rect.width));
  const frame = Math.round(progress * (store.frameCount - 1));
  store.setFrame(frame);
}

function stopScrub() {
  isScrubbing = false;
  document.removeEventListener('mousemove', handleScrub);
  document.removeEventListener('mouseup', stopScrub);
}

function setFrameFromInput(event: Event) {
  const input = event.target as HTMLInputElement;
  const frame = parseInt(input.value, 10);
  if (!isNaN(frame)) {
    store.setFrame(frame);
  }
}

// Keyboard shortcuts
function handleKeyDown(event: KeyboardEvent) {
  // Don't handle if in input
  if ((event.target as HTMLElement).tagName === 'INPUT' ||
      (event.target as HTMLElement).tagName === 'TEXTAREA') {
    return;
  }

  switch (event.key) {
    case ' ':
      event.preventDefault();
      togglePlayback();
      break;
    case 'Home':
      goToStart();
      break;
    case 'End':
      goToEnd();
      break;
    case 'PageUp':
      stepBackward();
      break;
    case 'PageDown':
      stepForward();
      break;
    case 'b':
    case 'B':
      // Set work area start
      workArea.start = store.currentFrame;
      break;
    case 'n':
    case 'N':
      // Set work area end
      workArea.end = store.currentFrame;
      break;
  }
}

// Close menu when clicking outside
function handleClickOutside(event: MouseEvent) {
  const target = event.target as HTMLElement;
  if (!target.closest('.add-layer-btn') && !target.closest('.add-layer-menu')) {
    showAddLayerMenu.value = false;
  }
}

onMounted(() => {
  updateTrackWidth();
  window.addEventListener('resize', updateTrackWidth);
  document.addEventListener('click', handleClickOutside);
  document.addEventListener('keydown', handleKeyDown);

  // Initialize work area
  workArea.end = store.frameCount - 1;
});

onUnmounted(() => {
  stopPlayback();
  window.removeEventListener('resize', updateTrackWidth);
  document.removeEventListener('click', handleClickOutside);
  document.removeEventListener('keydown', handleKeyDown);
});

// Update work area when frame count changes
watch(() => store.frameCount, (newCount) => {
  if (workArea.end >= newCount) {
    workArea.end = newCount - 1;
  }
});
</script>

<style scoped>
.timeline-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: #1e1e1e;
  color: #e0e0e0;
  font-size: 12px;
}

.timeline-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 6px 12px;
  background: #252525;
  border-bottom: 1px solid #333;
  gap: 12px;
}

.header-left {
  display: flex;
  align-items: center;
  gap: 12px;
}

.timeline-title {
  font-weight: 500;
}

.timeline-info {
  font-size: 11px;
  color: #888;
}

.header-center {
  display: flex;
  align-items: center;
  gap: 8px;
}

.playback-controls {
  display: flex;
  gap: 2px;
}

.playback-controls button {
  width: 28px;
  height: 24px;
  border: 1px solid #444;
  background: #2a2a2a;
  color: #888;
  border-radius: 3px;
  cursor: pointer;
  font-size: 10px;
}

.playback-controls button:hover {
  background: #333;
  color: #fff;
}

.playback-controls button.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.loop-btn {
  width: 28px;
  height: 24px;
  border: 1px solid #444;
  background: #2a2a2a;
  color: #888;
  border-radius: 3px;
  cursor: pointer;
  font-size: 9px;
}

.loop-btn.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.header-right {
  display: flex;
  align-items: center;
  gap: 8px;
  position: relative;
}

.search-input {
  width: 120px;
  padding: 4px 8px;
  border: 1px solid #444;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
}

.search-input:focus {
  outline: none;
  border-color: #7c9cff;
}

.add-layer-btn {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 4px 10px;
  border: none;
  background: #7c9cff;
  color: white;
  border-radius: 4px;
  cursor: pointer;
  font-size: 11px;
}

.add-layer-btn:hover {
  background: #8cacff;
}

.add-layer-menu {
  position: absolute;
  top: 100%;
  right: 0;
  margin-top: 4px;
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 4px;
  overflow: hidden;
  z-index: 100;
  min-width: 120px;
}

.add-layer-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  border: none;
  background: transparent;
  color: #e0e0e0;
  cursor: pointer;
  font-size: 11px;
  text-align: left;
}

.add-layer-menu button:hover {
  background: #3a3a3a;
}

.column-headers {
  display: flex;
  height: 20px;
  background: #222;
  border-bottom: 1px solid #333;
  font-size: 9px;
  color: #666;
}

.layer-columns-header {
  width: 220px;
  min-width: 220px;
  display: flex;
  align-items: center;
  gap: 2px;
  padding: 0 4px;
  border-right: 1px solid #333;
}

.col-header {
  display: flex;
  align-items: center;
  justify-content: center;
}

.col-label { width: 14px; }
.col-av { width: 18px; }
.col-solo { width: 14px; }
.col-lock { width: 14px; }
.col-name { flex: 1; text-align: left; padding-left: 4px; }
.col-parent { width: 30px; }
.col-switches { width: 60px; }

.track-header {
  flex: 1;
}

.timeline-content {
  flex: 1;
  position: relative;
  overflow: auto;
  min-height: 0;
}

.time-ruler {
  display: flex;
  height: 24px;
  background: #222;
  border-bottom: 1px solid #333;
  position: sticky;
  top: 0;
  z-index: 5;
}

.ruler-sidebar {
  width: 220px;
  min-width: 220px;
  border-right: 1px solid #333;
}

.ruler-track {
  flex: 1;
  position: relative;
}

.work-area {
  position: absolute;
  top: 0;
  bottom: 0;
  background: rgba(124, 156, 255, 0.15);
  cursor: move;
}

.work-area-handle {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 6px;
  background: #7c9cff;
  cursor: ew-resize;
}

.work-area-handle.start {
  left: 0;
}

.work-area-handle.end {
  right: 0;
}

.marker {
  position: absolute;
  top: 0;
  width: 0;
  height: 100%;
  z-index: 3;
  cursor: pointer;
}

.marker-flag {
  position: absolute;
  top: 0;
  left: -5px;
  width: 10px;
  height: 10px;
  clip-path: polygon(0 0, 100% 0, 100% 70%, 50% 100%, 0 70%);
}

.marker.selected .marker-flag {
  transform: scale(1.2);
  filter: brightness(1.3);
}

.ruler-mark {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  background: #333;
}

.ruler-mark.major {
  background: #444;
}

.mark-label {
  position: absolute;
  top: 2px;
  left: 4px;
  font-size: 9px;
  color: #666;
  white-space: nowrap;
}

.layer-tracks {
  min-height: 100px;
}

.empty-state {
  padding: 24px;
  text-align: center;
  color: #555;
}

.empty-state .hint {
  font-size: 11px;
  margin-top: 4px;
}

.playhead {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 1px;
  pointer-events: none;
  z-index: 10;
}

.playhead-head {
  position: absolute;
  top: 0;
  left: -5px;
  width: 10px;
  height: 10px;
  background: #ff4444;
  clip-path: polygon(0 0, 100% 0, 50% 100%);
}

.playhead-line {
  position: absolute;
  top: 10px;
  bottom: 0;
  left: 0;
  width: 1px;
  background: #ff4444;
}

.timeline-scrubber {
  display: flex;
  align-items: center;
  padding: 6px 0;
  background: #252525;
  border-top: 1px solid #333;
}

.scrubber-sidebar {
  width: 220px;
  min-width: 220px;
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 0 12px;
}

.toggle-switches-btn {
  padding: 2px 6px;
  border: 1px solid #444;
  background: #2a2a2a;
  color: #666;
  border-radius: 3px;
  cursor: pointer;
  font-size: 9px;
}

.toggle-switches-btn.active {
  background: #7c9cff;
  border-color: #7c9cff;
  color: #fff;
}

.frame-label {
  font-size: 11px;
  color: #888;
  font-family: monospace;
}

.scrubber-track {
  flex: 1;
  height: 6px;
  background: #1a1a1a;
  border-radius: 3px;
  cursor: pointer;
  position: relative;
  margin: 0 12px;
  overflow: hidden;
}

.scrubber-work-area {
  position: absolute;
  top: 0;
  bottom: 0;
  background: rgba(124, 156, 255, 0.2);
}

.scrubber-progress {
  position: absolute;
  top: 0;
  left: 0;
  height: 100%;
  background: #7c9cff;
  border-radius: 3px;
  pointer-events: none;
}

.frame-input {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 0 12px;
}

.frame-input input {
  width: 50px;
  padding: 2px 6px;
  border: 1px solid #444;
  background: #1a1a1a;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 11px;
  text-align: right;
}

.frame-input input:focus {
  outline: none;
  border-color: #7c9cff;
}

.frame-total {
  font-size: 11px;
  color: #555;
}

.marker-dialog {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.marker-dialog-content {
  background: #2a2a2a;
  border: 1px solid #444;
  border-radius: 8px;
  padding: 20px;
  min-width: 300px;
}

.marker-dialog-content h3 {
  margin: 0 0 16px;
  font-size: 14px;
}

.form-row {
  display: flex;
  flex-direction: column;
  gap: 4px;
  margin-bottom: 12px;
}

.form-row label {
  font-size: 11px;
  color: #888;
}

.form-row input,
.form-row textarea {
  padding: 6px 8px;
  border: 1px solid #444;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
}

.form-row input[type="color"] {
  width: 50px;
  height: 30px;
  padding: 2px;
}

.dialog-actions {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  margin-top: 16px;
}

.dialog-actions button {
  padding: 6px 12px;
  border: 1px solid #444;
  background: #333;
  color: #e0e0e0;
  border-radius: 4px;
  cursor: pointer;
  font-size: 11px;
}

.dialog-actions button:hover {
  background: #3a3a3a;
}

.dialog-actions button.primary {
  background: #7c9cff;
  border-color: #7c9cff;
}

.dialog-actions button.primary:hover {
  background: #8cacff;
}

.icon {
  font-family: monospace;
  font-weight: bold;
}
</style>
