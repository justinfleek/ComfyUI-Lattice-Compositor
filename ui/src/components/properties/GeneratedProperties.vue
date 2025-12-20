<template>
  <div class="generated-properties">
    <!-- Status Banner -->
    <div class="status-banner" :class="generatedData.status">
      <span class="status-icon">{{ statusIcon }}</span>
      <span class="status-text">{{ statusText }}</span>
      <span v-if="generatedData.lastGenerated" class="status-time">
        {{ formatTime(generatedData.lastGenerated) }}
      </span>
    </div>

    <!-- Error Message -->
    <div v-if="generatedData.status === 'error' && generatedData.errorMessage" class="error-message">
      {{ generatedData.errorMessage }}
    </div>

    <!-- Generation Type -->
    <div class="prop-section">
      <div class="section-title">Generation Settings</div>

      <div class="row">
        <label>Type</label>
        <select :value="generatedData.generationType" @change="updateData('generationType', ($event.target as HTMLSelectElement).value)">
          <option value="depth">Depth Map</option>
          <option value="normal">Normal Map</option>
          <option value="edge">Edge Detection</option>
          <option value="segment">Segmentation</option>
          <option value="inpaint">Inpainting</option>
          <option value="custom">Custom</option>
        </select>
      </div>

      <div class="row">
        <label>Model</label>
        <select :value="generatedData.model" @change="updateData('model', ($event.target as HTMLSelectElement).value)">
          <optgroup label="Depth Models">
            <option value="depth-anything-v2">Depth Anything V2</option>
            <option value="midas">MiDaS</option>
            <option value="zoedepth">ZoeDepth</option>
          </optgroup>
          <optgroup label="Normal Models">
            <option value="normal-bae">Normal BAE</option>
            <option value="omnidata">Omnidata</option>
          </optgroup>
          <optgroup label="Edge Models">
            <option value="canny">Canny Edge</option>
            <option value="hed">HED</option>
            <option value="pidinet">PidiNet</option>
          </optgroup>
          <optgroup label="Segmentation">
            <option value="sam">SAM</option>
            <option value="oneformer">OneFormer</option>
          </optgroup>
        </select>
      </div>
    </div>

    <!-- Source Layer -->
    <div class="prop-section">
      <div class="section-title">Source</div>

      <div class="row">
        <label>Source Layer</label>
        <select :value="generatedData.sourceLayerId || ''" @change="updateData('sourceLayerId', ($event.target as HTMLSelectElement).value || null)">
          <option value="">None</option>
          <option v-for="layer in sourceLayers" :key="layer.id" :value="layer.id">
            {{ layer.name }}
          </option>
        </select>
      </div>

      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="generatedData.autoRegenerate" @change="updateData('autoRegenerate', !generatedData.autoRegenerate)" />
          Auto-regenerate on source change
        </label>
      </div>
    </div>

    <!-- Actions -->
    <div class="prop-section">
      <div class="section-title">Actions</div>

      <div class="action-buttons">
        <button
          class="action-btn primary"
          @click="regenerate"
          :disabled="generatedData.status === 'generating' || !generatedData.sourceLayerId"
        >
          <span class="btn-icon">{{ generatedData.status === 'generating' ? '...' : '▶' }}</span>
          {{ generatedData.status === 'generating' ? 'Generating...' : 'Generate' }}
        </button>

        <button
          class="action-btn"
          @click="clearGenerated"
          :disabled="generatedData.status === 'generating'"
        >
          Clear
        </button>
      </div>

      <p v-if="!generatedData.sourceLayerId" class="hint">
        Select a source layer to generate from
      </p>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import type { Layer, GeneratedLayerData } from '@/types/project';

const props = defineProps<{
  layer: Layer;
}>();

const emit = defineEmits<{
  (e: 'update', data: Partial<GeneratedLayerData>): void;
}>();

const store = useCompositorStore();

const generatedData = computed(() => props.layer.data as GeneratedLayerData);

// Get layers that can be sources (images, video, other layers - not this one)
const sourceLayers = computed(() => {
  return store.layers.filter(l =>
    l.id !== props.layer.id &&
    ['image', 'video', 'solid', 'text', 'spline', 'shape'].includes(l.type)
  );
});

const statusIcon = computed(() => {
  switch (generatedData.value.status) {
    case 'pending': return '○';
    case 'generating': return '◐';
    case 'complete': return '●';
    case 'error': return '✕';
    default: return '○';
  }
});

const statusText = computed(() => {
  switch (generatedData.value.status) {
    case 'pending': return 'Not generated';
    case 'generating': return 'Generating...';
    case 'complete': return 'Complete';
    case 'error': return 'Error';
    default: return 'Unknown';
  }
});

function updateData<K extends keyof GeneratedLayerData>(key: K, value: GeneratedLayerData[K]) {
  emit('update', { [key]: value } as Partial<GeneratedLayerData>);
}

function regenerate() {
  // Set status to generating - actual generation would be handled by AI service
  emit('update', { status: 'generating' });

  // Simulate generation (in real app, this would call the AI service)
  setTimeout(() => {
    emit('update', {
      status: 'complete',
      lastGenerated: new Date().toISOString()
    });
  }, 2000);
}

function clearGenerated() {
  emit('update', {
    status: 'pending',
    generatedAssetId: null,
    lastGenerated: undefined,
    errorMessage: undefined
  });
}

function formatTime(isoString: string): string {
  const date = new Date(isoString);
  return date.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });
}
</script>

<style scoped>
.generated-properties {
  padding: 8px 0;
}

.status-banner {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  margin: 0 10px 12px;
  border-radius: 4px;
  font-size: 13px;
}

.status-banner.pending {
  background: #2a2a2a;
  color: #888;
}

.status-banner.generating {
  background: rgba(74, 144, 217, 0.2);
  color: #4a90d9;
}

.status-banner.complete {
  background: rgba(46, 204, 113, 0.2);
  color: #2ecc71;
}

.status-banner.error {
  background: rgba(231, 76, 60, 0.2);
  color: #e74c3c;
}

.status-icon {
  font-size: 14px;
}

.status-text {
  flex: 1;
  font-weight: 500;
}

.status-time {
  font-size: 12px;
  opacity: 0.7;
}

.error-message {
  margin: 0 10px 12px;
  padding: 8px;
  background: rgba(231, 76, 60, 0.1);
  border: 1px solid rgba(231, 76, 60, 0.3);
  border-radius: 4px;
  color: #e74c3c;
  font-size: 12px;
}

.prop-section {
  margin-bottom: 12px;
  padding: 0 10px;
}

.section-title {
  font-size: 12px;
  font-weight: 600;
  color: #4a90d9;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: 8px;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.row label {
  min-width: 90px;
  font-size: 13px;
  color: #888;
}

.row select {
  flex: 1;
  padding: 4px 8px;
  background: #1e1e1e;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.row select:focus {
  outline: none;
  border-color: #4a90d9;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  min-width: auto;
  color: #e0e0e0;
  font-size: 13px;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
  accent-color: #4a90d9;
}

.action-buttons {
  display: flex;
  gap: 8px;
}

.action-btn {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 8px 12px;
  border: 1px solid #3a3a3a;
  border-radius: 4px;
  background: #252525;
  color: #e0e0e0;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.15s;
}

.action-btn:hover:not(:disabled) {
  background: #333;
}

.action-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.action-btn.primary {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.action-btn.primary:hover:not(:disabled) {
  background: #5aa0e9;
}

.btn-icon {
  font-size: 12px;
}

.hint {
  margin-top: 8px;
  font-size: 12px;
  color: #666;
  text-align: center;
}
</style>
