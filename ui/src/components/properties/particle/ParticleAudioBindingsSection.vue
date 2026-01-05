<template>
  <div class="property-section">
    <div class="section-header" @click="$emit('toggle')">
      <i class="pi" :class="expanded ? 'pi-chevron-down' : 'pi-chevron-right'" />
      <span>Audio Bindings</span>
      <button class="add-btn" @click.stop="$emit('add')" title="Add Audio Binding">
        <i class="pi pi-plus" />
      </button>
    </div>
    <div v-if="expanded" class="section-content">
      <div v-if="audioBindings.length === 0" class="empty-message">
        No audio bindings. Click + to add one.
      </div>
      <div
        v-for="binding in audioBindings"
        :key="binding.id"
        class="force-item"
      >
        <div class="force-header">
          <input
            type="checkbox"
            :checked="binding.enabled"
            @change="$emit('update', binding.id, 'enabled', ($event.target as HTMLInputElement).checked)"
          />
          <span>{{ binding.feature }} → {{ binding.parameter }}</span>
          <button class="remove-btn" @click="$emit('remove', binding.id)" title="Remove">
            <i class="pi pi-times" />
          </button>
        </div>
        <div class="force-content">
          <div class="property-row">
            <label>Feature</label>
            <select
              :value="binding.feature"
              @change="$emit('update', binding.id, 'feature', ($event.target as HTMLSelectElement).value)"
            >
              <option value="amplitude">Amplitude</option>
              <option value="bass">Bass</option>
              <option value="mid">Mid</option>
              <option value="high">High</option>
              <option value="beat">Beat</option>
              <option value="spectralCentroid">Spectral Centroid</option>
            </select>
          </div>
          <div class="property-row">
            <label title="Minimum audio value to respond to (filters quiet audio)">Input Min</label>
            <input
              type="range"
              :value="binding.min"
              min="0"
              max="1"
              step="0.05"
              @input="$emit('update', binding.id, 'min', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ binding.min.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label title="Maximum audio value (values above this are capped)">Input Max</label>
            <input
              type="range"
              :value="binding.max"
              min="0"
              max="1"
              step="0.05"
              @input="$emit('update', binding.id, 'max', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ binding.max.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label>Target</label>
            <select
              :value="binding.target"
              @change="$emit('update', binding.id, 'target', ($event.target as HTMLSelectElement).value)"
            >
              <option value="emitter">Emitter</option>
              <option value="system">System</option>
              <option value="forceField">Force Field</option>
            </select>
          </div>
          <div class="property-row">
            <label>Parameter</label>
            <select
              :value="binding.parameter"
              @change="$emit('update', binding.id, 'parameter', ($event.target as HTMLSelectElement).value)"
            >
              <option value="emissionRate">Emission Rate</option>
              <option value="speed">Speed</option>
              <option value="size">Size</option>
              <option value="lifetime">Lifetime</option>
              <option value="spread">Spread</option>
              <option value="gravity">Gravity</option>
              <option value="strength">Force Strength</option>
            </select>
          </div>
          <div class="property-row">
            <label title="Temporal smoothing (0=instant, 1=very slow)">Smoothing</label>
            <input
              type="range"
              :value="binding.smoothing"
              min="0"
              max="1"
              step="0.05"
              @input="$emit('update', binding.id, 'smoothing', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ binding.smoothing.toFixed(2) }}</span>
          </div>
          <div class="property-row">
            <label>Output Min</label>
            <input
              type="number"
              :value="binding.outputMin"
              step="1"
              @input="$emit('update', binding.id, 'outputMin', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>Output Max</label>
            <input
              type="number"
              :value="binding.outputMax"
              step="1"
              @input="$emit('update', binding.id, 'outputMax', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>Curve</label>
            <select
              :value="binding.curve"
              @change="$emit('update', binding.id, 'curve', ($event.target as HTMLSelectElement).value)"
            >
              <option value="linear">Linear</option>
              <option value="exponential">Exponential</option>
              <option value="logarithmic">Logarithmic</option>
              <option value="step">Step</option>
            </select>
          </div>
          <div v-if="binding.curve === 'step'" class="property-row">
            <label title="Number of discrete steps (2-20)">Step Count</label>
            <input
              type="number"
              :value="binding.stepCount ?? 5"
              min="2"
              max="20"
              step="1"
              @input="$emit('update', binding.id, 'stepCount', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label title="When to apply this binding">Trigger Mode</label>
            <select
              :value="binding.triggerMode ?? 'continuous'"
              @change="$emit('update', binding.id, 'triggerMode', ($event.target as HTMLSelectElement).value)"
            >
              <option value="continuous">Continuous</option>
              <option value="onThreshold">On Threshold</option>
              <option value="onBeat">On Beat</option>
            </select>
          </div>
          <div v-if="binding.triggerMode === 'onThreshold'" class="property-row">
            <label title="Audio value must exceed this to apply (0-1)">Threshold</label>
            <input
              type="range"
              :value="binding.threshold ?? 0.5"
              min="0"
              max="1"
              step="0.05"
              @input="$emit('update', binding.id, 'threshold', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ (binding.threshold ?? 0.5).toFixed(2) }}</span>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import type { AudioBindingConfig } from "@/types/project";

interface Props {
  audioBindings: AudioBindingConfig[];
  expanded: boolean;
}

defineProps<Props>();

defineEmits<{
  (e: "toggle"): void;
  (e: "add"): void;
  (e: "remove", id: string): void;
  (e: "update", id: string, key: keyof AudioBindingConfig, value: any): void;
}>();
</script>

<style scoped>
.force-content {
  padding: 8px;
}
</style>
