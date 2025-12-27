<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="$emit('close')">
      <div class="dialog-box">
        <div class="dialog-header">
          <h3>Keyframe Interpolation</h3>
          <button class="close-btn" @click="$emit('close')">&times;</button>
        </div>
        <div class="dialog-body">
          <!-- Selected keyframes info -->
          <div class="info-row">
            <span class="info-label">Selected Keyframes:</span>
            <span class="info-value">{{ keyframeCount }}</span>
          </div>

          <!-- Interpolation Type -->
          <div class="form-row">
            <label>Temporal Interpolation</label>
            <select v-model="interpolationType" class="select-input">
              <option value="linear">Linear</option>
              <option value="bezier">Bezier (Ease)</option>
              <option value="hold">Hold (Step)</option>
            </select>
          </div>

          <!-- Easing Preset (only for bezier) -->
          <div v-if="interpolationType === 'bezier'" class="form-row">
            <label>Easing Preset</label>
            <select v-model="easingPreset" class="select-input">
              <option value="">Custom</option>
              <optgroup label="Ease In">
                <option value="easeInSine">Ease In Sine</option>
                <option value="easeInQuad">Ease In Quad</option>
                <option value="easeInCubic">Ease In Cubic</option>
                <option value="easeInQuart">Ease In Quart</option>
                <option value="easeInQuint">Ease In Quint</option>
                <option value="easeInExpo">Ease In Expo</option>
                <option value="easeInCirc">Ease In Circ</option>
                <option value="easeInBack">Ease In Back</option>
                <option value="easeInElastic">Ease In Elastic</option>
              </optgroup>
              <optgroup label="Ease Out">
                <option value="easeOutSine">Ease Out Sine</option>
                <option value="easeOutQuad">Ease Out Quad</option>
                <option value="easeOutCubic">Ease Out Cubic</option>
                <option value="easeOutQuart">Ease Out Quart</option>
                <option value="easeOutQuint">Ease Out Quint</option>
                <option value="easeOutExpo">Ease Out Expo</option>
                <option value="easeOutCirc">Ease Out Circ</option>
                <option value="easeOutBack">Ease Out Back</option>
                <option value="easeOutElastic">Ease Out Elastic</option>
                <option value="easeOutBounce">Ease Out Bounce</option>
              </optgroup>
              <optgroup label="Ease In/Out">
                <option value="easeInOutSine">Ease In/Out Sine</option>
                <option value="easeInOutQuad">Ease In/Out Quad</option>
                <option value="easeInOutCubic">Ease In/Out Cubic</option>
                <option value="easeInOutQuart">Ease In/Out Quart</option>
                <option value="easeInOutQuint">Ease In/Out Quint</option>
                <option value="easeInOutExpo">Ease In/Out Expo</option>
                <option value="easeInOutCirc">Ease In/Out Circ</option>
                <option value="easeInOutBack">Ease In/Out Back</option>
                <option value="easeInOutElastic">Ease In/Out Elastic</option>
              </optgroup>
            </select>
          </div>

          <!-- Control Mode (only for bezier) -->
          <div v-if="interpolationType === 'bezier'" class="form-row">
            <label>Handle Mode</label>
            <select v-model="controlMode" class="select-input">
              <option value="symmetric">Symmetric (mirrored)</option>
              <option value="smooth">Smooth (continuous)</option>
              <option value="corner">Corner (independent)</option>
            </select>
          </div>

          <!-- Easing curve preview -->
          <div v-if="interpolationType === 'bezier'" class="curve-preview">
            <svg viewBox="0 0 100 100" class="curve-svg">
              <!-- Grid -->
              <line x1="0" y1="50" x2="100" y2="50" stroke="#333" stroke-width="0.5" />
              <line x1="50" y1="0" x2="50" y2="100" stroke="#333" stroke-width="0.5" />
              <!-- Curve -->
              <path :d="curvePath" fill="none" stroke="#8B5CF6" stroke-width="2" />
              <!-- Start/End points -->
              <circle cx="0" cy="100" r="3" fill="#8B5CF6" />
              <circle cx="100" cy="0" r="3" fill="#8B5CF6" />
            </svg>
          </div>
        </div>
        <div class="dialog-footer">
          <button class="btn-cancel" @click="$emit('close')">Cancel</button>
          <button class="btn-confirm" @click="confirm" :disabled="keyframeCount === 0">Apply</button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { ref, computed, watch } from 'vue';
import { easings } from '@/services/easing';
import type { InterpolationType, BaseInterpolationType, ControlMode } from '@/types/project';

const props = defineProps<{
  visible: boolean;
  keyframeCount: number;
  initialInterpolation?: InterpolationType;
  initialControlMode?: ControlMode;
}>();

const emit = defineEmits<{
  close: [];
  confirm: [settings: {
    interpolation: BaseInterpolationType;
    easingPreset: string;
    controlMode: ControlMode;
  }];
}>();

const interpolationType = ref<BaseInterpolationType>('bezier');
const easingPreset = ref<string>('easeInOutCubic');
const controlMode = ref<ControlMode>('smooth');

// Reset to initial values when dialog opens
watch(() => props.visible, (visible) => {
  if (visible) {
    // Convert easing names to 'bezier' (easing is handled via easingPreset field)
    const initial = props.initialInterpolation;
    const isBaseType = initial === 'linear' || initial === 'bezier' || initial === 'hold';
    interpolationType.value = isBaseType ? initial : 'bezier';
    controlMode.value = props.initialControlMode || 'smooth';
    easingPreset.value = 'easeInOutCubic';
  }
});

// Generate SVG path for curve preview
const curvePath = computed(() => {
  if (interpolationType.value !== 'bezier') {
    return 'M 0 100 L 100 0';
  }

  const easingFn = easings[easingPreset.value as keyof typeof easings] || easings.linear;
  const points: string[] = [];

  for (let i = 0; i <= 100; i += 2) {
    const t = i / 100;
    const y = 100 - easingFn(t) * 100;
    points.push(`${i === 0 ? 'M' : 'L'} ${i} ${y}`);
  }

  return points.join(' ');
});

function confirm() {
  emit('confirm', {
    interpolation: interpolationType.value,
    easingPreset: easingPreset.value,
    controlMode: controlMode.value
  });
  emit('close');
}
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-box {
  background: #1e1e1e;
  border: 1px solid #333;
  border-radius: 8px;
  width: 380px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  border-bottom: 1px solid #333;
}

.dialog-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 600;
  color: #fff;
}

.close-btn {
  background: transparent;
  border: none;
  color: #888;
  font-size: 20px;
  cursor: pointer;
  padding: 0;
  line-height: 1;
}
.close-btn:hover { color: #fff; }

.dialog-body {
  padding: 16px;
}

.info-row {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 8px 0;
  margin-bottom: 12px;
  border-bottom: 1px solid #333;
}

.info-label {
  color: #888;
  font-size: 12px;
}

.info-value {
  color: #8B5CF6;
  font-size: 13px;
  font-weight: 600;
}

.form-row {
  margin-bottom: 12px;
}

.form-row label {
  display: block;
  color: #aaa;
  font-size: 12px;
  margin-bottom: 6px;
}

.select-input {
  width: 100%;
  background: #111;
  border: 1px solid #444;
  color: #fff;
  padding: 8px 12px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
}
.select-input:focus {
  outline: none;
  border-color: #8B5CF6;
}
.select-input option {
  background: #1e1e1e;
  color: #fff;
}
.select-input optgroup {
  background: #111;
  color: #888;
  font-style: normal;
}

.curve-preview {
  margin-top: 16px;
  padding: 12px;
  background: #111;
  border: 1px solid #333;
  border-radius: 4px;
}

.curve-svg {
  width: 100%;
  height: 80px;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #333;
}

.btn-cancel, .btn-confirm {
  padding: 8px 16px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
}

.btn-cancel {
  background: #333;
  border: 1px solid #444;
  color: #ccc;
}
.btn-cancel:hover { background: #444; }

.btn-confirm {
  background: #8B5CF6;
  border: none;
  color: #fff;
}
.btn-confirm:hover:not(:disabled) { background: #9D70F9; }
.btn-confirm:disabled { opacity: 0.5; cursor: not-allowed; }
</style>
