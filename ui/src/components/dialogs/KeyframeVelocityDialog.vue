<!--
  @component KeyframeVelocityDialog
  @description Dialog for setting precise keyframe velocity and influence values.

  Allows setting:
  - Incoming velocity (speed entering the keyframe)
  - Outgoing velocity (speed leaving the keyframe)
  - Incoming influence (percentage of segment for ease-in)
  - Outgoing influence (percentage of segment for ease-out)
-->
<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="$emit('close')">
      <div class="dialog-box">
        <div class="dialog-header">
          <h3>Keyframe Velocity</h3>
          <button class="close-btn" @click="$emit('close')">&times;</button>
        </div>
        <div class="dialog-body">
          <!-- Selected keyframes info -->
          <div class="info-row">
            <span class="info-label">Selected Keyframes:</span>
            <span class="info-value">{{ keyframeCount }}</span>
          </div>

          <!-- Incoming section -->
          <div class="velocity-section">
            <div class="section-header">Incoming</div>

            <div class="form-row">
              <label>Velocity</label>
              <div class="input-group">
                <input
                  type="number"
                  v-model.number="incomingVelocity"
                  class="number-input"
                  step="0.1"
                  :placeholder="'0'"
                />
                <span class="input-unit">{{ velocityUnit }}</span>
              </div>
            </div>

            <div class="form-row">
              <label>Influence</label>
              <div class="input-group">
                <input
                  type="number"
                  v-model.number="incomingInfluence"
                  class="number-input"
                  min="0"
                  max="100"
                  step="1"
                />
                <span class="input-unit">%</span>
              </div>
              <input
                type="range"
                v-model.number="incomingInfluence"
                min="0"
                max="100"
                class="slider"
              />
            </div>
          </div>

          <!-- Outgoing section -->
          <div class="velocity-section">
            <div class="section-header">Outgoing</div>

            <div class="form-row">
              <label>Velocity</label>
              <div class="input-group">
                <input
                  type="number"
                  v-model.number="outgoingVelocity"
                  class="number-input"
                  step="0.1"
                  :placeholder="'0'"
                />
                <span class="input-unit">{{ velocityUnit }}</span>
              </div>
            </div>

            <div class="form-row">
              <label>Influence</label>
              <div class="input-group">
                <input
                  type="number"
                  v-model.number="outgoingInfluence"
                  class="number-input"
                  min="0"
                  max="100"
                  step="1"
                />
                <span class="input-unit">%</span>
              </div>
              <input
                type="range"
                v-model.number="outgoingInfluence"
                min="0"
                max="100"
                class="slider"
              />
            </div>
          </div>

          <!-- Link velocities toggle -->
          <div class="form-row checkbox-row">
            <label class="checkbox-label">
              <input type="checkbox" v-model="linkVelocities" />
              <span>Link incoming and outgoing velocities</span>
            </label>
          </div>

          <!-- Velocity preview visualization -->
          <div class="velocity-preview">
            <svg viewBox="0 0 200 80" class="velocity-svg">
              <!-- Background grid -->
              <line x1="0" y1="40" x2="200" y2="40" stroke="#333" stroke-width="0.5" />
              <line x1="100" y1="0" x2="100" y2="80" stroke="#333" stroke-width="0.5" />

              <!-- Incoming curve -->
              <path
                :d="incomingCurvePath"
                fill="none"
                stroke="#4CAF50"
                stroke-width="2"
              />

              <!-- Outgoing curve -->
              <path
                :d="outgoingCurvePath"
                fill="none"
                stroke="#2196F3"
                stroke-width="2"
              />

              <!-- Keyframe point -->
              <circle cx="100" cy="40" r="5" fill="#8B5CF6" />

              <!-- Labels -->
              <text x="30" y="75" fill="#4CAF50" font-size="10">In</text>
              <text x="160" y="75" fill="#2196F3" font-size="10">Out</text>
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
import { computed, ref, watch } from "vue";

const props = defineProps<{
  visible: boolean;
  keyframeCount: number;
  propertyType?: string; // 'position', 'rotation', 'opacity', etc.
  initialInVelocity?: number;
  initialOutVelocity?: number;
  initialInInfluence?: number;
  initialOutInfluence?: number;
}>();

const emit = defineEmits<{
  close: [];
  confirm: [
    settings: {
      incomingVelocity: number;
      outgoingVelocity: number;
      incomingInfluence: number;
      outgoingInfluence: number;
    },
  ];
}>();

// Form state
const incomingVelocity = ref(0);
const outgoingVelocity = ref(0);
const incomingInfluence = ref(33.33);
const outgoingInfluence = ref(33.33);
const linkVelocities = ref(false);

// Determine unit based on property type
const velocityUnit = computed(() => {
  const type = props.propertyType?.toLowerCase() || "";
  if (type.includes("rotation") || type.includes("angle")) {
    return "deg/sec";
  }
  if (type.includes("opacity") || type.includes("scale")) {
    return "%/sec";
  }
  return "px/sec";
});

// Link velocities when checkbox is enabled
watch(incomingVelocity, (newVal) => {
  if (linkVelocities.value) {
    outgoingVelocity.value = newVal;
  }
});

watch(outgoingVelocity, (newVal) => {
  if (linkVelocities.value) {
    incomingVelocity.value = newVal;
  }
});

// Reset to initial values when dialog opens
watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      incomingVelocity.value = props.initialInVelocity ?? 0;
      outgoingVelocity.value = props.initialOutVelocity ?? 0;
      incomingInfluence.value = props.initialInInfluence ?? 33.33;
      outgoingInfluence.value = props.initialOutInfluence ?? 33.33;
      linkVelocities.value = false;
    }
  },
);

// Generate SVG path for incoming velocity curve
const incomingCurvePath = computed(() => {
  const influence = incomingInfluence.value / 100;
  const velocity = Math.min(Math.max(incomingVelocity.value / 100, -1), 1);

  // Control points for bezier
  const x1 = 0;
  const y1 = 60;
  const cpX = 100 - influence * 100;
  const cpY = 40 + velocity * 20;
  const x2 = 100;
  const y2 = 40;

  return `M ${x1} ${y1} Q ${cpX} ${cpY} ${x2} ${y2}`;
});

// Generate SVG path for outgoing velocity curve
const outgoingCurvePath = computed(() => {
  const influence = outgoingInfluence.value / 100;
  const velocity = Math.min(Math.max(outgoingVelocity.value / 100, -1), 1);

  // Control points for bezier
  const x1 = 100;
  const y1 = 40;
  const cpX = 100 + influence * 100;
  const cpY = 40 - velocity * 20;
  const x2 = 200;
  const y2 = 20;

  return `M ${x1} ${y1} Q ${cpX} ${cpY} ${x2} ${y2}`;
});

function confirm() {
  emit("confirm", {
    incomingVelocity: incomingVelocity.value,
    outgoingVelocity: outgoingVelocity.value,
    incomingInfluence: incomingInfluence.value,
    outgoingInfluence: outgoingInfluence.value,
  });
  emit("close");
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

.velocity-section {
  margin-bottom: 16px;
  padding: 12px;
  background: #151515;
  border-radius: 6px;
  border: 1px solid #2a2a2a;
}

.section-header {
  font-size: 12px;
  font-weight: 600;
  color: #888;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: 12px;
}

.form-row {
  margin-bottom: 10px;
}

.form-row label {
  display: block;
  color: #aaa;
  font-size: 12px;
  margin-bottom: 6px;
}

.input-group {
  display: flex;
  align-items: center;
  gap: 8px;
}

.number-input {
  flex: 1;
  background: #111;
  border: 1px solid #444;
  color: #fff;
  padding: 8px 12px;
  border-radius: 4px;
  font-size: 13px;
  text-align: right;
}
.number-input:focus {
  outline: none;
  border-color: #8B5CF6;
}
.number-input::placeholder {
  color: #555;
}

.input-unit {
  color: #666;
  font-size: 12px;
  min-width: 50px;
}

.slider {
  width: 100%;
  margin-top: 8px;
  height: 4px;
  -webkit-appearance: none;
  appearance: none;
  background: #333;
  border-radius: 2px;
  cursor: pointer;
}
.slider::-webkit-slider-thumb {
  -webkit-appearance: none;
  appearance: none;
  width: 14px;
  height: 14px;
  background: #8B5CF6;
  border-radius: 50%;
  cursor: pointer;
}
.slider::-moz-range-thumb {
  width: 14px;
  height: 14px;
  background: #8B5CF6;
  border-radius: 50%;
  cursor: pointer;
  border: none;
}

.checkbox-row {
  margin: 16px 0;
}

.checkbox-label {
  display: flex;
  align-items: center;
  gap: 8px;
  color: #aaa;
  font-size: 13px;
  cursor: pointer;
}

.checkbox-label input[type="checkbox"] {
  width: 16px;
  height: 16px;
  accent-color: #8B5CF6;
}

.velocity-preview {
  margin-top: 16px;
  padding: 12px;
  background: #111;
  border: 1px solid #333;
  border-radius: 4px;
}

.velocity-svg {
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
