<template>
  <Teleport to="body">
    <div class="expression-overlay" v-if="visible" @click.self="$emit('close')">
      <div class="expression-input">
        <div class="expression-header">
      <span class="expression-icon">fx</span>
      <span class="expression-title">Expression</span>
      <button class="close-btn" @click="$emit('close')">&times;</button>
    </div>

    <div class="expression-body">
      <!-- Mode toggle -->
      <div class="mode-toggle">
        <button
          :class="{ active: mode === 'preset' }"
          @click="mode = 'preset'"
        >Preset</button>
        <button
          :class="{ active: mode === 'data' }"
          @click="mode = 'data'"
          :disabled="availableDataAssets.length === 0"
          :title="availableDataAssets.length === 0 ? 'Import data files in Project panel first' : 'Drive property from data file'"
        >Data</button>
        <button
          :class="{ active: mode === 'custom' }"
          @click="mode = 'custom'"
        >Custom</button>
      </div>

      <!-- Preset mode -->
      <div v-if="mode === 'preset'" class="preset-section">
        <label>Expression Type</label>
        <select v-model="selectedPreset" class="preset-select">
          <option value="">Select expression...</option>
          <optgroup label="Motion">
            <option value="inertiaLight">Inertia (Light)</option>
            <option value="inertiaHeavy">Inertia (Heavy)</option>
            <option value="bounceGentle">Bounce (Gentle)</option>
            <option value="bounceFirm">Bounce (Firm)</option>
            <option value="elasticSnappy">Elastic (Snappy)</option>
            <option value="elasticLoose">Elastic (Loose)</option>
          </optgroup>
          <optgroup label="Jitter/Wiggle">
            <option value="jitterSubtle">Jitter (Subtle)</option>
            <option value="jitterModerate">Jitter (Moderate)</option>
            <option value="jitterIntense">Jitter (Intense)</option>
          </optgroup>
          <optgroup label="Loop">
            <option value="repeatCycle">Loop (Cycle)</option>
            <option value="repeatPingpong">Loop (Ping-Pong)</option>
            <option value="repeatOffset">Loop (Offset)</option>
          </optgroup>
        </select>

        <!-- Preset description -->
        <p v-if="presetDescription" class="preset-description">
          {{ presetDescription }}
        </p>
      </div>

      <!-- Data mode -->
      <div v-if="mode === 'data'" class="data-section">
        <label>Data File</label>
        <select v-model="selectedDataAsset" class="data-select">
          <option value="">Select data file...</option>
          <option v-for="asset in availableDataAssets" :key="asset.name" :value="asset.name">
            {{ asset.name }} ({{ asset.type.toUpperCase() }})
          </option>
        </select>

        <!-- CSV/TSV specific options -->
        <template v-if="isCSVType && selectedDataAsset">
          <label>Column</label>
          <select v-model="selectedColumn" class="data-select">
            <option value="">Select column...</option>
            <option v-for="(header, idx) in csvHeaders" :key="idx" :value="header">
              {{ header }} (col {{ idx }})
            </option>
          </select>

          <label>Row Mapping</label>
          <select v-model="rowMappingMode" class="data-select">
            <option value="frame">Frame number (row = frame)</option>
            <option value="time">Time in seconds (row = round(time))</option>
            <option value="manual">Manual offset</option>
          </select>

          <template v-if="rowMappingMode === 'manual'">
            <label>Row Offset</label>
            <input
              type="number"
              v-model.number="manualRowOffset"
              class="offset-input"
              placeholder="0"
            />
          </template>
        </template>

        <!-- JSON specific options -->
        <template v-if="isJSONType && selectedDataAsset">
          <label>Property Path</label>
          <input
            type="text"
            v-model="jsonPropertyPath"
            class="path-input"
            placeholder="e.g., data[0].value or path.to.property"
          />
          <p class="hint">
            Use dot notation to access nested properties. Use [n] for arrays.
          </p>
        </template>

        <!-- Preview generated expression -->
        <template v-if="generatedDataExpression">
          <label>Generated Expression</label>
          <code class="generated-expression">{{ generatedDataExpression }}</code>
        </template>
      </div>

      <!-- Custom mode -->
      <div v-if="mode === 'custom'" class="custom-section">
        <label>Expression Code</label>
        <textarea
          v-model="customExpression"
          class="expression-textarea"
          :class="{ 'has-error': expressionError }"
          placeholder="wiggle(2, 10)"
          rows="3"
          @keydown.enter.ctrl="apply"
        />
        <p v-if="expressionError" class="expression-error">
          {{ expressionError }}
        </p>
        <p v-else class="hint">
          Available: wiggle(freq, amp), loopOut('cycle'), time, value, thisLayer.effect("name")("param")
        </p>
      </div>
    </div>

    <div class="expression-footer">
      <button class="btn-remove" v-if="hasExpression" @click="remove">
        Remove
      </button>
      <div class="spacer"></div>
      <button class="btn-cancel" @click="$emit('close')">Cancel</button>
      <button
        class="btn-apply"
        @click="apply"
        :disabled="!canApply"
      >Apply</button>
      </div>
    </div>
  </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, ref, watch } from "vue";
import { EXPRESSION_PRESETS, validateExpression } from "@/services/expressions";
import { useCompositorStore } from "@/stores/compositorStore";
import type { PropertyExpression } from "@/types/project";

interface Props {
  visible: boolean;
  currentExpression?: PropertyExpression | null;
}

const props = defineProps<Props>();
const store = useCompositorStore();

const emit = defineEmits<{
  (e: "close"): void;
  (e: "apply", expression: PropertyExpression): void;
  (e: "remove"): void;
}>();

const mode = ref<"preset" | "custom" | "data">("preset");
const selectedPreset = ref<string>("");
const customExpression = ref<string>("");
const expressionError = ref<string | null>(null);

// Data-driven mode state
const selectedDataAsset = ref<string>("");
const selectedColumn = ref<string>("");
const jsonPropertyPath = ref<string>("");
const rowMappingMode = ref<"frame" | "time" | "manual">("frame");
const manualRowOffset = ref(0);

// Get available data assets from project
const availableDataAssets = computed(() => {
  const assets = store.project?.dataAssets ?? {};
  return Object.entries(assets).map(([name, asset]) => ({
    name,
    type: asset.type,
    headers: asset.headers,
    numRows: asset.numRows,
    numColumns: asset.numColumns,
  }));
});

// Get the selected data asset details
const selectedAssetDetails = computed(() => {
  const name = selectedDataAsset.value;
  if (!name) return null;
  const asset = store.project?.dataAssets?.[name];
  return asset || null;
});

// Is selected asset CSV/TSV?
const isCSVType = computed(() => {
  const asset = selectedAssetDetails.value;
  return asset && (asset.type === "csv" || asset.type === "tsv");
});

// Is selected asset JSON?
const isJSONType = computed(() => {
  const asset = selectedAssetDetails.value;
  return asset && (asset.type === "json" || asset.type === "mgjson");
});

// CSV headers for column dropdown
const csvHeaders = computed(() => {
  const asset = selectedAssetDetails.value;
  return asset?.headers ?? [];
});

// Generate expression code from data selection
const generatedDataExpression = computed(() => {
  if (!selectedDataAsset.value) return "";

  const assetName = JSON.stringify(selectedDataAsset.value);

  if (isCSVType.value) {
    // CSV: footage("file.csv").dataValue([row, column])
    const column = selectedColumn.value || "0";
    const columnRef = /^\d+$/.test(column) ? column : JSON.stringify(column);

    let rowExpr = "frame";
    if (rowMappingMode.value === "time") {
      rowExpr = "Math.round(time)";
    } else if (rowMappingMode.value === "manual") {
      rowExpr = `frame + ${manualRowOffset.value}`;
    }

    return `footage(${assetName}).dataValue([${rowExpr}, ${columnRef}])`;
  } else if (isJSONType.value) {
    // JSON: footage("file.json").sourceData.path
    const path = jsonPropertyPath.value || "";
    if (path) {
      return `footage(${assetName}).sourceData.${path}`;
    }
    return `footage(${assetName}).sourceData`;
  }

  return "";
});

// Check if property already has an expression
const hasExpression = computed(() => {
  return props.currentExpression?.enabled ?? false;
});

// Preset descriptions
const presetDescriptions: Record<string, string> = {
  inertiaLight: "Adds subtle overshoot after keyframes end",
  inertiaHeavy: "Adds noticeable overshoot with slower settle",
  bounceGentle: "Soft bouncing at the end of motion",
  bounceFirm: "Quick bouncing with higher energy",
  elasticSnappy: "Snappy spring-like motion",
  elasticLoose: "Loose, wobbly spring motion",
  jitterSubtle: "Subtle random movement (noise)",
  jitterModerate: "Moderate random movement",
  jitterIntense: "Strong random movement",
  repeatCycle: "Loop keyframes from start",
  repeatPingpong: "Loop keyframes back and forth",
  repeatOffset: "Loop with continuous offset",
};

const presetDescription = computed(() => {
  return presetDescriptions[selectedPreset.value] || "";
});

// Validate custom expression when it changes
watch(customExpression, (code) => {
  if (mode.value === "custom" && code.trim()) {
    const result = validateExpression(code);
    expressionError.value = result.valid
      ? null
      : result.error || "Invalid expression";
  } else {
    expressionError.value = null;
  }
});

// Can apply if preset selected, custom expression entered without errors, or data configured
const canApply = computed(() => {
  if (mode.value === "preset") {
    return selectedPreset.value !== "";
  } else if (mode.value === "data") {
    if (!selectedDataAsset.value) return false;
    if (isCSVType.value && !selectedColumn.value) return false;
    return true;
  }
  // Custom mode: must have content and no errors
  return customExpression.value.trim() !== "" && !expressionError.value;
});

// Initialize from current expression when dialog opens
watch(
  () => props.visible,
  (visible) => {
    if (visible && props.currentExpression) {
      // Check if it's a data-driven expression by checking params
      const params = props.currentExpression.params as any;
      if (params?.dataAsset) {
        // Restore data-driven state
        mode.value = "data";
        selectedDataAsset.value = params.dataAsset || "";
        selectedColumn.value = params.column || "";
        jsonPropertyPath.value = params.jsonPath || "";
        rowMappingMode.value = params.rowMapping || "frame";
        manualRowOffset.value = params.rowOffset || 0;
      } else if (props.currentExpression.type === "preset") {
        mode.value = "preset";
        // Find matching preset
        const presetKey = Object.keys(EXPRESSION_PRESETS).find((key) => {
          const preset = EXPRESSION_PRESETS[key];
          return preset.name === props.currentExpression?.name;
        });
        selectedPreset.value = presetKey || "";
      } else {
        mode.value = "custom";
        customExpression.value = props.currentExpression.name || "";
      }
    } else if (visible) {
      // Reset all state
      mode.value = "preset";
      selectedPreset.value = "";
      customExpression.value = "";
      selectedDataAsset.value = "";
      selectedColumn.value = "";
      jsonPropertyPath.value = "";
      rowMappingMode.value = "frame";
      manualRowOffset.value = 0;
    }
  },
);

function apply() {
  if (!canApply.value) return;

  let expression: PropertyExpression;

  if (mode.value === "preset") {
    const preset = EXPRESSION_PRESETS[selectedPreset.value];
    if (preset) {
      expression = {
        enabled: true,
        type: "preset",
        name: preset.name,
        params: { ...preset.params },
      };
    } else {
      return;
    }
  } else if (mode.value === "data") {
    // Data-driven expression - generate the footage() code
    expression = {
      enabled: true,
      type: "custom", // Treat as custom expression
      name: generatedDataExpression.value,
      params: {
        // Store metadata for potential re-editing
        dataAsset: selectedDataAsset.value,
        column: selectedColumn.value,
        jsonPath: jsonPropertyPath.value,
        rowMapping: rowMappingMode.value,
        rowOffset: manualRowOffset.value,
      },
    };
  } else {
    expression = {
      enabled: true,
      type: "custom",
      name: customExpression.value.trim(),
      params: {},
    };
  }

  emit("apply", expression);
  emit("close");
}

function remove() {
  emit("remove");
  emit("close");
}
</script>

<style scoped>
.expression-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.5);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.expression-input {
  background: #1e1e1e;
  border: 1px solid #333;
  border-radius: 6px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
  width: 280px;
  overflow: hidden;
}

.expression-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  background: linear-gradient(135deg, rgba(139, 92, 246, 0.2), rgba(236, 72, 153, 0.2));
  border-bottom: 1px solid #333;
}

.expression-icon {
  font-size: 12px;
  font-weight: bold;
  color: #EC4899;
  font-style: italic;
}

.expression-title {
  flex: 1;
  font-size: 13px;
  font-weight: 600;
  color: #e5e5e5;
}

.close-btn {
  background: transparent;
  border: none;
  color: #888;
  font-size: 16px;
  cursor: pointer;
  padding: 0;
}
.close-btn:hover { color: #fff; }

.expression-body {
  padding: 12px;
}

.mode-toggle {
  display: flex;
  gap: 4px;
  margin-bottom: 12px;
}

.mode-toggle button {
  flex: 1;
  padding: 6px 12px;
  border: 1px solid #444;
  background: #111;
  color: #888;
  font-size: 12px;
  cursor: pointer;
  border-radius: 4px;
  transition: all 0.15s;
}

.mode-toggle button:hover {
  background: #222;
  color: #aaa;
}

.mode-toggle button.active {
  background: var(--lattice-accent, #8B5CF6);
  border-color: var(--lattice-accent, #8B5CF6);
  color: #fff;
}

label {
  display: block;
  font-size: 11px;
  color: #888;
  margin-bottom: 4px;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.preset-select {
  width: 100%;
  padding: 8px;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e5e5e5;
  font-size: 13px;
  cursor: pointer;
}

.preset-select:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.preset-select option {
  background: #1e1e1e;
}

.preset-select optgroup {
  color: #888;
  font-style: normal;
}

.preset-description {
  margin: 8px 0 0;
  font-size: 11px;
  color: #888;
  font-style: italic;
}

.expression-textarea {
  width: 100%;
  padding: 8px;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e5e5e5;
  font-size: 12px;
  font-family: 'Fira Code', 'Consolas', monospace;
  resize: vertical;
  min-height: 60px;
}

.expression-textarea:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.hint {
  margin: 6px 0 0;
  font-size: 10px;
  color: #666;
}

.expression-textarea.has-error {
  border-color: #EF4444;
}

.expression-error {
  margin: 6px 0 0;
  font-size: 11px;
  color: #EF4444;
  background: rgba(239, 68, 68, 0.1);
  padding: 6px 8px;
  border-radius: 4px;
  border-left: 2px solid #EF4444;
}

/* Data section styles */
.data-section {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.data-select {
  width: 100%;
  padding: 8px;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e5e5e5;
  font-size: 13px;
  cursor: pointer;
}

.data-select:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.data-select option {
  background: #1e1e1e;
}

.path-input,
.offset-input {
  width: 100%;
  padding: 8px;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  color: #e5e5e5;
  font-size: 12px;
  font-family: 'Fira Code', 'Consolas', monospace;
}

.path-input:focus,
.offset-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8B5CF6);
}

.offset-input {
  width: 80px;
}

.generated-expression {
  display: block;
  padding: 8px;
  background: #111;
  border: 1px solid #444;
  border-radius: 4px;
  color: #10B981;
  font-size: 11px;
  font-family: 'Fira Code', 'Consolas', monospace;
  word-break: break-all;
}

.mode-toggle button:disabled {
  opacity: 0.4;
  cursor: not-allowed;
}

.expression-footer {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  border-top: 1px solid #333;
  background: #151515;
}

.spacer { flex: 1; }

.btn-remove, .btn-cancel, .btn-apply {
  padding: 6px 12px;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.btn-remove {
  background: transparent;
  border: 1px solid #EF4444;
  color: #EF4444;
}
.btn-remove:hover {
  background: rgba(239, 68, 68, 0.1);
}

.btn-cancel {
  background: #333;
  border: 1px solid #444;
  color: #ccc;
}
.btn-cancel:hover { background: #444; }

.btn-apply {
  background: var(--lattice-accent, #8B5CF6);
  border: none;
  color: #fff;
}
.btn-apply:hover:not(:disabled) {
  background: var(--lattice-accent-hover, #9D70F9);
}
.btn-apply:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}
</style>
