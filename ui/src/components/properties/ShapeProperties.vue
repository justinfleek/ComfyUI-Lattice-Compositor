<template>
  <div class="shape-properties">
    <!-- Stroke Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('stroke')">
        <span class="expand-icon">{{ expandedSections.includes('stroke') ? '▼' : '►' }}</span>
        <span class="section-title">Stroke</span>
        <input
          type="checkbox"
          :checked="hasStroke"
          @click.stop
          @change="toggleStroke"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('stroke') && hasStroke" class="section-content">
        <div class="property-row">
          <label>Color</label>
          <div class="color-input-wrapper">
            <input
              type="color"
              :value="shapeData.stroke || '#ffffff'"
              @input="e => update('stroke', (e.target as HTMLInputElement).value)"
            />
          </div>
        </div>

        <div class="property-row">
          <label>Opacity</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Stroke Opacity') ?? shapeData.strokeOpacity ?? 100"
            @update:modelValue="v => updateAnimatable('Stroke Opacity', v, 'strokeOpacity')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Stroke Opacity') }" @click="toggleKeyframe('Stroke Opacity', 'strokeOpacity')">◆</button>
        </div>

        <div class="property-row">
          <label>Width</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Stroke Width') ?? shapeData.strokeWidth ?? 2"
            @update:modelValue="v => updateAnimatable('Stroke Width', v, 'strokeWidth')"
            :min="0"
            :max="500"
            unit="px"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Stroke Width') }" @click="toggleKeyframe('Stroke Width', 'strokeWidth')">◆</button>
        </div>

        <div class="property-row">
          <label>Line Cap</label>
          <div class="icon-toggle-group">
            <button :class="{ active: strokeLineCap === 'butt' }" @click="update('strokeLineCap', 'butt')" title="Butt Cap">┃</button>
            <button :class="{ active: strokeLineCap === 'round' }" @click="update('strokeLineCap', 'round')" title="Round Cap">◯</button>
            <button :class="{ active: strokeLineCap === 'square' }" @click="update('strokeLineCap', 'square')" title="Square Cap">□</button>
          </div>
        </div>

        <div class="property-row">
          <label>Line Join</label>
          <div class="icon-toggle-group">
            <button :class="{ active: strokeLineJoin === 'miter' }" @click="update('strokeLineJoin', 'miter')" title="Miter Join">⟨</button>
            <button :class="{ active: strokeLineJoin === 'round' }" @click="update('strokeLineJoin', 'round')" title="Round Join">◠</button>
            <button :class="{ active: strokeLineJoin === 'bevel' }" @click="update('strokeLineJoin', 'bevel')" title="Bevel Join">∠</button>
          </div>
        </div>

        <div class="property-row">
          <label>Dashes</label>
          <input
            type="text"
            class="dash-input"
            :value="dashArrayString"
            @change="updateDashArray"
            placeholder="e.g. 10, 5"
            title="Comma-separated dash pattern"
          />
        </div>

        <div class="property-row" v-if="hasDashes">
          <label>Dash Offset</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Dash Offset') ?? shapeData.strokeDashOffset ?? 0"
            @update:modelValue="v => updateAnimatable('Dash Offset', v, 'strokeDashOffset')"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Dash Offset') }" @click="toggleKeyframe('Dash Offset', 'strokeDashOffset')">◆</button>
        </div>
      </div>
    </div>

    <!-- Fill Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('fill')">
        <span class="expand-icon">{{ expandedSections.includes('fill') ? '▼' : '►' }}</span>
        <span class="section-title">Fill</span>
        <input
          type="checkbox"
          :checked="hasFill"
          @click.stop
          @change="toggleFill"
          class="section-toggle"
        />
      </div>

      <div v-if="expandedSections.includes('fill') && hasFill" class="section-content">
        <div class="property-row">
          <label>Color</label>
          <div class="color-input-wrapper">
            <input
              type="color"
              :value="shapeData.fill || '#ffffff'"
              @input="e => update('fill', (e.target as HTMLInputElement).value)"
            />
          </div>
        </div>

        <div class="property-row">
          <label>Opacity</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Fill Opacity') ?? shapeData.fillOpacity ?? 100"
            @update:modelValue="v => updateAnimatable('Fill Opacity', v, 'fillOpacity')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Fill Opacity') }" @click="toggleKeyframe('Fill Opacity', 'fillOpacity')">◆</button>
        </div>
      </div>
    </div>

    <!-- Trim Paths Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('trim')">
        <span class="expand-icon">{{ expandedSections.includes('trim') ? '▼' : '►' }}</span>
        <span class="section-title">Trim Paths</span>
      </div>

      <div v-if="expandedSections.includes('trim')" class="section-content">
        <div class="property-row">
          <label>Start</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Trim Start') ?? shapeData.trimStart ?? 0"
            @update:modelValue="v => updateAnimatable('Trim Start', v, 'trimStart')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim Start') }" @click="toggleKeyframe('Trim Start', 'trimStart')">◆</button>
        </div>

        <div class="property-row">
          <label>End</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Trim End') ?? shapeData.trimEnd ?? 100"
            @update:modelValue="v => updateAnimatable('Trim End', v, 'trimEnd')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim End') }" @click="toggleKeyframe('Trim End', 'trimEnd')">◆</button>
        </div>

        <div class="property-row">
          <label>Offset</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Trim Offset') ?? shapeData.trimOffset ?? 0"
            @update:modelValue="v => updateAnimatable('Trim Offset', v, 'trimOffset')"
            :min="-360"
            :max="360"
            unit="°"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim Offset') }" @click="toggleKeyframe('Trim Offset', 'trimOffset')">◆</button>
        </div>
      </div>
    </div>

    <!-- Path Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('path')">
        <span class="expand-icon">{{ expandedSections.includes('path') ? '▼' : '►' }}</span>
        <span class="section-title">Path</span>
      </div>

      <div v-if="expandedSections.includes('path')" class="section-content">
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="shapeData.closed"
              @change="update('closed', ($event.target as HTMLInputElement).checked)"
            />
            Closed Path
          </label>
        </div>

        <div class="property-row info-row">
          <span class="info-label">Points:</span>
          <span class="info-value">{{ shapeData.controlPoints?.length || 0 }}</span>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';
import type { Layer, SplineData, AnimatableProperty } from '@/types/project';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

const expandedSections = ref<string[]>(['stroke', 'fill', 'trim']);

const shapeData = computed<SplineData>(() => {
  return props.layer.data as SplineData || {
    pathData: '',
    controlPoints: [],
    closed: false,
    stroke: '#ffffff',
    strokeWidth: 2,
    strokeOpacity: 100,
    strokeLineCap: 'round',
    strokeLineJoin: 'round',
    fill: '',
    fillOpacity: 100,
    trimStart: 0,
    trimEnd: 100,
    trimOffset: 0,
  };
});

const hasFill = computed(() => !!shapeData.value.fill && shapeData.value.fill !== 'transparent');
const hasStroke = computed(() => !!shapeData.value.stroke && (shapeData.value.strokeWidth ?? 0) > 0);
const strokeLineCap = computed(() => shapeData.value.strokeLineCap || 'round');
const strokeLineJoin = computed(() => shapeData.value.strokeLineJoin || 'round');
const hasDashes = computed(() => (shapeData.value.strokeDashArray?.length ?? 0) > 0);

const dashArrayString = computed(() => {
  return shapeData.value.strokeDashArray?.join(', ') || '';
});

// Toggle section visibility
function toggleSection(section: string) {
  const idx = expandedSections.value.indexOf(section);
  if (idx >= 0) {
    expandedSections.value.splice(idx, 1);
  } else {
    expandedSections.value.push(section);
  }
}

// Update layer data
function update(key: keyof SplineData | string, value: any) {
  store.updateLayer(props.layer.id, {
    data: { ...shapeData.value, [key]: value }
  });
  emit('update');
}

// Toggle fill on/off
function toggleFill(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  update('fill', checked ? '#ffffff' : '');
}

// Toggle stroke on/off
function toggleStroke(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  if (checked) {
    update('stroke', '#ffffff');
    if ((shapeData.value.strokeWidth ?? 0) <= 0) {
      update('strokeWidth', 2);
    }
  } else {
    update('strokeWidth', 0);
  }
}

// Update dash array from string input
function updateDashArray(e: Event) {
  const input = (e.target as HTMLInputElement).value;
  if (!input.trim()) {
    update('strokeDashArray', []);
    return;
  }
  const values = input.split(',').map(v => parseFloat(v.trim())).filter(v => !isNaN(v) && v >= 0);
  update('strokeDashArray', values);
}

// Get animatable property from layer.properties
function getProperty(name: string): AnimatableProperty<number> | undefined {
  return props.layer.properties?.find(p => p.name === name) as AnimatableProperty<number> | undefined;
}

// Get property value (from animated property or direct data)
function getPropertyValue(name: string): number | undefined {
  const prop = getProperty(name);
  return prop?.value;
}

// Check if property is animated (has keyframes)
function isAnimated(name: string): boolean {
  const prop = getProperty(name);
  return prop?.animated ?? false;
}

// Update animatable property
function updateAnimatable(propName: string, value: number, dataKey: string) {
  // Update the data value
  update(dataKey, value);

  // Also update the property in layer.properties if it exists
  const prop = getProperty(propName);
  if (prop) {
    prop.value = value;
  }
}

// Toggle keyframe for a property
function toggleKeyframe(propName: string, dataKey: string) {
  // Ensure property exists in layer.properties
  ensureProperty(propName, dataKey);

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some(k => k.frame === frame);

    if (hasKeyframeAtFrame) {
      // Remove keyframe at current frame
      prop.keyframes = prop.keyframes.filter(k => k.frame !== frame);
      prop.animated = prop.keyframes.length > 0;
    } else {
      // Add keyframe at current frame
      prop.keyframes.push({
        id: `kf_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
        frame,
        value: prop.value,
        easing: 'linear',
      });
      prop.animated = true;
    }
    emit('update');
  }
}

// Ensure a property exists in layer.properties for timeline display
function ensureProperty(propName: string, dataKey: string) {
  if (!props.layer.properties) {
    props.layer.properties = [];
  }

  const existing = props.layer.properties.find(p => p.name === propName);
  if (!existing) {
    const currentValue = (shapeData.value as any)[dataKey] ?? 0;
    props.layer.properties.push({
      id: `prop_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`,
      name: propName,
      type: 'number',
      value: currentValue,
      animated: false,
      keyframes: [],
      group: propName.includes('Trim') ? 'Trim Paths' : propName.includes('Stroke') ? 'Stroke' : propName.includes('Fill') ? 'Fill' : 'Shape',
    } as AnimatableProperty<number>);
  }
}
</script>

<style scoped>
.shape-properties {
  padding: 0;
}

.prop-section {
  border-bottom: 1px solid #2a2a2a;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 10px;
  cursor: pointer;
  user-select: none;
  background: #252525;
}

.section-header:hover {
  background: #2a2a2a;
}

.expand-icon {
  width: 10px;
  font-size: 11px;
  color: #666;
}

.section-title {
  flex: 1;
  font-weight: 600;
  font-size: 13px;
  color: #ccc;
}

.section-toggle {
  margin: 0;
  cursor: pointer;
}

.section-content {
  padding: 8px 10px;
  background: #1e1e1e;
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  min-height: 24px;
}

.property-row label {
  width: 70px;
  color: #888;
  font-size: 12px;
  flex-shrink: 0;
}

.property-row > :not(label):not(.keyframe-btn) {
  flex: 1;
}

.color-input-wrapper {
  display: flex;
  align-items: center;
}

.color-input-wrapper input[type="color"] {
  width: 60px;
  height: 24px;
  border: 1px solid #444;
  border-radius: 3px;
  padding: 0;
  cursor: pointer;
}

.icon-toggle-group {
  display: flex;
  background: #111;
  border-radius: 3px;
  border: 1px solid #333;
}

.icon-toggle-group button {
  background: transparent;
  border: none;
  color: #666;
  padding: 4px 8px;
  cursor: pointer;
  font-size: 13px;
  border-right: 1px solid #333;
}

.icon-toggle-group button:last-child {
  border-right: none;
}

.icon-toggle-group button.active {
  background: #4a90d9;
  color: #fff;
}

.icon-toggle-group button:hover:not(.active) {
  background: #333;
}

.dash-input {
  flex: 1;
  padding: 4px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  border-radius: 3px;
  color: #e0e0e0;
  font-size: 13px;
}

.dash-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.keyframe-btn {
  width: 18px;
  height: 18px;
  padding: 0;
  border: none;
  background: transparent;
  color: #444;
  cursor: pointer;
  font-size: 12px;
  border-radius: 2px;
  flex-shrink: 0;
}

.keyframe-btn:hover {
  color: #888;
}

.keyframe-btn.active {
  color: #f0c040;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  cursor: pointer;
  width: auto;
  color: #ccc;
  font-size: 13px;
}

.checkbox-row input[type="checkbox"] {
  margin: 0;
}

.info-row {
  color: #666;
  font-size: 12px;
}

.info-label {
  margin-right: 4px;
}

.info-value {
  color: #999;
}
</style>
