<template>
  <div class="shape-editor">
    <div class="property-row">
      <label>Copies</label>
      <ScrubableNumber
        :modelValue="operator.copies.value"
        @update:modelValue="v => updateNumber('copies', v)"
        :min="1"
        :max="100"
        :step="1"
      />
      <KeyframeToggle :property="operator.copies" @toggle="toggleKeyframe('copies')" />
    </div>
    <div class="property-row">
      <label>Offset</label>
      <ScrubableNumber
        :modelValue="operator.offset.value"
        @update:modelValue="v => updateNumber('offset', v)"
        :min="-10"
        :max="10"
        :step="0.1"
      />
      <KeyframeToggle :property="operator.offset" @toggle="toggleKeyframe('offset')" />
    </div>
    <div class="property-row">
      <label>Composite</label>
      <select :value="operator.composite" @change="updateComposite">
        <option value="below">Below</option>
        <option value="above">Above</option>
      </select>
    </div>

    <div class="subsection-header">Transform</div>

    <div class="property-row">
      <label>Position</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="operator.transform.position.value.x"
          @update:modelValue="v => updateTransformPoint('position', 'x', v)"
          unit="px"
        />
        <ScrubableNumber
          :modelValue="operator.transform.position.value.y"
          @update:modelValue="v => updateTransformPoint('position', 'y', v)"
          unit="px"
        />
      </div>
      <KeyframeToggle :property="operator.transform.position" @toggle="toggleTransformKeyframe('position')" />
    </div>
    <div class="property-row">
      <label>Scale</label>
      <div class="xy-inputs">
        <ScrubableNumber
          :modelValue="operator.transform.scale.value.x"
          @update:modelValue="v => updateTransformPoint('scale', 'x', v)"
          :min="0"
          :max="500"
          unit="%"
        />
        <ScrubableNumber
          :modelValue="operator.transform.scale.value.y"
          @update:modelValue="v => updateTransformPoint('scale', 'y', v)"
          :min="0"
          :max="500"
          unit="%"
        />
      </div>
      <KeyframeToggle :property="operator.transform.scale" @toggle="toggleTransformKeyframe('scale')" />
    </div>
    <div class="property-row">
      <label>Rotation</label>
      <ScrubableNumber
        :modelValue="operator.transform.rotation.value"
        @update:modelValue="v => updateTransformNumber('rotation', v)"
        unit="°"
      />
      <KeyframeToggle :property="operator.transform.rotation" @toggle="toggleTransformKeyframe('rotation')" />
    </div>
    <div class="property-row">
      <label>Start Opacity</label>
      <ScrubableNumber
        :modelValue="operator.transform.startOpacity.value"
        @update:modelValue="v => updateTransformNumber('startOpacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.transform.startOpacity" @toggle="toggleTransformKeyframe('startOpacity')" />
    </div>
    <div class="property-row">
      <label>End Opacity</label>
      <ScrubableNumber
        :modelValue="operator.transform.endOpacity.value"
        @update:modelValue="v => updateTransformNumber('endOpacity', v)"
        :min="0"
        :max="100"
        unit="%"
      />
      <KeyframeToggle :property="operator.transform.endOpacity" @toggle="toggleTransformKeyframe('endOpacity')" />
    </div>
  </div>
</template>

<script setup lang="ts">
import type { RepeaterOperator, RepeaterComposite, Point2D } from '@/types/shapes';
import { ScrubableNumber } from '@/components/controls';
import KeyframeToggle from '../KeyframeToggle.vue';
import { useCompositorStore } from '@/stores/compositorStore';

const props = defineProps<{ operator: RepeaterOperator }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

function updateNumber(prop: 'copies' | 'offset', value: number) {
  const updated = { ...props.operator };
  updated[prop] = { ...updated[prop], value };
  emit('update', updated);
}

function updateComposite(e: Event) {
  const updated = { ...props.operator };
  updated.composite = (e.target as HTMLSelectElement).value as RepeaterComposite;
  emit('update', updated);
}

function updateTransformPoint(prop: 'position' | 'scale' | 'anchorPoint', axis: 'x' | 'y', value: number) {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  updated.transform[prop] = {
    ...updated.transform[prop],
    value: { ...updated.transform[prop].value, [axis]: value }
  };
  emit('update', updated);
}

function updateTransformNumber(prop: 'rotation' | 'startOpacity' | 'endOpacity', value: number) {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  updated.transform[prop] = { ...updated.transform[prop], value };
  emit('update', updated);
}

function toggleKeyframe(prop: 'copies' | 'offset') {
  const updated = { ...props.operator };
  const animProp = updated[prop];
  const frame = store.currentFrame;

  const hasKf = animProp.keyframes.some(k => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame);
  } else {
    animProp.keyframes.push({
      id: `kf_${Date.now()}`,
      frame,
      value: animProp.value,
      easing: 'linear'
    });
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit('update', updated);
}

function toggleTransformKeyframe(prop: 'position' | 'scale' | 'anchorPoint' | 'rotation' | 'startOpacity' | 'endOpacity') {
  const updated = { ...props.operator };
  updated.transform = { ...updated.transform };
  const animProp = updated.transform[prop];
  const frame = store.currentFrame;

  const hasKf = animProp.keyframes.some(k => k.frame === frame);
  if (hasKf) {
    animProp.keyframes = animProp.keyframes.filter(k => k.frame !== frame);
  } else {
    animProp.keyframes.push({
      id: `kf_${Date.now()}`,
      frame,
      value: animProp.value,
      easing: 'linear'
    });
  }
  animProp.animated = animProp.keyframes.length > 0;
  emit('update', updated);
}
</script>

<style scoped>
.shape-editor {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
}

.property-row label {
  width: 80px;
  color: var(--weyl-text-muted, #888);
  font-size: 11px;
  flex-shrink: 0;
}

.property-row select {
  flex: 1;
  padding: 3px 6px;
  background: var(--weyl-surface-0, #0a0a0a);
  border: 1px solid var(--weyl-border-default, #333);
  border-radius: 3px;
  color: var(--weyl-text-primary, #e0e0e0);
  font-size: 11px;
}

.xy-inputs {
  display: flex;
  gap: 4px;
  flex: 1;
}

.xy-inputs > * {
  flex: 1;
}

.subsection-header {
  font-size: 10px;
  font-weight: 600;
  color: var(--weyl-text-muted, #666);
  text-transform: uppercase;
  letter-spacing: 0.05em;
  margin-top: 6px;
  padding-bottom: 4px;
  border-bottom: 1px solid var(--weyl-border-subtle, #2a2a2a);
}
</style>
