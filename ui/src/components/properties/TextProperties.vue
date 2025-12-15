<template>
  <div class="text-properties">
    <div class="property-group">
      <label>Source Text</label>
      <textarea
        v-model="textData.text"
        class="main-text-input"
        rows="3"
        @input="e => updateData('text', (e.target as HTMLTextAreaElement).value)"
      ></textarea>
    </div>

    <div class="property-group">
       <div class="row">
          <div class="col">
             <label>Fill Color</label>
             <ColorPicker :modelValue="textData.fill" @update:modelValue="v => updateData('fill', v)" />
          </div>
          <div class="col">
             <label>Stroke Color</label>
             <ColorPicker :modelValue="textData.stroke" @update:modelValue="v => updateData('stroke', v)" />
          </div>
       </div>
    </div>

    <div class="property-group">
       <div class="row">
          <label>Tracking</label>
          <ScrubableNumber :modelValue="textData.tracking" @update:modelValue="v => updateAnimatable('Tracking', v)" />
          <KeyframeToggle :property="getProperty('Tracking')" :layerId="layer.id" />
       </div>
       <div class="row">
          <label>Line Spacing</label>
          <ScrubableNumber :modelValue="textData.lineSpacing" @update:modelValue="v => updateAnimatable('Line Spacing', v)" />
          <KeyframeToggle :property="getProperty('Line Spacing')" :layerId="layer.id" />
       </div>
    </div>

    <div class="property-group checkbox">
       <label>
         <input type="checkbox" v-model="textData.perCharacter3D" @change="emit('update')" />
         Enable Per-Character 3D
       </label>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber, ColorPicker } from '@/components/controls';
import KeyframeToggle from './KeyframeToggle.vue';

const props = defineProps(['layer']);
const emit = defineEmits(['update']);
const store = useCompositorStore();

const textData = computed(() => props.layer.data);

function getProperty(name: string) {
    return props.layer.properties.find((p: any) => p.name === name);
}

function updateData(key: string, val: any) {
    textData.value[key] = val;
    // Sync to animatable property if it exists
    const propName = key === 'fill' ? 'Fill Color' : key === 'stroke' ? 'Stroke Color' : 'Source Text';
    const prop = getProperty(propName);
    if(prop) prop.value = val;

    emit('update');
}

function updateAnimatable(name: string, val: number) {
    const prop = getProperty(name);
    if (prop) {
        prop.value = val;
        // Also update static data for immediate render if needed
        const key = name.charAt(0).toLowerCase() + name.slice(1).replace(' ', '');
        if (textData.value[key] !== undefined) textData.value[key] = val;
        store.project.meta.modified = new Date().toISOString();
    }
}
</script>

<style scoped>
.text-properties { padding: 10px; font-size: 13px; color: #ccc; }
.property-group { margin-bottom: 15px; border-bottom: 1px solid #333; padding-bottom: 10px; }
.main-text-input { width: 100%; background: #111; color: #fff; border: 1px solid #444; padding: 8px; font-size: 14px; margin-top: 5px; }
.row { display: flex; align-items: center; gap: 10px; margin-bottom: 8px; justify-content: space-between; }
.col { flex: 1; }
label { display: block; color: #888; margin-bottom: 4px; font-size: 12px; }
.checkbox label { display: flex; align-items: center; gap: 8px; cursor: pointer; color: #eee; }
</style>
