<template>
  <div class="text-properties">
    <div class="prop-section">
      <div class="section-title">Source Text</div>
      <textarea
        :value="textData.text"
        @input="e => updateText((e.target as HTMLTextAreaElement).value)"
        class="text-area"
        rows="3"
      ></textarea>
    </div>

    <div class="prop-section">
      <div class="section-title">Character</div>
      <div class="row font-row">
         <select :value="textData.fontFamily" @change="e => handleFontChange((e.target as HTMLSelectElement).value)" class="font-select">
            <template v-for="category in fontCategories" :key="category.name">
              <optgroup :label="category.name">
                <option v-for="font in category.fonts" :key="font.family" :value="font.family">
                  {{ font.family }}
                </option>
              </optgroup>
            </template>
         </select>
         <div class="style-toggles">
            <button :class="{active: textData.fontWeight === 'bold'}" @click="toggleBold">B</button>
            <button :class="{active: textData.fontStyle === 'italic'}" @click="toggleItalic">I</button>
         </div>
      </div>
      <div class="row" v-if="!hasSystemFonts">
         <button class="font-access-btn" @click="requestFontAccess" :disabled="loadingFonts">
           {{ loadingFonts ? 'Loading...' : '+ Load System Fonts' }}
         </button>
      </div>

      <div class="row">
         <label>Size</label>
         <ScrubableNumber :modelValue="getPropertyValue('Font Size') || textData.fontSize" @update:modelValue="v => updateAnimatable('Font Size', v)" />
      </div>

      <div class="row color-row">
         <div class="color-item">
            <input type="color" :value="textData.fill" @input="e => updateData('fill', (e.target as HTMLInputElement).value)" />
            <span>Fill</span>
         </div>
         <div class="color-item">
            <input type="color" :value="textData.stroke || '#000000'" @input="e => updateData('stroke', (e.target as HTMLInputElement).value)" />
            <span>Stroke</span>
         </div>
      </div>

      <div class="row">
         <label>Stroke Width</label>
         <ScrubableNumber :modelValue="getPropertyValue('Stroke Width') || textData.strokeWidth || 0" @update:modelValue="v => updateAnimatable('Stroke Width', v)" :min="0" :max="50" />
      </div>

      <div class="row">
         <label>Alignment</label>
         <div class="align-buttons">
            <button :class="{ active: textData.textAlign === 'left' }" @click="updateData('textAlign', 'left')">◀</button>
            <button :class="{ active: textData.textAlign === 'center' }" @click="updateData('textAlign', 'center')">▬</button>
            <button :class="{ active: textData.textAlign === 'right' }" @click="updateData('textAlign', 'right')">▶</button>
         </div>
      </div>
    </div>

    <div class="prop-section">
      <div class="section-title">Transform</div>

      <div class="row">
         <label>Position</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.position.value.x" @update:modelValue="v => updateTransform('position', 'x', v)" />
            <ScrubableNumber :modelValue="transform.position.value.y" @update:modelValue="v => updateTransform('position', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Anchor Pt</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.anchorPoint.value.x" @update:modelValue="v => updateTransform('anchorPoint', 'x', v)" />
            <ScrubableNumber :modelValue="transform.anchorPoint.value.y" @update:modelValue="v => updateTransform('anchorPoint', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Scale %</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.scale.value.x" @update:modelValue="v => updateTransform('scale', 'x', v)" />
            <ScrubableNumber :modelValue="transform.scale.value.y" @update:modelValue="v => updateTransform('scale', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Rotation</label>
         <ScrubableNumber :modelValue="transform.rotation.value" @update:modelValue="v => updateTransform('rotation', null, v)" />
      </div>
      <div class="row">
         <label>Opacity</label>
         <ScrubableNumber :modelValue="layer.opacity?.value ?? 100" @update:modelValue="v => updateOpacity(v)" :min="0" :max="100" />
      </div>
    </div>

    <div class="prop-section">
       <div class="section-title">Path Options</div>
       <div class="row">
          <label>Path</label>
          <select :value="textData.pathLayerId || ''" @change="e => updateData('pathLayerId', (e.target as HTMLSelectElement).value || null)" class="full-select">
             <option value="">None</option>
             <option v-for="l in splineLayers" :key="l.id" :value="l.id">{{ l.name }}</option>
          </select>
       </div>

       <template v-if="textData.pathLayerId">
         <div class="row">
            <label>Path Offset %</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('Path Offset') ?? textData.pathOffset ?? 0"
              @update:modelValue="v => updateAnimatable('Path Offset', v)"
              :min="-100"
              :max="200"
              :precision="1"
            />
            <button
              class="keyframe-btn"
              :class="{ active: isPropertyAnimated('Path Offset') }"
              @click="toggleKeyframe('Path Offset')"
              title="Add keyframe"
            >◆</button>
         </div>

         <div class="row">
            <label>First Margin</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('First Margin') ?? textData.pathFirstMargin ?? 0"
              @update:modelValue="v => updateAnimatable('First Margin', v)"
              :min="0"
            />
         </div>

         <div class="row">
            <label>Last Margin</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('Last Margin') ?? textData.pathLastMargin ?? 0"
              @update:modelValue="v => updateAnimatable('Last Margin', v)"
              :min="0"
            />
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathReversed" @change="updateData('pathReversed', !textData.pathReversed)" />
              Reverse Path
            </label>
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathPerpendicularToPath ?? true" @change="updateData('pathPerpendicularToPath', !textData.pathPerpendicularToPath)" />
              Perpendicular to Path
            </label>
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathForceAlignment" @change="updateData('pathForceAlignment', !textData.pathForceAlignment)" />
              Force Alignment
            </label>
         </div>
       </template>
    </div>

    <div class="prop-section">
       <div class="section-title">Advanced</div>
       <div class="row">
          <label>Tracking</label>
          <ScrubableNumber :modelValue="getPropertyValue('Tracking') || textData.tracking || 0" @update:modelValue="v => updateAnimatable('Tracking', v)" />
       </div>
       <div class="row">
          <label>Line Spacing</label>
          <ScrubableNumber :modelValue="getPropertyValue('Line Spacing') || textData.lineSpacing || 0" @update:modelValue="v => updateAnimatable('Line Spacing', v)" />
       </div>
       <div class="row">
          <label>Baseline</label>
          <ScrubableNumber :modelValue="getPropertyValue('Baseline Shift') || textData.baselineShift || 0" @update:modelValue="v => updateAnimatable('Baseline Shift', v)" />
       </div>
       <div class="row">
          <label>Char Offset</label>
          <ScrubableNumber :modelValue="getPropertyValue('Character Offset') || textData.characterOffset || 0" @update:modelValue="v => updateAnimatable('Character Offset', v)" :precision="0" />
       </div>
       <div class="row text-formatting-row">
          <label>Case</label>
          <div class="format-toggles">
            <button :class="{ active: textData.textCase === 'uppercase' }" @click="toggleCase('uppercase')" title="All Caps">AA</button>
            <button :class="{ active: textData.textCase === 'smallcaps' }" @click="toggleCase('smallcaps')" title="Small Caps">ᴀᴀ</button>
            <button :class="{ active: textData.textCase === 'normal' || !textData.textCase }" @click="toggleCase('normal')" title="Normal">Aa</button>
          </div>
       </div>
       <div class="row text-formatting-row">
          <label>Script</label>
          <div class="format-toggles">
            <button :class="{ active: textData.verticalAlign === 'super' }" @click="toggleVerticalAlign('super')" title="Superscript">X²</button>
            <button :class="{ active: textData.verticalAlign === 'sub' }" @click="toggleVerticalAlign('sub')" title="Subscript">X₂</button>
            <button :class="{ active: textData.verticalAlign === 'baseline' || !textData.verticalAlign }" @click="toggleVerticalAlign('baseline')" title="Normal">X</button>
          </div>
       </div>
    </div>

    <div class="prop-section checkbox">
       <label>
         <input type="checkbox" :checked="textData.perCharacter3D" @change="updateData('perCharacter3D', !textData.perCharacter3D)" />
         Enable Per-Character 3D
       </label>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';
import { fontService, type FontCategory } from '@/services/fontService';

const props = defineProps<{ layer: any }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

// Font loading state
const fontCategories = ref<FontCategory[]>([]);
const hasSystemFonts = ref(false);
const loadingFonts = ref(false);

onMounted(async () => {
  await fontService.initialize();
  fontCategories.value = fontService.getFontCategories();
  hasSystemFonts.value = fontService.hasSystemFonts();
});

// Request system font access (requires user interaction)
async function requestFontAccess() {
  loadingFonts.value = true;
  try {
    const success = await fontService.requestSystemFontAccess();
    if (success) {
      fontCategories.value = fontService.getFontCategories();
      hasSystemFonts.value = true;
    }
  } finally {
    loadingFonts.value = false;
  }
}

const textData = computed(() => props.layer.data);
const transform = computed(() => props.layer.transform);
const splineLayers = computed(() => store.layers.filter(l => l.type === 'spline'));

function getProperty(name: string) {
    return props.layer.properties?.find((p: any) => p.name === name);
}

function getPropertyValue(name: string) {
    const p = getProperty(name);
    return p ? p.value : null;
}

function updateText(val: string) {
    // Use store action to update text property
    store.setPropertyValue(props.layer.id, 'Source Text', val);
    // Also update the layer data directly for immediate render
    store.updateLayerData(props.layer.id, { text: val });
    emit('update');
}

function updateData(key: string, val: any) {
    // Use store action to update layer data
    store.updateLayerData(props.layer.id, { [key]: val });

    // Sync to animatable property via store
    const map: Record<string, string> = {
        'fill': 'Fill Color',
        'stroke': 'Stroke Color',
        'fontSize': 'Font Size',
        'strokeWidth': 'Stroke Width'
    };
    if (map[key]) {
        store.setPropertyValue(props.layer.id, map[key], val);
    }
    emit('update');
}

function updateAnimatable(name: string, val: number) {
    // Use store action to update property value
    store.setPropertyValue(props.layer.id, name, val);

    // Also update static data for immediate render via store
    const keyMap: Record<string, string> = {
        'Font Size': 'fontSize',
        'Stroke Width': 'strokeWidth',
        'Tracking': 'tracking',
        'Line Spacing': 'lineSpacing',
        'Baseline Shift': 'baselineShift',
        'Character Offset': 'characterOffset',
        'Path Offset': 'pathOffset',
        'First Margin': 'pathFirstMargin',
        'Last Margin': 'pathLastMargin'
    };
    if (keyMap[name]) {
        store.updateLayerData(props.layer.id, { [keyMap[name]]: val });
    }
    emit('update');
}

function isPropertyAnimated(name: string): boolean {
    const prop = getProperty(name);
    return prop?.animated ?? false;
}

function toggleKeyframe(name: string) {
    const prop = getProperty(name);
    if (!prop) return;

    const currentFrame = store.currentFrame;

    // Check if keyframe exists at current frame
    const existingKf = prop.keyframes?.find((kf: any) => kf.frame === currentFrame);

    if (existingKf) {
        // Remove keyframe via store
        store.removeKeyframe(props.layer.id, name, existingKf.id);
    } else {
        // Add keyframe at current frame via store
        store.addKeyframe(props.layer.id, name, prop.value, currentFrame);
    }

    emit('update');
}

function updateTransform(propName: string, axis: string | null, val: number) {
    const prop = transform.value[propName];
    let newValue: any;
    if (axis) {
        newValue = { ...prop.value, [axis]: val };
    } else {
        newValue = val;
    }
    // Use store action to update transform property
    store.setPropertyValue(props.layer.id, `transform.${propName}`, newValue);
    emit('update');
}

function updateOpacity(val: number) {
    // Use store action to update opacity
    store.setPropertyValue(props.layer.id, 'opacity', val);
    emit('update');
}

function toggleBold() {
    updateData('fontWeight', textData.value.fontWeight === 'bold' ? '400' : 'bold');
}
function toggleItalic() {
    updateData('fontStyle', textData.value.fontStyle === 'italic' ? 'normal' : 'italic');
}

function toggleCase(caseType: 'uppercase' | 'smallcaps' | 'normal') {
    updateData('textCase', caseType);
}

function toggleVerticalAlign(align: 'super' | 'sub' | 'baseline') {
    updateData('verticalAlign', align);
}

// Handle font change - ensure Google fonts are loaded
async function handleFontChange(family: string) {
    // Ensure the font is loaded before applying
    await fontService.ensureFont(family);
    updateData('fontFamily', family);
}
</script>

<style scoped>
.text-properties { padding: 15px; color: #ddd; font-family: 'Segoe UI', sans-serif; font-size: 13px; overflow-y: auto; }
.prop-section { margin-bottom: 20px; border-bottom: 1px solid #333; padding-bottom: 10px; }
.section-title { font-weight: bold; margin-bottom: 10px; color: #888; font-size: 13px; text-transform: uppercase; }

.row { display: flex; align-items: center; margin-bottom: 8px; gap: 10px; }
.row label { width: 80px; color: #aaa; flex-shrink: 0; }

.text-area { width: 100%; background: #222; border: 1px solid #444; color: #fff; padding: 8px; font-family: sans-serif; resize: vertical; border-radius: 3px; }
.text-area:focus { border-color: #4a90d9; outline: none; }

.font-select, .full-select { flex: 1; background: #222; color: #fff; border: 1px solid #444; padding: 6px; border-radius: 3px; max-width: 200px; }
.font-select:focus, .full-select:focus { border-color: #4a90d9; outline: none; }
.font-select optgroup { color: #888; font-style: normal; background: #1a1a1a; }
.font-select option { color: #fff; background: #222; padding: 4px; }

.font-row { flex-wrap: nowrap; }

.font-access-btn {
  flex: 1;
  background: #333;
  border: 1px dashed #555;
  color: #888;
  padding: 8px 12px;
  border-radius: 3px;
  cursor: pointer;
  font-size: 13px;
  transition: all 0.2s;
}
.font-access-btn:hover:not(:disabled) { background: #444; color: #aaa; border-color: #666; }
.font-access-btn:disabled { cursor: not-allowed; opacity: 0.6; }

.style-toggles { display: flex; gap: 2px; }
.style-toggles button { background: #333; border: 1px solid #444; color: #aaa; width: 28px; height: 28px; cursor: pointer; font-weight: bold; border-radius: 3px; }
.style-toggles button.active { background: #4a90d9; color: #fff; border-color: #4a90d9; }
.style-toggles button:hover:not(.active) { background: #444; }

.color-row { justify-content: flex-start; gap: 20px; }
.color-item { display: flex; align-items: center; gap: 8px; }
.color-item input[type="color"] { width: 32px; height: 28px; border: 1px solid #444; padding: 0; cursor: pointer; border-radius: 3px; background: #222; }
.color-item span { color: #aaa; font-size: 12px; }

.align-buttons { display: flex; background: #222; border: 1px solid #444; border-radius: 3px; overflow: hidden; }
.align-buttons button { flex: 1; background: transparent; border: none; color: #666; padding: 6px 12px; cursor: pointer; font-size: 12px; border-right: 1px solid #444; }
.align-buttons button:last-child { border-right: none; }
.align-buttons button.active { background: #4a90d9; color: #fff; }
.align-buttons button:hover:not(.active) { background: #333; color: #fff; }

.vec2 { display: flex; gap: 5px; flex: 1; }

.checkbox label { display: flex; align-items: center; gap: 10px; cursor: pointer; color: #eee; font-size: 13px; }
.checkbox input[type="checkbox"] { width: 16px; height: 16px; cursor: pointer; }

.checkbox-row label { display: flex; align-items: center; gap: 8px; cursor: pointer; color: #ddd; font-size: 12px; width: auto; }
.checkbox-row input[type="checkbox"] { width: 14px; height: 14px; cursor: pointer; }

.keyframe-btn {
  background: #333;
  border: 1px solid #444;
  color: #666;
  width: 24px;
  height: 24px;
  cursor: pointer;
  border-radius: 3px;
  font-size: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
}
.keyframe-btn:hover { background: #444; color: #888; }
.keyframe-btn.active { background: #b38600; color: #fff; border-color: #b38600; }

.text-formatting-row { gap: 8px; }
.format-toggles { display: flex; background: #222; border: 1px solid #444; border-radius: 3px; overflow: hidden; }
.format-toggles button {
  background: transparent;
  border: none;
  color: #888;
  padding: 6px 10px;
  cursor: pointer;
  font-size: 13px;
  border-right: 1px solid #444;
  min-width: 32px;
}
.format-toggles button:last-child { border-right: none; }
.format-toggles button.active { background: #4a90d9; color: #fff; }
.format-toggles button:hover:not(.active) { background: #333; color: #fff; }
</style>
