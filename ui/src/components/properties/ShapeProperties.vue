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
            @update:modelValue="(v: number) => updateAnimatable('Stroke Opacity', v, 'strokeOpacity')"
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
            @update:modelValue="(v: number) => updateAnimatable('Stroke Width', v, 'strokeWidth')"
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
            :modelValue="getPropertyValue('Dash Offset') ?? getNumericValue(shapeData.strokeDashOffset, 0)"
            @update:modelValue="(v: number) => updateAnimatable('Dash Offset', v, 'strokeDashOffset')"
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
            @update:modelValue="(v: number) => updateAnimatable('Fill Opacity', v, 'fillOpacity')"
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
            :modelValue="getPropertyValue('Trim Start') ?? getNumericValue(shapeData.trimStart, 0)"
            @update:modelValue="(v: number) => updateAnimatable('Trim Start', v, 'trimStart')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim Start') }" @click="toggleKeyframe('Trim Start', 'trimStart')">◆</button>
        </div>

        <div class="property-row">
          <label>End</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Trim End') ?? getNumericValue(shapeData.trimEnd, 100)"
            @update:modelValue="(v: number) => updateAnimatable('Trim End', v, 'trimEnd')"
            :min="0"
            :max="100"
            unit="%"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim End') }" @click="toggleKeyframe('Trim End', 'trimEnd')">◆</button>
        </div>

        <div class="property-row">
          <label>Offset</label>
          <ScrubableNumber
            :modelValue="getPropertyValue('Trim Offset') ?? getNumericValue(shapeData.trimOffset, 0)"
            @update:modelValue="(v: number) => updateAnimatable('Trim Offset', v, 'trimOffset')"
            :min="-360"
            :max="360"
            unit="°"
          />
          <button class="keyframe-btn" :class="{ active: isAnimated('Trim Offset') }" @click="toggleKeyframe('Trim Offset', 'trimOffset')">◆</button>
        </div>
      </div>
    </div>

    <!-- Path Effects Section -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('effects')">
        <span class="expand-icon">{{ expandedSections.includes('effects') ? '▼' : '►' }}</span>
        <span class="section-title">Path Effects</span>
        <span class="effect-count" v-if="pathEffects.length > 0">{{ pathEffects.length }}</span>
      </div>

      <div v-if="expandedSections.includes('effects')" class="section-content">
        <!-- Add Effect Button -->
        <div class="add-effect-row">
          <select v-model="newEffectType" class="effect-select">
            <option value="">Add Effect...</option>
            <option value="offsetPath">Offset Path</option>
            <option value="roughen">Roughen</option>
            <option value="wiggle">Wiggle Path</option>
            <option value="zigzag">Zig Zag</option>
            <option value="wave">Wave</option>
          </select>
          <button class="add-btn" @click="addEffect" :disabled="!newEffectType">+</button>
        </div>

        <!-- Effect List -->
        <div v-for="(effect, index) in pathEffects" :key="effect.id" class="effect-item">
          <div class="effect-header">
            <button class="effect-toggle" @click="toggleEffect(effect.id)">
              {{ effect.enabled ? '●' : '○' }}
            </button>
            <span class="effect-name">{{ getEffectDisplayName(effect.type) }}</span>
            <div class="effect-actions">
              <button class="effect-action" @click="moveEffect(index, -1)" :disabled="index === 0" title="Move Up">▲</button>
              <button class="effect-action" @click="moveEffect(index, 1)" :disabled="index === pathEffects.length - 1" title="Move Down">▼</button>
              <button class="effect-action delete" @click="removeEffect(effect.id)" title="Delete">×</button>
            </div>
          </div>

          <div v-if="effect.enabled" class="effect-params">
            <!-- Offset Path -->
            <template v-if="effect.type === 'offsetPath'">
              <div class="property-row">
                <label>Amount</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'amount')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'amount', v)"
                  :min="-100"
                  :max="100"
                  unit="px"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'amount') }" @click="toggleEffectKeyframe(effect.id, 'amount')">◆</button>
              </div>
              <div class="property-row">
                <label>Join</label>
                <div class="icon-toggle-group">
                  <button :class="{ active: effect.lineJoin === 'miter' }" @click="updateEffectMeta(effect.id, 'lineJoin', 'miter')">⟨</button>
                  <button :class="{ active: effect.lineJoin === 'round' }" @click="updateEffectMeta(effect.id, 'lineJoin', 'round')">◠</button>
                  <button :class="{ active: effect.lineJoin === 'bevel' }" @click="updateEffectMeta(effect.id, 'lineJoin', 'bevel')">∠</button>
                </div>
              </div>
            </template>

            <!-- Roughen -->
            <template v-else-if="effect.type === 'roughen'">
              <div class="property-row">
                <label>Size</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'size')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'size', v)"
                  :min="0"
                  :max="100"
                  unit="px"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'size') }" @click="toggleEffectKeyframe(effect.id, 'size')">◆</button>
              </div>
              <div class="property-row">
                <label>Detail</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'detail')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'detail', v)"
                  :min="1"
                  :max="10"
                  :step="1"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'detail') }" @click="toggleEffectKeyframe(effect.id, 'detail')">◆</button>
              </div>
              <div class="property-row">
                <label>Seed</label>
                <ScrubableNumber
                  :modelValue="effect.seed ?? 12345"
                  @update:modelValue="(v: number) => updateEffectMeta(effect.id, 'seed', v)"
                  :min="0"
                  :max="99999"
                  :step="1"
                />
              </div>
            </template>

            <!-- Wiggle -->
            <template v-else-if="effect.type === 'wiggle'">
              <div class="property-row">
                <label>Size</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'size')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'size', v)"
                  :min="0"
                  :max="100"
                  unit="px"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'size') }" @click="toggleEffectKeyframe(effect.id, 'size')">◆</button>
              </div>
              <div class="property-row">
                <label>Detail</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'detail')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'detail', v)"
                  :min="1"
                  :max="10"
                  :step="1"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'detail') }" @click="toggleEffectKeyframe(effect.id, 'detail')">◆</button>
              </div>
              <div class="property-row">
                <label>Correlation</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'correlation')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'correlation', v)"
                  :min="0"
                  :max="100"
                  unit="%"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'correlation') }" @click="toggleEffectKeyframe(effect.id, 'correlation')">◆</button>
              </div>
              <div class="property-row">
                <label>Temp Phase</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'temporalPhase')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'temporalPhase', v)"
                  :min="0"
                  :max="360"
                  unit="°"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'temporalPhase') }" @click="toggleEffectKeyframe(effect.id, 'temporalPhase')">◆</button>
              </div>
            </template>

            <!-- Zig Zag -->
            <template v-else-if="effect.type === 'zigzag'">
              <div class="property-row">
                <label>Size</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'size')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'size', v)"
                  :min="0"
                  :max="100"
                  unit="px"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'size') }" @click="toggleEffectKeyframe(effect.id, 'size')">◆</button>
              </div>
              <div class="property-row">
                <label>Ridges</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'ridgesPerSegment')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'ridgesPerSegment', v)"
                  :min="1"
                  :max="20"
                  :step="1"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'ridgesPerSegment') }" @click="toggleEffectKeyframe(effect.id, 'ridgesPerSegment')">◆</button>
              </div>
              <div class="property-row">
                <label>Points</label>
                <div class="icon-toggle-group">
                  <button :class="{ active: effect.pointType === 'corner' }" @click="updateEffectMeta(effect.id, 'pointType', 'corner')">∠</button>
                  <button :class="{ active: effect.pointType === 'smooth' }" @click="updateEffectMeta(effect.id, 'pointType', 'smooth')">◠</button>
                </div>
              </div>
            </template>

            <!-- Wave -->
            <template v-else-if="effect.type === 'wave'">
              <div class="property-row">
                <label>Amplitude</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'amplitude')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'amplitude', v)"
                  :min="0"
                  :max="100"
                  unit="px"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'amplitude') }" @click="toggleEffectKeyframe(effect.id, 'amplitude')">◆</button>
              </div>
              <div class="property-row">
                <label>Frequency</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'frequency')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'frequency', v)"
                  :min="0.1"
                  :max="20"
                  :step="0.1"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'frequency') }" @click="toggleEffectKeyframe(effect.id, 'frequency')">◆</button>
              </div>
              <div class="property-row">
                <label>Phase</label>
                <ScrubableNumber
                  :modelValue="getEffectPropValue(effect, 'phase')"
                  @update:modelValue="(v: number) => updateEffectProp(effect.id, 'phase', v)"
                  :min="0"
                  :max="360"
                  unit="°"
                />
                <button class="keyframe-btn" :class="{ active: isEffectPropAnimated(effect, 'phase') }" @click="toggleEffectKeyframe(effect.id, 'phase')">◆</button>
              </div>
              <div class="property-row">
                <label>Type</label>
                <div class="icon-toggle-group wide">
                  <button :class="{ active: effect.waveType === 'sine' }" @click="updateEffectMeta(effect.id, 'waveType', 'sine')">∿</button>
                  <button :class="{ active: effect.waveType === 'triangle' }" @click="updateEffectMeta(effect.id, 'waveType', 'triangle')">△</button>
                  <button :class="{ active: effect.waveType === 'square' }" @click="updateEffectMeta(effect.id, 'waveType', 'square')">□</button>
                </div>
              </div>
            </template>
          </div>
        </div>

        <div v-if="pathEffects.length === 0" class="no-effects">
          No path effects. Use the dropdown above to add one.
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

    <!-- Attached Elements Section - shows what's using this shape as a motion path -->
    <div class="prop-section">
      <div class="section-header" @click="toggleSection('attached')">
        <span class="expand-icon">{{ expandedSections.includes('attached') ? '▼' : '►' }}</span>
        <span class="section-title">Motion Path Usage</span>
        <span class="attached-count" v-if="attachedLayers.length > 0">{{ attachedLayers.length }}</span>
      </div>

      <div v-if="expandedSections.includes('attached')" class="section-content">
        <div v-if="attachedLayers.length === 0" class="no-attached">
          No layers are using this shape as a motion path.
          <p class="hint-text">Text, cameras, and particles can follow this shape's outline.</p>
        </div>
        <div v-else class="attached-list">
          <div
            v-for="attached in attachedLayers"
            :key="attached.id"
            class="attached-item"
            @click="selectLayer(attached.id)"
          >
            <span class="attached-icon">{{ getLayerIcon(attached.type) }}</span>
            <span class="attached-name">{{ attached.name }}</span>
            <span class="attached-usage">{{ attached.usage }}</span>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import type {
  AnimatableProperty,
  Layer,
  OffsetPathEffect,
  RoughenEffect,
  SplineData,
  SplinePathEffect,
  SplinePathEffectInstance,
  SplinePathEffectType,
  WaveEffect,
  WigglePathEffect,
  ZigZagEffect,
} from "@/types/project";

const props = defineProps<{ layer: Layer }>();
const emit = defineEmits(["update"]);
const store = useCompositorStore();

const expandedSections = ref<string[]>(["stroke", "fill", "trim"]);
const newEffectType = ref<SplinePathEffectType | "">("");

const shapeData = computed<SplineData>(() => {
  return (
    (props.layer.data as SplineData) || {
      pathData: "",
      controlPoints: [],
      closed: false,
      stroke: "#ffffff",
      strokeWidth: 2,
      strokeOpacity: 100,
      strokeLineCap: "round",
      strokeLineJoin: "round",
      fill: "",
      fillOpacity: 100,
      trimStart: 0,
      trimEnd: 100,
      trimOffset: 0,
    }
  );
});

const hasFill = computed(
  () => !!shapeData.value.fill && shapeData.value.fill !== "transparent",
);
const hasStroke = computed(
  () => !!shapeData.value.stroke && (shapeData.value.strokeWidth ?? 0) > 0,
);
const strokeLineCap = computed(() => shapeData.value.strokeLineCap || "round");
const strokeLineJoin = computed(
  () => shapeData.value.strokeLineJoin || "round",
);

// Helper to get dash array value from number[] | AnimatableProperty<number[]>
function getDashArray(): number[] {
  const dashArray = shapeData.value.strokeDashArray;
  if (!dashArray) return [];
  if (Array.isArray(dashArray)) return dashArray;
  // It's an AnimatableProperty<number[]>
  return dashArray.value ?? [];
}

const hasDashes = computed(() => getDashArray().length > 0);

const dashArrayString = computed(() => {
  return getDashArray().join(", ") || "";
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

// Find layers that reference this spline shape as a motion path
const attachedLayers = computed(() => {
  const layerId = props.layer.id;
  const attached: Array<{
    id: string;
    name: string;
    type: string;
    usage: string;
  }> = [];

  for (const layer of store.layers) {
    // Check text layers for path reference
    if (layer.type === "text") {
      const textData = layer.data as { pathLayerId?: string } | null;
      if (textData?.pathLayerId === layerId) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Text on path",
        });
      }
    }

    // Check camera layers for spline path
    if (layer.type === "camera") {
      const cameraData = layer.data as {
        pathFollowing?: { pathLayerId?: string };
      } | null;
      if (cameraData?.pathFollowing?.pathLayerId === layerId) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Camera path",
        });
      }
    }

    // Check particle layers for spline emission
    if (layer.type === "particles") {
      const particleData = layer.data as {
        emitters?: Array<{ shape?: string; splinePath?: { layerId?: string } }>;
      } | null;
      if (
        particleData?.emitters?.some(
          (e) => e.shape === "spline" && e.splinePath?.layerId === layerId,
        )
      ) {
        attached.push({
          id: layer.id,
          name: layer.name,
          type: layer.type,
          usage: "Particle emitter",
        });
      }
    }
  }

  return attached;
});

// Get layer icon for attached elements list
function getLayerIcon(type: string): string {
  const icons: Record<string, string> = {
    text: "T",
    camera: "🎥",
    particles: "✨",
  };
  return icons[type] || "◇";
}

// Select attached layer
function selectLayer(layerId: string) {
  layerStore.selectLayer(store, layerId);
}

// Update layer data
function update(key: keyof SplineData | string, value: unknown) {
  layerStore.updateLayer(store, props.layer.id, {
    data: { ...shapeData.value, [key]: value },
  });
  emit("update");
}

// Toggle fill on/off
function toggleFill(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  update("fill", checked ? "#ffffff" : "");
}

// Toggle stroke on/off
function toggleStroke(e: Event) {
  const checked = (e.target as HTMLInputElement).checked;
  if (checked) {
    update("stroke", "#ffffff");
    if ((shapeData.value.strokeWidth ?? 0) <= 0) {
      update("strokeWidth", 2);
    }
  } else {
    update("strokeWidth", 0);
  }
}

// Update dash array from string input
function updateDashArray(e: Event) {
  const input = (e.target as HTMLInputElement).value;
  if (!input.trim()) {
    update("strokeDashArray", []);
    return;
  }
  const values = input
    .split(",")
    .map((v) => parseFloat(v.trim()))
    .filter((v) => !Number.isNaN(v) && v >= 0);
  update("strokeDashArray", values);
}

// Get animatable property from layer.properties
function getProperty(name: string): AnimatableProperty<number> | undefined {
  return props.layer.properties?.find((p) => p.name === name) as
    | AnimatableProperty<number>
    | undefined;
}

// Extract numeric value from number or AnimatableProperty
function getNumericValue(
  value: number | AnimatableProperty<number> | undefined,
  fallback: number,
): number {
  if (value === undefined || value === null) return fallback;
  if (typeof value === "number") return value;
  // It's an AnimatableProperty, extract the value
  return value.value ?? fallback;
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
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName ? { ...p, value } : p,
    );
    layerStore.updateLayer(store, props.layer.id, { properties: updatedProperties });
  }
}

// Toggle keyframe for a property
function toggleKeyframe(propName: string, dataKey: string) {
  // Ensure property exists in layer.properties
  ensureProperty(propName, dataKey);

  const prop = getProperty(propName);
  if (prop) {
    const frame = store.currentFrame;
    const hasKeyframeAtFrame = prop.keyframes.some((k) => k.frame === frame);

    let updatedKeyframes: typeof prop.keyframes;
    let updatedAnimated: boolean;

    if (hasKeyframeAtFrame) {
      // Remove keyframe at current frame
      updatedKeyframes = prop.keyframes.filter((k) => k.frame !== frame);
      updatedAnimated = updatedKeyframes.length > 0;
    } else {
      // Add keyframe at current frame
      updatedKeyframes = [
        ...prop.keyframes,
        {
          id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
          frame,
          value: prop.value,
          interpolation: "linear" as const,
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: "corner" as const,
        },
      ];
      updatedAnimated = true;
    }

    // Update via store to track in history
    const updatedProperties = (props.layer.properties || []).map((p) =>
      p.name === propName
        ? { ...p, keyframes: updatedKeyframes, animated: updatedAnimated }
        : p,
    );
    layerStore.updateLayer(store, props.layer.id, { properties: updatedProperties });
    emit("update");
  }
}

// Type-safe property accessor for SplineData
// Maps component property keys to actual SplineData property names
function getSplineDataProperty(
  data: SplineData,
  key: string,
): number | AnimatableProperty<number> | undefined {
  // Map component dataKey strings to actual SplineData properties
  // Note: Component uses legacy names (strokeLineCap, strokeDashArray) but type uses (lineCap, dashArray)
  let propertyKey: keyof SplineData | undefined;
  if (key === "strokeOpacity") propertyKey = "strokeOpacity";
  else if (key === "strokeWidth") propertyKey = "strokeWidth";
  else if (key === "fillOpacity") propertyKey = "fillOpacity";
  else if (key === "trimStart") propertyKey = "trimStart";
  else if (key === "trimEnd") propertyKey = "trimEnd";
  else if (key === "trimOffset") propertyKey = "trimOffset";
  else if (key === "strokeDashOffset") propertyKey = "dashOffset"; // Map legacy name
  else return undefined;

  const value = data[propertyKey];
  if (value === undefined) return undefined;

  // Return as-is if it's already a number or AnimatableProperty
  if (typeof value === "number" || (typeof value === "object" && "value" in value)) {
    return value as number | AnimatableProperty<number>;
  }

  return undefined;
}

// Extract numeric value from number or AnimatableProperty
function extractNumericValue(
  value: number | AnimatableProperty<number> | undefined,
): number {
  if (value === undefined) return 0;
  if (typeof value === "number") return value;
  return value.value ?? 0;
}

// Ensure a property exists in layer.properties for timeline display
function ensureProperty(propName: string, dataKey: string) {
  const existingProperties = props.layer.properties || [];
  const existing = existingProperties.find((p) => p.name === propName);

  if (!existing) {
    const propertyValue = getSplineDataProperty(shapeData.value, dataKey);
    const currentValue = extractNumericValue(propertyValue);
    const newProperty = {
      id: `prop_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
      name: propName,
      type: "number",
      value: currentValue,
      animated: false,
      keyframes: [],
      group: propName.includes("Trim")
        ? "Trim Paths"
        : propName.includes("Stroke")
          ? "Stroke"
          : propName.includes("Fill")
            ? "Fill"
            : "Shape",
    } as AnimatableProperty<number>;

    // Update via store to track in history
    layerStore.updateLayer(store, props.layer.id, {
      properties: [...existingProperties, newProperty],
    });
  }
}

// ============================================================================
// PATH EFFECTS
// ============================================================================

const pathEffects = computed<SplinePathEffectInstance[]>(() => {
  return (
    (shapeData.value.pathEffects || []) as SplinePathEffectInstance[]
  ).sort((a, b) => a.order - b.order);
});

function getEffectDisplayName(type: SplinePathEffectType): string {
  const names: Record<SplinePathEffectType, string> = {
    offsetPath: "Offset Path",
    roughen: "Roughen",
    wiggle: "Wiggle Path",
    zigzag: "Zig Zag",
    wave: "Wave",
  };
  return names[type] || type;
}

function generateId(): string {
  return `effect_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`;
}

function createAnimatableProp(
  value: number,
  name: string,
): AnimatableProperty<number> {
  return {
    id: generateId(),
    name,
    type: "number",
    value,
    animated: false,
    keyframes: [],
  };
}

function addEffect() {
  if (!newEffectType.value) return;

  const effects = [...(shapeData.value.pathEffects || [])];
  const newOrder =
    effects.length > 0 ? Math.max(...effects.map((e) => e.order)) + 1 : 0;

  let newEffect: SplinePathEffect;

  switch (newEffectType.value) {
    case "offsetPath":
      newEffect = {
        id: generateId(),
        type: "offsetPath",
        enabled: true,
        order: newOrder,
        amount: createAnimatableProp(0, "Offset Amount"),
        lineJoin: "round",
        miterLimit: createAnimatableProp(4, "Miter Limit"),
      } as OffsetPathEffect;
      break;
    case "roughen":
      newEffect = {
        id: generateId(),
        type: "roughen",
        enabled: true,
        order: newOrder,
        size: createAnimatableProp(5, "Roughen Size"),
        detail: createAnimatableProp(2, "Roughen Detail"),
        seed: Math.floor(Math.random() * 99999),
      } as RoughenEffect;
      break;
    case "wiggle":
      newEffect = {
        id: generateId(),
        type: "wiggle",
        enabled: true,
        order: newOrder,
        size: createAnimatableProp(10, "Wiggle Size"),
        detail: createAnimatableProp(3, "Wiggle Detail"),
        temporalPhase: createAnimatableProp(0, "Temporal Phase"),
        spatialPhase: createAnimatableProp(0, "Spatial Phase"),
        correlation: createAnimatableProp(50, "Correlation"),
        seed: Math.floor(Math.random() * 99999),
      } as WigglePathEffect;
      break;
    case "zigzag":
      newEffect = {
        id: generateId(),
        type: "zigzag",
        enabled: true,
        order: newOrder,
        size: createAnimatableProp(10, "Zig Zag Size"),
        ridgesPerSegment: createAnimatableProp(5, "Ridges Per Segment"),
        pointType: "smooth",
      } as ZigZagEffect;
      break;
    case "wave":
      newEffect = {
        id: generateId(),
        type: "wave",
        enabled: true,
        order: newOrder,
        amplitude: createAnimatableProp(10, "Wave Amplitude"),
        frequency: createAnimatableProp(2, "Wave Frequency"),
        phase: createAnimatableProp(0, "Wave Phase"),
        waveType: "sine",
      } as WaveEffect;
      break;
    default:
      return;
  }

  effects.push(newEffect);
  update("pathEffects", effects);
  newEffectType.value = "";
}

function removeEffect(effectId: string) {
  const effects = (shapeData.value.pathEffects || []).filter(
    (e) => e.id !== effectId,
  );
  update("pathEffects", effects);
}

function toggleEffect(effectId: string) {
  const effects = [...(shapeData.value.pathEffects || [])];
  const effect = effects.find((e) => e.id === effectId);
  if (effect) {
    effect.enabled = !effect.enabled;
    update("pathEffects", effects);
  }
}

function moveEffect(index: number, direction: -1 | 1) {
  const effects = [...(shapeData.value.pathEffects || [])].sort(
    (a, b) => a.order - b.order,
  );
  const newIndex = index + direction;
  if (newIndex < 0 || newIndex >= effects.length) return;

  // Swap orders
  const tempOrder = effects[index].order;
  effects[index].order = effects[newIndex].order;
  effects[newIndex].order = tempOrder;

  update("pathEffects", effects);
}

// Type-safe property accessor for SplinePathEffect discriminated union
function getEffectPropValue(
  effect: SplinePathEffectInstance,
  propName: string,
): number {
  // Type-safe property access based on effect type
  if (effect.type === "offsetPath") {
    if (propName === "amount") return effect.amount.value;
    if (propName === "miterLimit") return effect.miterLimit.value;
  } else if (effect.type === "roughen") {
    if (propName === "size") return effect.size.value;
    if (propName === "detail") return effect.detail.value;
  } else if (effect.type === "wiggle") {
    if (propName === "size") return effect.size.value;
    if (propName === "detail") return effect.detail.value;
    if (propName === "temporalPhase") return effect.temporalPhase.value;
    if (propName === "spatialPhase") return effect.spatialPhase.value;
    if (propName === "correlation") return effect.correlation.value;
  } else if (effect.type === "zigzag") {
    if (propName === "size") return effect.size.value;
    if (propName === "ridgesPerSegment") return effect.ridgesPerSegment.value;
  } else if (effect.type === "wave") {
    if (propName === "amplitude") return effect.amplitude.value;
    if (propName === "frequency") return effect.frequency.value;
    if (propName === "phase") return effect.phase.value;
  }
  return 0;
}

// Type-safe check if effect property is animated
function isEffectPropAnimated(
  effect: SplinePathEffectInstance,
  propName: string,
): boolean {
  // Type-safe property access based on effect type
  let prop: AnimatableProperty<number> | undefined;
  if (effect.type === "offsetPath") {
    if (propName === "amount") prop = effect.amount;
    else if (propName === "miterLimit") prop = effect.miterLimit;
  } else if (effect.type === "roughen") {
    if (propName === "size") prop = effect.size;
    else if (propName === "detail") prop = effect.detail;
  } else if (effect.type === "wiggle") {
    if (propName === "size") prop = effect.size;
    else if (propName === "detail") prop = effect.detail;
    else if (propName === "temporalPhase") prop = effect.temporalPhase;
    else if (propName === "spatialPhase") prop = effect.spatialPhase;
    else if (propName === "correlation") prop = effect.correlation;
  } else if (effect.type === "zigzag") {
    if (propName === "size") prop = effect.size;
    else if (propName === "ridgesPerSegment") prop = effect.ridgesPerSegment;
  } else if (effect.type === "wave") {
    if (propName === "amplitude") prop = effect.amplitude;
    else if (propName === "frequency") prop = effect.frequency;
    else if (propName === "phase") prop = effect.phase;
  }
  if (!prop) return false;
  return prop.animated ?? false;
}

// Type-safe update of effect property value
function updateEffectProp(effectId: string, propName: string, value: number) {
  const effects = [...(shapeData.value.pathEffects || [])];
  const effect = effects.find((e) => e.id === effectId);
  if (!effect) return;

  // Type-safe property update based on effect type
  if (effect.type === "offsetPath") {
    if (propName === "amount") effect.amount.value = value;
    else if (propName === "miterLimit") effect.miterLimit.value = value;
  } else if (effect.type === "roughen") {
    if (propName === "size") effect.size.value = value;
    else if (propName === "detail") effect.detail.value = value;
  } else if (effect.type === "wiggle") {
    if (propName === "size") effect.size.value = value;
    else if (propName === "detail") effect.detail.value = value;
    else if (propName === "temporalPhase") effect.temporalPhase.value = value;
    else if (propName === "spatialPhase") effect.spatialPhase.value = value;
    else if (propName === "correlation") effect.correlation.value = value;
  } else if (effect.type === "zigzag") {
    if (propName === "size") effect.size.value = value;
    else if (propName === "ridgesPerSegment") effect.ridgesPerSegment.value = value;
  } else if (effect.type === "wave") {
    if (propName === "amplitude") effect.amplitude.value = value;
    else if (propName === "frequency") effect.frequency.value = value;
    else if (propName === "phase") effect.phase.value = value;
  }

  update("pathEffects", effects);
}

// Type-safe update of effect metadata (non-animatable properties)
function updateEffectMeta(
  effectId: string,
  key: string,
  value: string | number | boolean,
) {
  const effects = [...(shapeData.value.pathEffects || [])];
  const effect = effects.find((e) => e.id === effectId);
  if (!effect) return;

  // Type-safe metadata update based on effect type
  if (key === "enabled") {
    effect.enabled = value as boolean;
  } else if (key === "order") {
    effect.order = value as number;
  } else if (effect.type === "offsetPath" && key === "lineJoin") {
    effect.lineJoin = value as "miter" | "round" | "bevel";
  } else if (effect.type === "roughen" && key === "seed") {
    effect.seed = value as number;
  } else if (effect.type === "wiggle" && key === "seed") {
    effect.seed = value as number;
  } else if (effect.type === "zigzag" && key === "pointType") {
    effect.pointType = value as "corner" | "smooth";
  } else if (effect.type === "wave" && key === "waveType") {
    effect.waveType = value as "sine" | "triangle" | "square";
  }

  update("pathEffects", effects);
}

// Type-safe toggle keyframe for effect property
function toggleEffectKeyframe(effectId: string, propName: string) {
  const effects = [...(shapeData.value.pathEffects || [])];
  const effect = effects.find((e) => e.id === effectId);
  if (!effect) return;

  // Type-safe property access based on effect type
  let prop: AnimatableProperty<number> | undefined;
  if (effect.type === "offsetPath") {
    if (propName === "amount") prop = effect.amount;
    else if (propName === "miterLimit") prop = effect.miterLimit;
  } else if (effect.type === "roughen") {
    if (propName === "size") prop = effect.size;
    else if (propName === "detail") prop = effect.detail;
  } else if (effect.type === "wiggle") {
    if (propName === "size") prop = effect.size;
    else if (propName === "detail") prop = effect.detail;
    else if (propName === "temporalPhase") prop = effect.temporalPhase;
    else if (propName === "spatialPhase") prop = effect.spatialPhase;
    else if (propName === "correlation") prop = effect.correlation;
  } else if (effect.type === "zigzag") {
    if (propName === "size") prop = effect.size;
    else if (propName === "ridgesPerSegment") prop = effect.ridgesPerSegment;
  } else if (effect.type === "wave") {
    if (propName === "amplitude") prop = effect.amplitude;
    else if (propName === "frequency") prop = effect.frequency;
    else if (propName === "phase") prop = effect.phase;
  }

  if (!prop) return;

  const frame = store.currentFrame;
  const hasKeyframeAtFrame = prop.keyframes.some((k) => k.frame === frame);

  if (hasKeyframeAtFrame) {
    prop.keyframes = prop.keyframes.filter((k) => k.frame !== frame);
    prop.animated = prop.keyframes.length > 0;
  } else {
    prop.keyframes.push({
      id: `kf_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
      frame,
      value: prop.value,
      interpolation: "linear" as const,
      inHandle: { frame: -5, value: 0, enabled: false },
      outHandle: { frame: 5, value: 0, enabled: false },
      controlMode: "corner" as const,
    });
    prop.animated = true;
  }

  update("pathEffects", effects);
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

/* Path Effects Styles */
.effect-count {
  background: #4a90d9;
  color: #fff;
  font-size: 10px;
  padding: 1px 5px;
  border-radius: 8px;
  margin-left: auto;
}

.add-effect-row {
  display: flex;
  gap: 6px;
  margin-bottom: 8px;
}

.effect-select {
  flex: 1;
  padding: 6px 8px;
  background: #1a1a1a;
  border: 1px solid #3a3a3a;
  border-radius: 3px;
  color: #e0e0e0;
  font-size: 12px;
  cursor: pointer;
}

.effect-select:focus {
  outline: none;
  border-color: #4a90d9;
}

.add-btn {
  width: 28px;
  height: 28px;
  padding: 0;
  border: 1px solid #4a90d9;
  background: #4a90d9;
  color: #fff;
  border-radius: 3px;
  cursor: pointer;
  font-size: 18px;
  font-weight: bold;
  line-height: 1;
}

.add-btn:hover:not(:disabled) {
  background: #5a9fea;
}

.add-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.effect-item {
  background: #252525;
  border-radius: 4px;
  margin-bottom: 6px;
  overflow: hidden;
}

.effect-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  background: #2a2a2a;
}

.effect-toggle {
  background: transparent;
  border: none;
  color: #4a90d9;
  cursor: pointer;
  font-size: 12px;
  padding: 2px;
}

.effect-toggle:hover {
  color: #5a9fea;
}

.effect-name {
  flex: 1;
  font-size: 12px;
  color: #ccc;
  font-weight: 500;
}

.effect-actions {
  display: flex;
  gap: 2px;
}

.effect-action {
  background: transparent;
  border: none;
  color: #666;
  cursor: pointer;
  font-size: 10px;
  padding: 2px 4px;
  border-radius: 2px;
}

.effect-action:hover:not(:disabled) {
  background: #333;
  color: #ccc;
}

.effect-action:disabled {
  opacity: 0.3;
  cursor: not-allowed;
}

.effect-action.delete {
  color: #c44;
  font-size: 14px;
  font-weight: bold;
}

.effect-action.delete:hover {
  background: #c44;
  color: #fff;
}

.effect-params {
  padding: 8px;
  display: flex;
  flex-direction: column;
  gap: 6px;
  border-top: 1px solid #333;
}

.no-effects {
  color: #666;
  font-size: 12px;
  text-align: center;
  padding: 12px;
  font-style: italic;
}

.icon-toggle-group.wide button {
  padding: 4px 12px;
}

/* Motion Path Usage / Attached Elements */
.attached-count {
  background: #4a90d9;
  color: #fff;
  font-size: 10px;
  padding: 1px 5px;
  border-radius: 8px;
  margin-left: auto;
}

.no-attached {
  color: #666;
  font-size: 12px;
  text-align: center;
  padding: 12px;
  font-style: italic;
}

.no-attached .hint-text {
  margin-top: 6px;
  font-size: 11px;
  color: #555;
}

.attached-list {
  display: flex;
  flex-direction: column;
  gap: 4px;
}

.attached-item {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 8px;
  background: #252525;
  border-radius: 4px;
  cursor: pointer;
}

.attached-item:hover {
  background: #333;
}

.attached-icon {
  font-size: 12px;
}

.attached-name {
  flex: 1;
  font-size: 12px;
  color: #ccc;
}

.attached-usage {
  font-size: 11px;
  color: #666;
}
</style>
