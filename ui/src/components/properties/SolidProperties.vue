<template>
  <div class="solid-properties">
    <!-- Color Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('color')">
        <i class="pi" :class="expandedSections.has('color') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Fill</span>
      </div>
      <div v-if="expandedSections.has('color')" class="section-content">
        <div class="property-row">
          <label>Color</label>
          <input
            type="color"
            :value="solidData.color"
            :disabled="solidData.shadowCatcher"
            @change="updateSolidData('color', ($event.target as HTMLInputElement).value)"
          />
          <span class="value-display">{{ solidData.color }}</span>
        </div>
        <div class="property-row">
          <label>Width</label>
          <input
            type="number"
            :value="solidData.width"
            min="1"
            max="7680"
            @change="updateSolidData('width', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
        <div class="property-row">
          <label>Height</label>
          <input
            type="number"
            :value="solidData.height"
            min="1"
            max="4320"
            @change="updateSolidData('height', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
      </div>
    </div>

    <!-- Shadow Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('shadow')">
        <i class="pi" :class="expandedSections.has('shadow') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Shadow</span>
      </div>
      <div v-if="expandedSections.has('shadow')" class="section-content">
        <div class="property-row">
          <label title="Shadow catcher mode - renders only shadows, not the solid color. Use for compositing 3D objects onto footage.">
            <input
              type="checkbox"
              :checked="solidData.shadowCatcher"
              @change="updateSolidData('shadowCatcher', ($event.target as HTMLInputElement).checked)"
            />
            Shadow Catcher
          </label>
        </div>

        <template v-if="solidData.shadowCatcher">
          <div class="property-row">
            <label title="Shadow opacity (0-100%)">Shadow Opacity</label>
            <input
              type="range"
              :value="solidData.shadowOpacity ?? 50"
              min="0"
              max="100"
              step="1"
              @input="updateSolidData('shadowOpacity', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ solidData.shadowOpacity ?? 50 }}%</span>
          </div>
          <div class="property-row">
            <label title="Shadow color (usually black)">Shadow Color</label>
            <input
              type="color"
              :value="solidData.shadowColor ?? '#000000'"
              @change="updateSolidData('shadowColor', ($event.target as HTMLInputElement).value)"
            />
          </div>
          <div class="info-note">
            Shadow catcher creates a transparent surface that only shows shadows cast by 3D objects.
            Perfect for compositing onto footage.
          </div>
        </template>

        <template v-else>
          <div class="property-row">
            <label title="Receive shadows from light layers">
              <input
                type="checkbox"
                :checked="solidData.receiveShadow"
                @change="updateSolidData('receiveShadow', ($event.target as HTMLInputElement).checked)"
              />
              Receive Shadows
            </label>
          </div>
        </template>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, reactive } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import type { SolidLayerData } from "@/types/project";

const props = defineProps<{
  layerId: string;
}>();

const emit =
  defineEmits<(e: "update", data: Partial<SolidLayerData>) => void>();

const store = useCompositorStore();

// Expanded sections
const expandedSections = reactive(new Set<string>(["color", "shadow"]));

function toggleSection(section: string) {
  if (expandedSections.has(section)) {
    expandedSections.delete(section);
  } else {
    expandedSections.add(section);
  }
}

// Get layer data
const layer = computed(() => store.layers.find((l) => l.id === props.layerId));

const solidData = computed<SolidLayerData>(() => {
  const data = layer.value?.data as SolidLayerData | undefined;
  return {
    color: data?.color ?? "#808080",
    width: data?.width ?? 1920,
    height: data?.height ?? 1080,
    shadowCatcher: data?.shadowCatcher ?? false,
    shadowOpacity: data?.shadowOpacity ?? 50,
    shadowColor: data?.shadowColor ?? "#000000",
    receiveShadow: data?.receiveShadow ?? false,
  };
});

function updateSolidData<K extends keyof SolidLayerData>(
  key: K,
  value: SolidLayerData[K],
) {
  store.updateLayerData(props.layerId, { [key]: value });
  emit("update", { [key]: value });
}
</script>

<style scoped>
.solid-properties {
  display: flex;
  flex-direction: column;
}

.property-section {
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.section-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 12px;
  cursor: pointer;
  user-select: none;
  font-size: var(--lattice-text-sm, 12px);
  font-weight: 500;
  color: var(--lattice-text-secondary, #9CA3AF);
  background: var(--lattice-surface-0, #0a0a0a);
}

.section-header:hover {
  background: var(--lattice-surface-1, #121212);
}

.section-content {
  padding: 8px 12px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  flex: 0 0 120px;
  font-size: var(--lattice-text-xs, 11px);
  color: var(--lattice-text-secondary, #9CA3AF);
}

.property-row input[type="color"] {
  width: 32px;
  height: 24px;
  padding: 0;
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  cursor: pointer;
}

.property-row input[type="number"] {
  flex: 1;
  max-width: 80px;
  padding: 4px 8px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #2a2a2a);
  border-radius: var(--lattice-radius-sm, 2px);
  color: var(--lattice-text-primary, #E5E5E5);
  font-size: var(--lattice-text-xs, 11px);
}

.property-row input[type="range"] {
  flex: 1;
  max-width: 120px;
}

.property-row input[type="checkbox"] {
  margin-right: 6px;
}

.value-display {
  font-size: var(--lattice-text-xs, 11px);
  color: var(--lattice-text-muted, #6B7280);
  min-width: 50px;
}

.info-note {
  padding: 8px 10px;
  margin-top: 8px;
  background: rgba(139, 92, 246, 0.1);
  border: 1px solid rgba(139, 92, 246, 0.3);
  border-radius: var(--lattice-radius-sm, 2px);
  font-size: var(--lattice-text-xs, 11px);
  color: var(--lattice-text-secondary, #9CA3AF);
  line-height: 1.4;
}
</style>
