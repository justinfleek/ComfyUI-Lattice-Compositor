<template>
  <div class="template-builder-overlay" v-if="visible" @click.self="close">
    <div class="template-builder-dialog">
      <!-- Dialog Header -->
      <div class="dialog-header">
        <h2>Template Builder</h2>
        <p class="dialog-subtitle">Create reusable motion graphics templates with exposed controls</p>
        <button class="close-btn" @click="close" title="Close">×</button>
      </div>

      <!-- Panel Header with Tabs -->
      <div class="panel-header">
        <div class="tabs">
        <button
          class="tab"
          :class="{ active: activeTab === 'browse' }"
          @click="activeTab = 'browse'"
        >
          Browse
        </button>
        <button
          class="tab"
          :class="{ active: activeTab === 'edit' }"
          @click="activeTab = 'edit'"
        >
          Edit
        </button>
      </div>
    </div>

    <!-- Browse Tab -->
    <div v-if="activeTab === 'browse'" class="tab-content browse-tab">
      <div class="search-bar">
        <input
          type="text"
          v-model="searchQuery"
          placeholder="Search templates..."
          class="search-input"
        />
      </div>

      <div class="templates-grid">
        <div
          v-for="template in filteredTemplates"
          :key="template.id"
          class="template-card"
          :class="{ selected: selectedTemplateId === template.id }"
          @click="selectTemplate(template)"
          @dblclick="applyTemplate(template)"
        >
          <div class="template-poster">
            <img v-if="template.posterImage" :src="template.posterImage" alt="" />
            <div v-else class="poster-placeholder">No Preview</div>
          </div>
          <div class="template-info">
            <span class="template-name">{{ template.name }}</span>
            <span class="template-author">{{ template.author || 'Local' }}</span>
          </div>
        </div>

        <div v-if="filteredTemplates.length === 0" class="no-templates">
          <p>No templates installed</p>
          <button class="btn-primary" @click="importTemplate">Import Template</button>
        </div>
      </div>

      <!-- Apply button when template selected -->
      <div v-if="selectedTemplateId" class="apply-section">
        <button class="btn-primary" @click="applySelectedTemplate">
          Apply to Composition
        </button>
      </div>
    </div>

    <!-- Edit Tab -->
    <div v-if="activeTab === 'edit'" class="tab-content edit-tab">
      <!-- Master Composition Selection -->
      <div v-if="!hasTemplate" class="no-master">
        <p class="message">Select a master composition to begin</p>
        <select v-model="selectedMasterCompId" class="comp-select">
          <option value="">-- Select Composition --</option>
          <option
            v-for="comp in compositions"
            :key="comp.id"
            :value="comp.id"
          >
            {{ comp.name }}
          </option>
        </select>
        <button
          class="btn-primary"
          :disabled="!selectedMasterCompId"
          @click="setMasterComposition"
        >
          Set Master Composition
        </button>
      </div>

      <!-- Template Editor -->
      <div v-else class="template-editor">
        <!-- Template Name -->
        <div class="template-name-section">
          <input
            type="text"
            v-model="templateName"
            placeholder="Template Name"
            class="template-name-input"
            @blur="updateTemplateName"
          />
          <button class="btn-icon" @click="clearMasterComposition" title="Clear Master">
            <span class="icon">×</span>
          </button>
        </div>

        <!-- Add Controls -->
        <div class="add-controls">
          <div class="add-dropdown">
            <button class="btn-secondary dropdown-trigger" @click="toggleAddMenu">
              + Add
            </button>
            <div v-if="showAddMenu" class="dropdown-menu">
              <button @click="addGroup">New Group</button>
              <button @click="addCommentItem">New Comment</button>
              <div class="dropdown-divider"></div>
              <div class="dropdown-label">Add Property from Layer:</div>
              <div
                v-for="layer in activeCompLayers"
                :key="layer.id"
                class="layer-item"
              >
                <button
                  class="layer-button"
                  @click="showLayerProperties(layer)"
                >
                  {{ layer.name }}
                </button>
              </div>
            </div>
          </div>
        </div>

        <!-- Properties List with Drag & Drop -->
        <div
          class="properties-list"
          @dragover.prevent="handleDragOver"
          @drop="handleDrop"
        >
          <!-- Ungrouped Properties -->
          <div
            v-for="(item, index) in organizedProperties.ungrouped"
            :key="item.id"
            class="property-item"
            :class="{
              selected: selectedPropertyId === item.id,
              'drag-over': dragOverIndex === index && !dragOverGroupId
            }"
            draggable="true"
            @dragstart="handleDragStart($event, item, index)"
            @dragend="handleDragEnd"
            @dragover.prevent="setDragOver(index, null)"
            @click="selectProperty(item)"
          >
            <div class="drag-handle">⋮⋮</div>
            <template v-if="isExposedProperty(item)">
              <ExposedPropertyControl
                :property="item"
                :layer="getLayerById(item.sourceLayerId)"
                @update="handlePropertyUpdate"
                @remove="removeProperty(item.id)"
              />
            </template>
            <template v-else>
              <CommentControl
                :comment="item"
                @update="handleCommentUpdate"
                @remove="removeCommentItem(item.id)"
              />
            </template>
          </div>

          <!-- Groups -->
          <div
            v-for="{ group, items } in organizedProperties.groups"
            :key="group.id"
            class="property-group"
            :class="{ collapsed: !group.expanded }"
          >
            <div
              class="group-header"
              @click="toggleGroup(group.id)"
              draggable="true"
              @dragstart="handleGroupDragStart($event, group)"
              @dragend="handleDragEnd"
              @dragover.prevent="setDragOver(-1, group.id)"
              :class="{ 'drag-over': dragOverGroupId === group.id }"
            >
              <div class="drag-handle">⋮⋮</div>
              <span class="expand-icon">{{ group.expanded ? '▼' : '▶' }}</span>
              <input
                type="text"
                v-model="group.name"
                class="group-name-input"
                @click.stop
                @blur="updateGroupName(group)"
              />
              <button
                class="btn-icon-small"
                @click.stop="removeGroup(group.id)"
                title="Remove Group"
              >
                ×
              </button>
            </div>
            <div
              v-if="group.expanded"
              class="group-content"
              @dragover.prevent="setDragOver(-1, group.id)"
              @drop="handleDropToGroup($event, group.id)"
            >
              <div
                v-for="(item, index) in items"
                :key="item.id"
                class="property-item"
                :class="{ selected: selectedPropertyId === item.id }"
                draggable="true"
                @dragstart="handleDragStart($event, item, index, group.id)"
                @dragend="handleDragEnd"
                @click="selectProperty(item)"
              >
                <div class="drag-handle">⋮⋮</div>
                <template v-if="isExposedProperty(item)">
                  <ExposedPropertyControl
                    :property="item"
                    :layer="getLayerById(item.sourceLayerId)"
                    @update="handlePropertyUpdate"
                    @remove="removeProperty(item.id)"
                  />
                </template>
                <template v-else>
                  <CommentControl
                    :comment="item"
                    @update="handleCommentUpdate"
                    @remove="removeCommentItem(item.id)"
                  />
                </template>
              </div>
              <div v-if="items.length === 0" class="group-empty">
                Drop properties here
              </div>
            </div>
          </div>
        </div>

        <!-- Layer Properties Picker Modal -->
        <div v-if="showPropertyPicker" class="property-picker-modal" @click.self="closePropertyPicker">
          <div class="picker-content">
            <div class="picker-header">
              <h3>Add Property from "{{ (selectedLayerForPicker != null && typeof selectedLayerForPicker === 'object' && 'name' in selectedLayerForPicker && typeof selectedLayerForPicker.name === 'string') ? selectedLayerForPicker.name : '' }}"</h3>
              <button class="btn-icon" @click="closePropertyPicker">×</button>
            </div>
            <div class="picker-list">
              <div
                v-for="prop in exposableProperties"
                :key="prop.path"
                class="picker-item"
                @click="addPropertyFromPicker(prop)"
              >
                <span class="prop-name">{{ prop.name }}</span>
                <span class="prop-type">{{ prop.type }}</span>
              </div>
            </div>
          </div>
        </div>

        <!-- Export Section -->
        <div class="export-section">
          <div class="poster-frame-control">
            <label>Poster Frame:</label>
            <input
              type="number"
              v-model.number="posterFrame"
              :min="0"
              :max="getMaxFrameCount()"
              class="poster-frame-input"
            />
            <button class="btn-small" @click="capturePosterFrame" :disabled="isCapturing">
              {{ isCapturing ? 'Capturing...' : 'Capture' }}
            </button>
          </div>
          <div v-if="posterImagePreview" class="poster-preview">
            <img :src="posterImagePreview" alt="Poster frame preview" />
          </div>
          <button
            class="btn-primary btn-export"
            @click="exportTemplate"
            :disabled="isExporting"
          >
            {{ isExporting ? 'Exporting...' : 'Export Template' }}
          </button>
        </div>
      </div>
    </div>

    <!-- Hidden file input for import -->
    <input
      ref="fileInput"
      type="file"
      accept=".lattice.json,.json"
      style="display: none"
      @change="handleFileImport"
    />
    </div>
  </div>
</template>

<script setup lang="ts">
import JSZip from "jszip";
import { computed, inject, onMounted, onUnmounted, ref, watch } from "vue";
import { safeNonNegativeDefault } from "@/utils/typeGuards";
import {
  safeJSONParse,
  safeJSONStringify,
  validateLatticeTemplate,
} from "@/services/jsonValidation";
import {
  addComment,
  addExposedProperty,
  addPropertyGroup,
  isExposedProperty as checkIsExposedProperty,
  clearTemplate,
  getExposableProperties,
  getOrganizedProperties,
  initializeTemplate,
  movePropertyToGroup,
  prepareTemplateExport,
  removeComment as removeCommentFn,
  removeExposedProperty,
  removePropertyGroup,
  reorderExposedProperties,
  updateComment as updateCommentFn,
  validateTemplate,
} from "@/services/templateBuilder";
import { useProjectStore } from "@/stores/projectStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useSelectionStore } from "@/stores/selectionStore";
import type { Layer } from "@/types/project";
import type {
  ExposedProperty,
  LatticeTemplate,
  PropertyGroup,
  SavedTemplate,
  TemplateComment,
} from "@/types/templateBuilder";
import type { JSONValue } from "@/types/dataAsset";

/**
 * All possible JavaScript values that can be validated at runtime
 * Used as input type for validators (replaces unknown)
 */
type RuntimeValue = string | number | boolean | object | null | undefined | bigint | symbol;

// Props and emits for dialog mode
const props = defineProps<{
  visible: boolean;
}>();

const emit = defineEmits<(e: "close") => void>();

function close() {
  emit("close");
}

// Inject frame capture from parent
const captureFrame = inject<() => Promise<string | null>>("captureFrame");

// Store
const projectStore = useProjectStore();
const animationStore = useAnimationStore();
const selectionStore = useSelectionStore();

// Helper function to create AnimationStoreAccess
function getAnimationStoreAccess() {
  return {
    project: projectStore.project,
    activeCompositionId: projectStore.activeCompositionId,
    currentFrame: animationStore.currentFrame,
    fps: projectStore.getFps(),
    frameCount: projectStore.getFrameCount(),
    selectedLayerIds: selectionStore.selectedLayerIds,
    getActiveComp: () => projectStore.getActiveComp(),
    pushHistory: () => projectStore.pushHistory(),
  };
}

// State
const activeTab = ref<"browse" | "edit">("edit");
const searchQuery = ref("");
const selectedMasterCompId = ref("");
const showAddMenu = ref(false);
const selectedPropertyId = ref<string | null>(null);
const showPropertyPicker = ref(false);
const selectedLayerForPicker = ref<Layer | null>(null);
const savedTemplates = ref<SavedTemplate[]>([]);
const selectedTemplateId = ref<string | null>(null);
const fileInput = ref<HTMLInputElement | null>(null);

// Export state
const isExporting = ref(false);
const isCapturing = ref(false);
const posterFrame = ref(0);
const posterImagePreview = ref<string | null>(null);

// Drag and drop state
const draggedItem = ref<ExposedProperty | TemplateComment | null>(null);
const draggedGroup = ref<PropertyGroup | null>(null);
const draggedFromGroupId = ref<string | null>(null);
const dragOverIndex = ref<number>(-1);
const dragOverGroupId = ref<string | null>(null);

// Computed
const compositions = computed(() => Object.values(projectStore.project.compositions));

const activeComposition = computed(() => projectStore.getActiveComp());

// Type proof: frameCount ∈ number | undefined → number (≥ 0, frame count)
function getMaxFrameCount(): number {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const activeComp = activeComposition.value;
  const settings = (activeComp != null && typeof activeComp === "object" && "settings" in activeComp && activeComp.settings != null && typeof activeComp.settings === "object") ? activeComp.settings : undefined;
  const frameCount = (settings != null && typeof settings === "object" && "frameCount" in settings && typeof settings.frameCount === "number") ? settings.frameCount : undefined;
  return safeNonNegativeDefault(frameCount, 0, "activeComposition.settings.frameCount");
}

// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
const activeCompLayers = computed(() => {
  const comp = activeComposition.value;
  const layers = (comp !== null && comp !== undefined && typeof comp === "object" && "layers" in comp) ? comp.layers : undefined;
  return (layers !== null && layers !== undefined && Array.isArray(layers)) ? layers : [];
});

const hasTemplate = computed(() => {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const activeComp = activeComposition.value;
  const templateConfig = (activeComp != null && typeof activeComp === "object" && "templateConfig" in activeComp && activeComp.templateConfig != null) ? activeComp.templateConfig : undefined;
  return templateConfig !== undefined;
});

const templateConfig = computed(() => {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const activeComp = activeComposition.value;
  return (activeComp != null && typeof activeComp === "object" && "templateConfig" in activeComp && activeComp.templateConfig != null) ? activeComp.templateConfig : undefined;
});

const templateName = computed({
  get: () => {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const templateConfigVal = templateConfig.value;
    const name = (templateConfigVal != null && typeof templateConfigVal === "object" && "name" in templateConfigVal && typeof templateConfigVal.name === "string") ? templateConfigVal.name : undefined;
    return name || "";
  },
  set: (value: string) => {
    if (templateConfig.value) {
      templateConfig.value.name = value;
    }
  },
});

const organizedProperties = computed(() => {
  if (!templateConfig.value) {
    return { ungrouped: [], groups: [] };
  }
  return getOrganizedProperties(templateConfig.value);
});

const exposableProperties = computed(() => {
  if (!selectedLayerForPicker.value) return [];
  return getExposableProperties(selectedLayerForPicker.value);
});

const filteredTemplates = computed(() => {
  if (!searchQuery.value) return savedTemplates.value;
  const query = searchQuery.value.toLowerCase();
  return savedTemplates.value.filter(
    (t) => {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const author = (t != null && typeof t === "object" && "author" in t && typeof t.author === "string") ? t.author : undefined;
      const tags = (t != null && typeof t === "object" && "tags" in t && t.tags != null && Array.isArray(t.tags)) ? t.tags : undefined;
      return t.name.toLowerCase().includes(query) ||
        (author != null && author.toLowerCase().includes(query)) ||
        (tags != null && typeof tags.some === "function" && tags.some((tag) => tag.toLowerCase().includes(query)));
    },
  );
});

// Methods
function setMasterComposition() {
  if (!selectedMasterCompId.value) return;

  const comp = projectStore.project.compositions[selectedMasterCompId.value];
  if (!comp) return;

  comp.templateConfig = initializeTemplate(comp);
  projectStore.pushHistory();
}

function clearMasterComposition() {
  if (!activeComposition.value) return;

  clearTemplate(activeComposition.value);
  projectStore.pushHistory();
}

function updateTemplateName() {
  if (templateConfig.value) {
    templateConfig.value.modified = new Date().toISOString();
    projectStore.pushHistory();
  }
}

function toggleAddMenu() {
  showAddMenu.value = !showAddMenu.value;
}

function addGroup() {
  if (!templateConfig.value) return;
  addPropertyGroup(templateConfig.value, "New Group");
  showAddMenu.value = false;
  projectStore.pushHistory();
}

function addCommentItem() {
  if (!templateConfig.value) return;
  addComment(templateConfig.value, "Enter instructions here...");
  showAddMenu.value = false;
  projectStore.pushHistory();
}

function showLayerProperties(layer: Layer) {
  selectedLayerForPicker.value = layer;
  showPropertyPicker.value = true;
  showAddMenu.value = false;
}

function closePropertyPicker() {
  showPropertyPicker.value = false;
  selectedLayerForPicker.value = null;
}

function addPropertyFromPicker(prop: {
  path: string;
  name: string;
  type: import("@/types/templateBuilder").ExposedPropertyType;
}) {
  if (!templateConfig.value || !selectedLayerForPicker.value) return;

  addExposedProperty(
    templateConfig.value,
    selectedLayerForPicker.value.id,
    prop.path,
    prop.name,
    prop.type,
  );

  closePropertyPicker();
  projectStore.pushHistory();
}

function selectProperty(item: ExposedProperty | TemplateComment) {
  selectedPropertyId.value = item.id;
}

function removeProperty(propertyId: string) {
  if (!templateConfig.value) return;
  removeExposedProperty(templateConfig.value, propertyId);
  projectStore.pushHistory();
}

function removeCommentItem(commentId: string) {
  if (!templateConfig.value) return;
  removeCommentFn(templateConfig.value, commentId);
  projectStore.pushHistory();
}

function toggleGroup(groupId: string) {
  if (!templateConfig.value) return;
  const group = templateConfig.value.groups.find((g) => g.id === groupId);
  if (group) {
    group.expanded = !group.expanded;
  }
}

function updateGroupName(group: PropertyGroup) {
  if (!templateConfig.value) return;
  templateConfig.value.modified = new Date().toISOString();
  projectStore.pushHistory();
}

function removeGroup(groupId: string) {
  if (!templateConfig.value) return;
  removePropertyGroup(templateConfig.value, groupId);
  projectStore.pushHistory();
}

function handlePropertyUpdate(
  propertyId: string,
  updates: Partial<ExposedProperty>,
) {
  if (!templateConfig.value) return;
  const property = templateConfig.value.exposedProperties.find(
    (p) => p.id === propertyId,
  );
  if (property) {
    Object.assign(property, updates);
    templateConfig.value.modified = new Date().toISOString();
    projectStore.pushHistory();
  }
}

function handleCommentUpdate(commentId: string, text: string) {
  if (!templateConfig.value) return;
  updateCommentFn(templateConfig.value, commentId, text);
  projectStore.pushHistory();
}

function getLayerById(layerId: string): Layer | undefined {
  return activeCompLayers.value.find((l) => l.id === layerId);
}

function isExposedProperty(
  item: ExposedProperty | TemplateComment,
): item is ExposedProperty {
  return checkIsExposedProperty(item);
}

// ===========================================
// DRAG AND DROP
// ===========================================

function handleDragStart(
  event: DragEvent,
  item: ExposedProperty | TemplateComment,
  _index: number,
  groupId?: string,
) {
  if (!event.dataTransfer) return;
  draggedItem.value = item;
  draggedGroup.value = null;
  draggedFromGroupId.value = groupId || null;
  event.dataTransfer.setData("text/plain", item.id);
  event.dataTransfer.effectAllowed = "move";
}

function handleGroupDragStart(event: DragEvent, group: PropertyGroup) {
  if (!event.dataTransfer) return;
  draggedGroup.value = group;
  draggedItem.value = null;
  event.dataTransfer.setData("text/plain", group.id);
  event.dataTransfer.effectAllowed = "move";
}

function handleDragEnd() {
  draggedItem.value = null;
  draggedGroup.value = null;
  draggedFromGroupId.value = null;
  dragOverIndex.value = -1;
  dragOverGroupId.value = null;
}

function handleDragOver(event: DragEvent) {
  event.preventDefault();
}

function setDragOver(index: number, groupId: string | null) {
  dragOverIndex.value = index;
  dragOverGroupId.value = groupId;
}

function handleDrop(event: DragEvent) {
  event.preventDefault();

  if (!templateConfig.value) return;

  // Handle dropping item to reorder
  if (draggedItem.value) {
    // If item was in a group, remove it from the group
    if (draggedFromGroupId.value) {
      movePropertyToGroup(
        templateConfig.value,
        draggedItem.value.id,
        undefined,
      );
    }

    // Reorder based on drop position
    if (dragOverIndex.value >= 0) {
      const ids = organizedProperties.value.ungrouped.map((p) => p.id);
      const fromIndex = ids.indexOf(draggedItem.value.id);
      if (fromIndex !== -1) {
        ids.splice(fromIndex, 1);
      }
      ids.splice(dragOverIndex.value, 0, draggedItem.value.id);
      reorderExposedProperties(templateConfig.value, ids);
    }

    projectStore.pushHistory();
  }

  handleDragEnd();
}

function handleDropToGroup(event: DragEvent, groupId: string) {
  event.preventDefault();
  event.stopPropagation();

  if (!templateConfig.value || !draggedItem.value) return;

  // Move item to this group
  movePropertyToGroup(templateConfig.value, draggedItem.value.id, groupId);
  projectStore.pushHistory();

  handleDragEnd();
}

// ===========================================
// TEMPLATE OPERATIONS
// ===========================================

function selectTemplate(template: SavedTemplate) {
  selectedTemplateId.value = template.id;
}

function applySelectedTemplate() {
  const template = savedTemplates.value.find(
    (t) => t.id === selectedTemplateId.value,
  );
  if (template) {
    applyTemplate(template);
  }
}

async function applyTemplate(template: SavedTemplate) {
  if (!activeComposition.value) {
    alert("Please select a composition first");
    return;
  }

  try {
    // Load the template data
    const tplData = template.templateData;
    if (!tplData) {
      alert("Template data not found");
      return;
    }

    // Apply exposed property values to current composition
    if (tplData.templateConfig && tplData.composition) {
      // Copy template config
      activeComposition.value.templateConfig = {
        ...tplData.templateConfig,
        masterCompositionId: activeComposition.value.id,
      };

      // Apply exposed property default values
      tplData.templateConfig.exposedProperties.forEach(
        (prop: ExposedProperty) => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const activeComp = activeComposition.value;
          const layers = (activeComp != null && typeof activeComp === "object" && "layers" in activeComp && activeComp.layers != null && Array.isArray(activeComp.layers)) ? activeComp.layers : undefined;
          const layer = (layers != null && typeof layers.find === "function") ? layers.find(
            (l) => l.name === prop.sourceLayerId,
          ) : undefined;
          if (layer && prop.defaultValue !== undefined) {
            // Set the property value on the layer
            setNestedProperty(
              layer,
              prop.sourcePropertyPath,
              prop.defaultValue,
            );
          }
        },
      );

      projectStore.pushHistory();
      activeTab.value = "edit";

      console.log("[TemplateBuilder] Template applied:", template.name);
    }
  } catch (error) {
    console.error("[TemplateBuilder] Failed to apply template:", error);
    alert("Failed to apply template");
  }
}

/**
 * Set nested property value in template builder object
 * Accepts any JSON-serializable value
 */
function setNestedProperty(
  obj: Record<string, JSONValue>,
  path: string,
  value: JSONValue,
) {
  const parts = path.split(".");
  let current = obj;

  for (let i = 0; i < parts.length - 1; i++) {
    if (current[parts[i]] === undefined) {
      current[parts[i]] = {};
    }
    current = current[parts[i]];
  }

  const lastPart = parts[parts.length - 1];
  if (
    current[lastPart] &&
    typeof current[lastPart] === "object" &&
    "value" in current[lastPart]
  ) {
    current[lastPart].value = value;
  } else {
    current[lastPart] = value;
  }
}

function importTemplate() {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const fileInputVal = fileInput.value;
  if (fileInputVal != null && typeof fileInputVal === "object" && typeof fileInputVal.click === "function") {
    fileInputVal.click();
  }
}

async function handleFileImport(event: Event) {
  const input = event.target as HTMLInputElement;
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const files = (input != null && typeof input === "object" && "files" in input && input.files != null && input.files.length > 0) ? input.files : null;
  const file = (files != null && files.length > 0) ? files[0] : undefined;
  if (!file) return;

  try {
    let templateData: LatticeTemplate | null = null;

    if (file.name.endsWith(".zip")) {
      // Load as ZIP (bundled template with assets)
      const zip = await JSZip.loadAsync(file);
      const manifestFile = zip.file("manifest.json");
      if (!manifestFile) {
        throw new Error("Invalid template bundle: missing manifest.json");
      }

      const manifestJson = await manifestFile.async("string");
      templateData = safeJSONParse<LatticeTemplate>(manifestJson);
    } else {
      // Load as JSON (.lattice.json or .json)
      const text = await file.text();
      templateData = safeJSONParse<LatticeTemplate>(text);
    }

    // Validate
    const validation = validateLatticeTemplate(templateData);
    if (!validation.valid) {
      throw new Error(
        `Invalid template: ${validation.errors.map((e) => e.message).join(", ")}`,
      );
    }

    // Add to saved templates
    const newTemplate: SavedTemplate = {
      id: `template_${Date.now()}`,
      name: templateData.templateConfig.name,
      author: "Imported",
      posterImage: templateData.posterImage,
      tags: [],
      importDate: new Date().toISOString(),
      templateData: templateData,
    };

    savedTemplates.value.push(newTemplate);
    console.log("[TemplateBuilder] Template imported:", newTemplate.name);

    // Reset file input
    input.value = "";
  } catch (error) {
    console.error("[TemplateBuilder] Import failed:", error);
    alert(
      `Import failed: ${error instanceof Error ? error.message : "Unknown error"}`,
    );
    input.value = "";
  }
}

// ===========================================
// POSTER FRAME CAPTURE
// ===========================================

async function capturePosterFrame() {
  if (!captureFrame) {
    console.warn("[TemplateBuilder] Frame capture not available");
    return;
  }

  isCapturing.value = true;

  try {
    // Set the frame to poster frame
    const originalFrame = animationStore.currentFrame;
    animationStore.setFrame(getAnimationStoreAccess(), posterFrame.value);

    // Wait for render
    await new Promise((resolve) => setTimeout(resolve, 100));

    // Capture
    const imageData = await captureFrame();
    if (imageData) {
      posterImagePreview.value = imageData;

      // Update template config
      if (templateConfig.value) {
        templateConfig.value.posterFrame = posterFrame.value;
      }

      console.log("[TemplateBuilder] Poster frame captured");
    }

    // Restore frame
    animationStore.setFrame(getAnimationStoreAccess(), originalFrame);
  } catch (error) {
    console.error("[TemplateBuilder] Failed to capture poster frame:", error);
  } finally {
    isCapturing.value = false;
  }
}

// ===========================================
// TEMPLATE EXPORT
// ===========================================

async function exportTemplate() {
  if (!activeComposition.value || !templateConfig.value) return;

  isExporting.value = true;

  try {
    // Validate template
    const validation = validateTemplate(
      templateConfig.value,
      activeComposition.value,
    );
    if (!validation.valid) {
      console.error("Template validation failed:", validation.errors);
      alert(`Template validation failed:\n${validation.errors.join("\n")}`);
      return;
    }

    if (validation.warnings.length > 0) {
      console.warn("Template warnings:", validation.warnings);
    }

    // Capture poster frame if not already captured
    let posterImage = posterImagePreview.value || "";
    if (!posterImage && captureFrame) {
      posterImage = (await captureFrame()) || "";
    }

    // Prepare template data
    const template = prepareTemplateExport(
      activeComposition.value,
      projectStore.project.assets,
      posterImage,
    );

    if (!template) {
      alert("Export failed: Could not prepare template");
      return;
    }

    // Serialize to JSON
    const json = safeJSONStringify(template);

    // Create blob and download as .lattice.json
    const blob = new Blob([json], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `${templateConfig.value.name.replace(/\s+/g, "_")}.lattice.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);

    console.log("[TemplateBuilder] Template exported successfully");
  } catch (error) {
    console.error("[TemplateBuilder] Export failed:", error);
    alert(
      `Export failed: ${error instanceof Error ? error.message : "Unknown error"}`,
    );
  } finally {
    isExporting.value = false;
  }
}

// Close menu when clicking outside
function handleClickOutside(event: MouseEvent) {
  const target = event.target as HTMLElement;
  if (!target.closest(".add-dropdown")) {
    showAddMenu.value = false;
  }
}

// Watch for composition changes
watch(activeComposition, (comp) => {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
  const templateConfig = (comp != null && typeof comp === "object" && "templateConfig" in comp && comp.templateConfig != null) ? comp.templateConfig : undefined;
  if (templateConfig) {
    // Type proof: posterFrame ∈ number | undefined → number (≥ 0, frame index)
    posterFrame.value = safeNonNegativeDefault(comp.templateConfig.posterFrame, 0, "comp.templateConfig.posterFrame");
  }
});

// Lifecycle
onMounted(() => {
  document.addEventListener("click", handleClickOutside);

  // Load installed templates from localStorage
  try {
    const saved = localStorage.getItem("lattice_saved_templates");
    if (saved) {
      savedTemplates.value = safeJSONParse<SavedTemplate[]>(saved);
    }
  } catch (_e) {
    console.warn("[TemplateBuilder] Failed to load saved templates");
  }
});

onUnmounted(() => {
  document.removeEventListener("click", handleClickOutside);

  // Save installed templates
  try {
    const json = safeJSONStringify(savedTemplates.value);
    localStorage.setItem("lattice_saved_templates", json);
  } catch (_e) {
    console.warn("[TemplateBuilder] Failed to save templates");
  }
});
</script>

<style scoped>
.template-builder-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.template-builder-dialog {
  display: flex;
  flex-direction: column;
  width: 600px;
  max-width: 90vw;
  max-height: 80vh;
  background: var(--lattice-surface-1, #121212);
  border-radius: 12px;
  color: var(--lattice-text-primary, #e5e5e5);
  box-shadow: 0 20px 60px rgba(0, 0, 0, 0.5);
  overflow: hidden;
}

.dialog-header {
  padding: 20px 24px;
  background: var(--lattice-surface-0, #0a0a0a);
  position: relative;
}

.dialog-header h2 {
  margin: 0 0 4px 0;
  font-size: 18px;
  font-weight: 600;
}

.dialog-subtitle {
  margin: 0;
  font-size: 13px;
  color: var(--lattice-text-muted, #6b7280);
}

.close-btn {
  position: absolute;
  top: 16px;
  right: 16px;
  width: 32px;
  height: 32px;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 24px;
  cursor: pointer;
  border-radius: 6px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.close-btn:hover {
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.panel-header {
  padding: 8px 16px;
}

.tabs {
  display: flex;
  gap: 4px;
}

.tab {
  flex: 1;
  padding: 6px 12px;
  background: transparent;
  border: none;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 12px;
  cursor: pointer;
  border-radius: 4px;
  transition: all 0.15s ease;
}

.tab:hover {
  background: var(--lattice-surface-2, #1a1a1a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.tab.active {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
  color: var(--lattice-accent, #8b5cf6);
}

.tab-content {
  flex: 1;
  overflow-y: auto;
  padding: 12px;
}

/* Browse Tab */
.search-bar {
  margin-bottom: 12px;
}

.search-input {
  width: 100%;
  padding: 8px 12px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
}

.search-input::placeholder {
  color: var(--lattice-text-muted, #6b7280);
}

.templates-grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(120px, 1fr));
  gap: 12px;
}

.template-card {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 6px;
  overflow: hidden;
  cursor: pointer;
  transition: all 0.15s ease;
}

.template-card:hover {
  border-color: var(--lattice-accent, #8b5cf6);
}

.template-card.selected {
  border-color: var(--lattice-accent, #8b5cf6);
  box-shadow: 0 0 0 1px var(--lattice-accent, #8b5cf6);
}

.template-poster {
  aspect-ratio: 16/9;
  background: var(--lattice-surface-0, #0a0a0a);
  display: flex;
  align-items: center;
  justify-content: center;
}

.template-poster img {
  width: 100%;
  height: 100%;
  object-fit: cover;
}

.poster-placeholder {
  color: var(--lattice-text-muted, #6b7280);
  font-size: 10px;
}

.template-info {
  padding: 8px;
}

.template-name {
  display: block;
  font-size: 11px;
  font-weight: 500;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.template-author {
  display: block;
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
}

.no-templates {
  grid-column: 1 / -1;
  text-align: center;
  padding: 24px;
  color: var(--lattice-text-muted, #6b7280);
}

.apply-section {
  padding: 12px 0;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
  margin-top: 12px;
}

/* Edit Tab */
.no-master {
  text-align: center;
  padding: 24px 0;
}

.message {
  color: var(--lattice-text-secondary, #9ca3af);
  margin-bottom: 16px;
}

.comp-select {
  width: 100%;
  padding: 8px 12px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  margin-bottom: 12px;
}

.template-editor {
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.template-name-section {
  display: flex;
  gap: 8px;
  align-items: center;
}

.template-name-input {
  flex: 1;
  padding: 8px 12px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 14px;
  font-weight: 500;
}

.btn-icon {
  width: 28px;
  height: 28px;
  padding: 0;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  color: var(--lattice-text-secondary, #9ca3af);
  cursor: pointer;
  font-size: 16px;
}

.btn-icon:hover {
  background: var(--lattice-surface-3, #222222);
  color: var(--lattice-text-primary, #e5e5e5);
}

.add-controls {
  position: relative;
}

.add-dropdown {
  position: relative;
}

.dropdown-trigger {
  width: 100%;
}

.dropdown-menu {
  position: absolute;
  top: 100%;
  left: 0;
  right: 0;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 4px 0;
  z-index: 100;
  max-height: 300px;
  overflow-y: auto;
}

.dropdown-menu button {
  display: block;
  width: 100%;
  padding: 8px 12px;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  text-align: left;
  cursor: pointer;
}

.dropdown-menu button:hover {
  background: var(--lattice-surface-4, #2a2a2a);
}

.dropdown-divider {
  height: 1px;
  background: var(--lattice-border-subtle, #2a2a2a);
  margin: 4px 0;
}

.dropdown-label {
  padding: 8px 12px 4px;
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
  text-transform: uppercase;
}

.properties-list {
  flex: 1;
  min-height: 100px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  padding: 4px;
}

.property-item {
  display: flex;
  align-items: flex-start;
  gap: 4px;
  padding: 4px;
  border-radius: 3px;
  cursor: grab;
  transition: background 0.1s ease;
}

.property-item:hover {
  background: var(--lattice-surface-2, #1a1a1a);
}

.property-item.selected {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
}

.property-item.drag-over {
  border-top: 2px solid var(--lattice-accent, #8b5cf6);
}

.drag-handle {
  color: var(--lattice-text-muted, #6b7280);
  font-size: 10px;
  cursor: grab;
  padding: 4px 2px;
  opacity: 0.5;
}

.property-item:hover .drag-handle {
  opacity: 1;
}

.property-group {
  margin: 4px 0;
  background: var(--lattice-surface-1, #121212);
  border-radius: 4px;
}

.group-header {
  display: flex;
  align-items: center;
  gap: 4px;
  padding: 8px;
  cursor: pointer;
  border-radius: 4px;
}

.group-header:hover {
  background: var(--lattice-surface-2, #1a1a1a);
}

.group-header.drag-over {
  background: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
}

.expand-icon {
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
}

.group-name-input {
  flex: 1;
  background: transparent;
  border: none;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  font-weight: 500;
  padding: 2px 4px;
}

.group-name-input:focus {
  outline: none;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 2px;
}

.btn-icon-small {
  width: 20px;
  height: 20px;
  padding: 0;
  background: transparent;
  border: none;
  color: var(--lattice-text-muted, #6b7280);
  cursor: pointer;
  font-size: 14px;
  opacity: 0;
}

.group-header:hover .btn-icon-small {
  opacity: 1;
}

.btn-icon-small:hover {
  color: var(--lattice-text-primary, #e5e5e5);
}

.group-content {
  padding: 4px 4px 4px 20px;
  min-height: 30px;
}

.group-empty {
  padding: 12px;
  text-align: center;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 11px;
  font-style: italic;
}

/* Property Picker Modal */
.property-picker-modal {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.6);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.picker-content {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 8px;
  width: 300px;
  max-height: 400px;
  overflow: hidden;
  display: flex;
  flex-direction: column;
}

.picker-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 16px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.picker-header h3 {
  font-size: 13px;
  font-weight: 500;
  margin: 0;
}

.picker-list {
  flex: 1;
  overflow-y: auto;
  padding: 8px;
}

.picker-item {
  display: flex;
  justify-content: space-between;
  padding: 8px 12px;
  border-radius: 4px;
  cursor: pointer;
  transition: background 0.1s ease;
}

.picker-item:hover {
  background: var(--lattice-surface-3, #222222);
}

.prop-name {
  font-size: 12px;
}

.prop-type {
  font-size: 10px;
  color: var(--lattice-text-muted, #6b7280);
  text-transform: uppercase;
}

/* Export Section */
.export-section {
  padding-top: 12px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.poster-frame-control {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.poster-frame-control label {
  font-size: 11px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.poster-frame-input {
  width: 60px;
  padding: 4px 6px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 11px;
}

.poster-preview {
  margin-bottom: 8px;
  border-radius: 4px;
  overflow: hidden;
  background: var(--lattice-surface-0, #0a0a0a);
}

.poster-preview img {
  width: 100%;
  height: auto;
  display: block;
}

.btn-small {
  padding: 4px 8px;
  background: var(--lattice-surface-3, #222222);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-secondary, #9ca3af);
  font-size: 10px;
  cursor: pointer;
}

.btn-small:hover:not(:disabled) {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e5e5e5);
}

.btn-small:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.btn-export {
  width: 100%;
}

/* Buttons */
.btn-primary {
  padding: 10px 16px;
  background: var(--lattice-accent, #8b5cf6);
  border: none;
  border-radius: 4px;
  color: white;
  font-size: 12px;
  font-weight: 500;
  cursor: pointer;
  transition: background 0.15s ease;
}

.btn-primary:hover:not(:disabled) {
  background: var(--lattice-accent-hover, #a78bfa);
}

.btn-primary:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.btn-secondary {
  padding: 8px 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  cursor: pointer;
}

.btn-secondary:hover {
  background: var(--lattice-surface-3, #222222);
}
</style>
