<template>
  <div class="font-picker-overlay" @click.self="emit('close')">
    <div class="font-picker">
      <div class="picker-header">
        <h3>Select Font</h3>
        <button class="close-btn" @click="emit('close')">
          <i class="pi pi-times" />
        </button>
      </div>

      <!-- Search -->
      <div class="search-row">
        <i class="pi pi-search search-icon" />
        <input
          v-model="searchQuery"
          type="text"
          placeholder="Search fonts..."
          class="search-input"
          ref="searchInputRef"
        />
      </div>

      <!-- Font Categories -->
      <div class="font-categories">
        <div
          v-for="category in filteredCategories"
          :key="category.name"
          class="font-category"
        >
          <div class="category-header" @click="toggleCategory(category.name)">
            <i
              class="pi"
              :class="expandedCategories.has(category.name) ? 'pi-chevron-down' : 'pi-chevron-right'"
            />
            <span>{{ category.name }}</span>
            <span class="font-count">{{ category.fonts.length }}</span>
          </div>

          <div
            v-if="expandedCategories.has(category.name)"
            class="category-fonts"
          >
            <div
              v-for="font in category.fonts"
              :key="font.family"
              class="font-item"
              :class="{ selected: font.family === currentFont }"
              @click="selectFont(font.family)"
            >
              <span
                class="font-preview"
                :style="{ fontFamily: `'${font.family}', sans-serif` }"
              >
                {{ font.family }}
              </span>
              <span class="font-source">{{ font.source }}</span>
            </div>
          </div>
        </div>
      </div>

      <!-- Preview -->
      <div class="preview-section">
        <label>Preview:</label>
        <div
          class="preview-text"
          :style="{ fontFamily: `'${selectedPreviewFont}', sans-serif` }"
        >
          {{ previewText }}
        </div>
        <input
          v-model="previewText"
          type="text"
          class="preview-input"
          placeholder="Type preview text..."
        />
      </div>

      <!-- Actions -->
      <div class="picker-actions">
        <button
          v-if="hasSystemFonts === false"
          class="system-fonts-btn"
          @click="requestSystemFonts"
        >
          <i class="pi pi-desktop" />
          Load System Fonts
        </button>
        <button class="cancel-btn" @click="emit('close')">Cancel</button>
        <button
          class="select-btn"
          @click="confirmSelection"
          :disabled="!selectedPreviewFont"
        >
          Select
        </button>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, nextTick, onMounted, ref } from "vue";
import { type FontCategory, fontService } from "@/services/fontService";

interface Props {
  currentFont: string;
}

const props = defineProps<Props>();

const emit = defineEmits<{
  (e: "select", fontFamily: string): void;
  (e: "close"): void;
}>();

// Refs
const searchInputRef = ref<HTMLInputElement | null>(null);

// State
const searchQuery = ref("");
const selectedPreviewFont = ref(props.currentFont);
const previewText = ref("The quick brown fox jumps over the lazy dog");
const expandedCategories = ref(new Set(["Web Safe"]));
const fontCategories = ref<FontCategory[]>([]);
const hasSystemFonts = ref<boolean | null>(null);

// Filter categories based on search
const filteredCategories = computed(() => {
  if (!searchQuery.value.trim()) {
    return fontCategories.value;
  }

  const query = searchQuery.value.toLowerCase();

  return fontCategories.value
    .map((category) => ({
      ...category,
      fonts: category.fonts.filter((font) =>
        font.family.toLowerCase().includes(query),
      ),
    }))
    .filter((category) => category.fonts.length > 0);
});

// Initialize
onMounted(async () => {
  await fontService.initialize();
  fontCategories.value = fontService.getFontCategories();
  hasSystemFonts.value = fontService.hasSystemFonts();

  // Focus search input
  await nextTick();
  searchInputRef.value?.focus();

  // Load Google Font for current selection if needed
  if (props.currentFont) {
    await fontService.ensureFont(props.currentFont);
  }
});

// Category toggle
function toggleCategory(categoryName: string): void {
  if (expandedCategories.value.has(categoryName)) {
    expandedCategories.value.delete(categoryName);
  } else {
    expandedCategories.value.add(categoryName);
  }
}

// Font selection
async function selectFont(fontFamily: string): Promise<void> {
  selectedPreviewFont.value = fontFamily;

  // Ensure font is loaded for preview
  await fontService.ensureFont(fontFamily);
}

// Confirm selection
function confirmSelection(): void {
  if (selectedPreviewFont.value) {
    emit("select", selectedPreviewFont.value);
  }
}

// Request system fonts
async function requestSystemFonts(): Promise<void> {
  const success = await fontService.requestSystemFontAccess();
  if (success) {
    fontCategories.value = fontService.getFontCategories();
    hasSystemFonts.value = true;
    expandedCategories.value.add("System Fonts");
  }
}
</script>

<style scoped>
.font-picker-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.6);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.font-picker {
  width: 480px;
  max-height: 80vh;
  background: #2a2a2a;
  border-radius: 8px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.4);
  display: flex;
  flex-direction: column;
}

.picker-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 12px 16px;
  border-bottom: 1px solid #3d3d3d;
}

.picker-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 500;
  color: #e0e0e0;
}

.close-btn {
  padding: 4px 8px;
  border: none;
  background: transparent;
  color: #888;
  cursor: pointer;
}

.close-btn:hover {
  color: #fff;
}

.search-row {
  display: flex;
  align-items: center;
  padding: 12px 16px;
  border-bottom: 1px solid #3d3d3d;
  gap: 8px;
}

.search-icon {
  color: #666;
  font-size: 14px;
}

.search-input {
  flex: 1;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 13px;
}

.search-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.font-categories {
  flex: 1;
  overflow-y: auto;
  min-height: 200px;
  max-height: 300px;
}

.font-category {
  border-bottom: 1px solid #333;
}

.category-header {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 8px 16px;
  cursor: pointer;
  background: #2d2d2d;
  font-size: 12px;
  font-weight: 500;
  color: #aaa;
}

.category-header:hover {
  background: #333;
}

.category-header i {
  font-size: 12px;
  width: 16px;
}

.font-count {
  margin-left: auto;
  font-size: 12px;
  color: #666;
}

.category-fonts {
  background: #252525;
}

.font-item {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px 16px 8px 32px;
  cursor: pointer;
  transition: background 0.1s;
}

.font-item:hover {
  background: #2d2d2d;
}

.font-item.selected {
  background: rgba(74, 144, 217, 0.2);
}

.font-preview {
  font-size: 14px;
  color: #e0e0e0;
}

.font-source {
  font-size: 11px;
  color: #666;
  text-transform: uppercase;
  padding: 2px 4px;
  background: #333;
  border-radius: 2px;
}

.preview-section {
  padding: 12px 16px;
  border-top: 1px solid #3d3d3d;
}

.preview-section label {
  display: block;
  font-size: 13px;
  color: #888;
  margin-bottom: 8px;
}

.preview-text {
  font-size: 18px;
  color: #e0e0e0;
  padding: 12px;
  background: #1e1e1e;
  border-radius: 4px;
  margin-bottom: 8px;
  min-height: 48px;
  word-break: break-word;
}

.preview-input {
  width: 100%;
  padding: 6px 8px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 4px;
  font-size: 12px;
}

.preview-input:focus {
  outline: none;
  border-color: #4a90d9;
}

.picker-actions {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #3d3d3d;
}

.system-fonts-btn {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 12px;
  border: 1px solid #3d3d3d;
  background: transparent;
  color: #aaa;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
  margin-right: auto;
}

.system-fonts-btn:hover {
  background: #333;
  color: #fff;
}

.cancel-btn {
  padding: 6px 16px;
  border: 1px solid #3d3d3d;
  background: transparent;
  color: #aaa;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.cancel-btn:hover {
  background: #333;
  color: #fff;
}

.select-btn {
  padding: 6px 16px;
  border: none;
  background: #4a90d9;
  color: #fff;
  border-radius: 4px;
  font-size: 12px;
  cursor: pointer;
}

.select-btn:hover {
  background: #5a9fe9;
}

.select-btn:disabled {
  background: #333;
  color: #666;
  cursor: not-allowed;
}
</style>
