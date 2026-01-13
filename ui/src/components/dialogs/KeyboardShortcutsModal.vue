<!--
  @component KeyboardShortcutsModal
  @description Modal showing all keyboard shortcuts organized by category
-->
<template>
  <Teleport to="body">
    <div v-if="show" class="modal-overlay" @click.self="emit('close')">
      <div class="modal-container" @keydown.escape="emit('close')">
        <div class="modal-header">
          <h2>Keyboard Shortcuts</h2>
          <button class="close-btn" @click="emit('close')" title="Close (Esc)">&times;</button>
        </div>

        <div class="search-bar">
          <input
            v-model="searchQuery"
            type="text"
            placeholder="Search shortcuts..."
            class="search-input"
            ref="searchInput"
          />
        </div>

        <div class="modal-content">
          <div v-for="category in filteredCategories" :key="category.name" class="shortcut-category">
            <h3 class="category-title">{{ category.name }}</h3>
            <div class="shortcut-list">
              <div
                v-for="shortcut in category.shortcuts"
                :key="shortcut.keys"
                class="shortcut-item"
              >
                <span class="shortcut-keys">
                  <kbd v-for="(key, idx) in parseKeys(shortcut.keys)" :key="idx">{{ key }}</kbd>
                </span>
                <span class="shortcut-description">{{ shortcut.description }}</span>
              </div>
            </div>
          </div>

          <div v-if="filteredCategories.length === 0" class="no-results">
            No shortcuts found for "{{ searchQuery }}"
          </div>
        </div>

        <div class="modal-footer">
          <span class="hint">Press <kbd>?</kbd> to toggle this modal</span>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { computed, nextTick, ref, watch } from "vue";

interface Shortcut {
  keys: string;
  description: string;
}

interface Category {
  name: string;
  shortcuts: Shortcut[];
}

const props = defineProps<{
  show: boolean;
}>();

const emit = defineEmits<(e: "close") => void>();

const searchQuery = ref("");
const searchInput = ref<HTMLInputElement | null>(null);

// Focus search input when modal opens
watch(
  () => props.show,
  (isVisible) => {
    if (isVisible) {
      nextTick(() => {
        searchInput.value?.focus();
      });
    } else {
      searchQuery.value = "";
    }
  },
);

const allCategories: Category[] = [
  {
    name: "Playback",
    shortcuts: [
      { keys: "Space", description: "Play / Pause" },
      { keys: "Home", description: "Go to start" },
      { keys: "End", description: "Go to end" },
      { keys: "Left", description: "Step backward 1 frame" },
      { keys: "Right", description: "Step forward 1 frame" },
      { keys: "Shift+Left", description: "Step backward 10 frames" },
      { keys: "Shift+Right", description: "Step forward 10 frames" },
      { keys: "J", description: "Go to previous keyframe" },
      { keys: "K", description: "Go to next keyframe" },
      { keys: "Ctrl+.", description: "Audio preview only" },
    ],
  },
  {
    name: "Layer Selection",
    shortcuts: [
      { keys: "Ctrl+A", description: "Select all layers" },
      { keys: "Ctrl+Up", description: "Select previous layer" },
      { keys: "Ctrl+Down", description: "Select next layer" },
      {
        keys: "Ctrl+Shift+Up",
        description: "Extend selection to previous layer",
      },
      {
        keys: "Ctrl+Shift+Down",
        description: "Extend selection to next layer",
      },
      { keys: "Delete", description: "Delete selected layers" },
    ],
  },
  {
    name: "Layer Editing",
    shortcuts: [
      { keys: "Ctrl+D", description: "Duplicate selected layers" },
      { keys: "Ctrl+C", description: "Copy selected layers" },
      { keys: "Ctrl+X", description: "Cut selected layers" },
      { keys: "Ctrl+V", description: "Paste layers" },
      { keys: "Ctrl+L", description: "Toggle layer lock" },
      { keys: "Ctrl+Shift+C", description: "Pre-compose selected layers" },
      { keys: "Ctrl+Shift+D", description: "Split layer at playhead" },
      { keys: "Ctrl+Alt+R", description: "Reverse layer / Reverse keyframes" },
      { keys: "Alt+Shift+F", description: "Freeze frame at playhead" },
      { keys: "Ctrl+Alt+F", description: "Fit layer to composition" },
      {
        keys: "Ctrl+Alt+Shift+F",
        description: "Fit layer to composition height",
      },
    ],
  },
  {
    name: "Layer Timing",
    shortcuts: [
      { keys: "I", description: "Go to layer in point" },
      { keys: "O", description: "Go to layer out point" },
      { keys: "[", description: "Move in point to playhead" },
      { keys: "]", description: "Move out point to playhead" },
      { keys: "Alt+[", description: "Trim in point to playhead" },
      { keys: "Alt+]", description: "Trim out point to playhead" },
      { keys: "Ctrl+Alt+T", description: "Time stretch dialog" },
    ],
  },
  {
    name: "Property Reveal (Solo)",
    shortcuts: [
      { keys: "P", description: "Position" },
      { keys: "S", description: "Scale" },
      { keys: "R", description: "Rotation" },
      { keys: "T", description: "Opacity (Transparency)" },
      { keys: "A", description: "Anchor Point (Origin)" },
      { keys: "U", description: "All animated properties" },
      { keys: "U U", description: "All modified properties" },
      { keys: "E", description: "Effects" },
      { keys: "E E", description: "Expressions" },
      { keys: "M", description: "Masks" },
      { keys: "M M", description: "All mask properties" },
    ],
  },
  {
    name: "Keyframes",
    shortcuts: [
      { keys: "F9", description: "Apply smooth easing" },
      { keys: "Shift+F9", description: "Apply ease in" },
      { keys: "Ctrl+Shift+F9", description: "Apply ease out" },
      { keys: "Ctrl+Alt+H", description: "Convert to hold keyframes" },
      { keys: "Ctrl+Shift+K", description: "Keyframe interpolation dialog" },
    ],
  },
  {
    name: "Tools",
    shortcuts: [
      { keys: "V", description: "Selection tool" },
      { keys: "H", description: "Hand tool (pan)" },
      { keys: "Z", description: "Zoom tool" },
      { keys: "P", description: "Pen tool" },
      { keys: "T", description: "Text tool" },
    ],
  },
  {
    name: "View & Zoom",
    shortcuts: [
      { keys: "=", description: "Zoom timeline in" },
      { keys: "-", description: "Zoom timeline out" },
      { keys: ";", description: "Zoom timeline to fit" },
      { keys: "Ctrl+=", description: "Zoom viewer in" },
      { keys: "Ctrl+-", description: "Zoom viewer out" },
      { keys: "Ctrl+0", description: "Fit viewer to window" },
      { keys: "Shift+G", description: "Toggle curve editor" },
      { keys: "Ctrl+Shift+H", description: "Toggle transparency grid" },
      { keys: "Ctrl+Shift+R", description: "Toggle rulers" },
      { keys: "Ctrl+Shift+;", description: "Toggle snap" },
    ],
  },
  {
    name: "Work Area",
    shortcuts: [
      { keys: "B", description: "Set work area start" },
      { keys: "N", description: "Set work area end" },
    ],
  },
  {
    name: "Project & Dialogs",
    shortcuts: [
      { keys: "Ctrl+K", description: "Composition settings" },
      { keys: "Ctrl+M", description: "Export dialog" },
      { keys: "Ctrl+I", description: "Import asset" },
      { keys: "Ctrl+Shift+I", description: "Import camera tracking" },
      { keys: "Ctrl+Z", description: "Undo" },
      { keys: "Ctrl+Shift+Z", description: "Redo" },
      { keys: "?", description: "Toggle keyboard shortcuts" },
    ],
  },
];

function parseKeys(keyString: string): string[] {
  return keyString.split("+").map((key) => {
    // Format special keys
    const keyMap: Record<string, string> = {
      Ctrl: "Ctrl",
      Shift: "Shift",
      Alt: "Alt",
      Space: "Space",
      Left: "←",
      Right: "→",
      Up: "↑",
      Down: "↓",
      Delete: "Del",
    };
    return keyMap[key] || key;
  });
}

const filteredCategories = computed(() => {
  if (!searchQuery.value.trim()) {
    return allCategories;
  }

  const query = searchQuery.value.toLowerCase();
  return allCategories
    .map((category) => ({
      name: category.name,
      shortcuts: category.shortcuts.filter(
        (s) =>
          s.description.toLowerCase().includes(query) ||
          s.keys.toLowerCase().includes(query),
      ),
    }))
    .filter((category) => category.shortcuts.length > 0);
});
</script>

<style scoped>
.modal-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.75);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.modal-container {
  background: var(--lattice-surface-1, #121212);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 8px;
  width: 700px;
  max-width: 90vw;
  max-height: 85vh;
  display: flex;
  flex-direction: column;
  box-shadow: 0 16px 48px rgba(0, 0, 0, 0.5);
}

.modal-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px 20px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.modal-header h2 {
  margin: 0;
  font-size: 16px;
  font-weight: 600;
  color: var(--lattice-text-primary, #e5e5e5);
}

.close-btn {
  width: 28px;
  height: 28px;
  border: none;
  background: transparent;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 20px;
  cursor: pointer;
  border-radius: 4px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.close-btn:hover {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-primary, #e5e5e5);
}

.search-bar {
  padding: 12px 20px;
  border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);
}

.search-input {
  width: 100%;
  padding: 8px 12px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 13px;
}

.search-input:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
}

.search-input::placeholder {
  color: var(--lattice-text-muted, #6b7280);
}

.modal-content {
  flex: 1;
  overflow-y: auto;
  padding: 16px 20px;
}

.shortcut-category {
  margin-bottom: 20px;
}

.shortcut-category:last-child {
  margin-bottom: 0;
}

.category-title {
  margin: 0 0 10px 0;
  font-size: 12px;
  font-weight: 600;
  color: var(--lattice-accent, #8b5cf6);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.shortcut-list {
  display: flex;
  flex-direction: column;
  gap: 6px;
}

.shortcut-item {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 6px 8px;
  border-radius: 4px;
}

.shortcut-item:hover {
  background: var(--lattice-surface-2, #1a1a1a);
}

.shortcut-keys {
  display: flex;
  gap: 4px;
  min-width: 140px;
}

kbd {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  min-width: 24px;
  height: 22px;
  padding: 0 6px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  font-size: 11px;
  font-family: inherit;
  color: var(--lattice-text-primary, #e5e5e5);
  box-shadow: 0 1px 0 rgba(0, 0, 0, 0.3);
}

.shortcut-description {
  flex: 1;
  font-size: 13px;
  color: var(--lattice-text-secondary, #9ca3af);
}

.no-results {
  text-align: center;
  padding: 40px 20px;
  color: var(--lattice-text-muted, #6b7280);
  font-size: 14px;
}

.modal-footer {
  padding: 12px 20px;
  border-top: 1px solid var(--lattice-border-subtle, #2a2a2a);
  text-align: center;
}

.hint {
  font-size: 12px;
  color: var(--lattice-text-muted, #6b7280);
}

.hint kbd {
  margin: 0 4px;
}

/* Custom scrollbar */
.modal-content::-webkit-scrollbar {
  width: 8px;
}

.modal-content::-webkit-scrollbar-track {
  background: transparent;
}

.modal-content::-webkit-scrollbar-thumb {
  background: var(--lattice-surface-3, #222);
  border-radius: 4px;
}

.modal-content::-webkit-scrollbar-thumb:hover {
  background: var(--lattice-surface-4, #2a2a2a);
}
</style>
