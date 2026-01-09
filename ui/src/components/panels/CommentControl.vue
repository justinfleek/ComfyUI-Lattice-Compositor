<template>
  <div class="comment-control" :class="{ expanded: isExpanded }">
    <div class="comment-header" @click="toggleExpand">
      <div class="comment-icon">
        <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
          <path d="M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2z"/>
        </svg>
      </div>
      <span class="comment-label">Comment</span>
      <button
        class="btn-icon-tiny expand-btn"
        :title="isExpanded ? 'Collapse' : 'Expand'"
      >
        <svg
          width="10"
          height="10"
          viewBox="0 0 24 24"
          fill="none"
          stroke="currentColor"
          stroke-width="2"
          :style="{ transform: isExpanded ? 'rotate(180deg)' : 'rotate(0deg)' }"
        >
          <polyline points="6 9 12 15 18 9"/>
        </svg>
      </button>
      <button
        class="btn-icon-tiny remove-btn"
        @click.stop="$emit('remove')"
        title="Remove comment"
      >
        ×
      </button>
    </div>

    <div v-if="isExpanded" class="comment-body">
      <textarea
        ref="textareaRef"
        v-model="localText"
        class="comment-textarea"
        placeholder="Add a note for template users..."
        @blur="updateText"
        @input="autoResize"
      />
    </div>
  </div>
</template>

<script setup lang="ts">
import { nextTick, onMounted, ref, watch } from "vue";
import type { TemplateComment } from "@/types/templateBuilder";

const props = defineProps<{
  comment: TemplateComment;
}>();

const emit = defineEmits<{
  (e: "update", commentId: string, text: string): void;
  (e: "remove"): void;
}>();

// Local state
const localText = ref(props.comment.text);
const isExpanded = ref(true);
const textareaRef = ref<HTMLTextAreaElement | null>(null);

// Watch for external changes
watch(
  () => props.comment.text,
  (newText) => {
    localText.value = newText;
  },
);

// Toggle expand/collapse
function toggleExpand() {
  isExpanded.value = !isExpanded.value;
  if (isExpanded.value) {
    nextTick(() => {
      autoResize();
    });
  }
}

// Update comment text
function updateText() {
  if (localText.value !== props.comment.text) {
    emit("update", props.comment.id, localText.value);
  }
}

// Auto-resize textarea based on content
function autoResize() {
  const textarea = textareaRef.value;
  if (textarea) {
    textarea.style.height = "auto";
    textarea.style.height = `${Math.max(60, textarea.scrollHeight)}px`;
  }
}

// Initialize textarea height on mount
onMounted(() => {
  nextTick(() => {
    autoResize();
  });
});
</script>

<style scoped>
.comment-control {
  background: var(--lattice-surface-2, #1a1a1a);
  border-radius: 4px;
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  overflow: hidden;
}

.comment-control.expanded {
  border-color: var(--lattice-accent-muted, rgba(139, 92, 246, 0.2));
}

.comment-header {
  display: flex;
  align-items: center;
  padding: 8px 10px;
  cursor: pointer;
  gap: 8px;
  user-select: none;
}

.comment-header:hover {
  background: var(--lattice-surface-3, #222222);
}

.comment-icon {
  color: var(--lattice-accent, #8b5cf6);
  display: flex;
  align-items: center;
  justify-content: center;
  opacity: 0.8;
}

.comment-label {
  flex: 1;
  font-size: 12px;
  font-weight: 500;
  color: var(--lattice-text-secondary, #9ca3af);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.btn-icon-tiny {
  width: 18px;
  height: 18px;
  padding: 0;
  background: none;
  border: none;
  color: var(--lattice-text-muted, #6b7280);
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  border-radius: 2px;
  transition: all 0.15s ease;
}

.btn-icon-tiny:hover {
  color: var(--lattice-text-primary, #e5e5e5);
  background: var(--lattice-surface-4, #2a2a2a);
}

.expand-btn svg {
  transition: transform 0.2s ease;
}

.remove-btn {
  font-size: 14px;
  opacity: 0;
  transition: opacity 0.15s ease;
}

.comment-control:hover .remove-btn {
  opacity: 1;
}

.remove-btn:hover {
  color: var(--lattice-error, #ef4444);
}

.comment-body {
  padding: 0 10px 10px;
}

.comment-textarea {
  width: 100%;
  min-height: 60px;
  padding: 8px 10px;
  background: var(--lattice-surface-0, #0a0a0a);
  border: 1px solid var(--lattice-border-subtle, #2a2a2a);
  border-radius: 3px;
  color: var(--lattice-text-primary, #e5e5e5);
  font-size: 12px;
  line-height: 1.5;
  resize: none;
  font-family: inherit;
}

.comment-textarea:focus {
  outline: none;
  border-color: var(--lattice-accent, #8b5cf6);
}

.comment-textarea::placeholder {
  color: var(--lattice-text-muted, #6b7280);
}
</style>
