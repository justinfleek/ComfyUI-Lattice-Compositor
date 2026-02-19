<template>
  <Teleport to="body">
    <div v-if="visible" class="dialog-overlay" @click.self="$emit('close')">
      <div class="dialog-box">
        <div class="dialog-header">
          <h3>Pre-compose</h3>
          <button class="close-btn" @click="$emit('close')">&times;</button>
        </div>
        <div class="dialog-body">
          <div class="form-row">
            <label for="precomp-name">New composition name</label>
            <input
              id="precomp-name"
              ref="nameInput"
              v-model="compName"
              type="text"
              placeholder="Enter name..."
              @keydown.enter="confirm"
              @keydown.escape="$emit('close')"
            />
          </div>
          <div class="info-text">
            {{ layerCount }} layer{{ layerCount !== 1 ? 's' : '' }} will be moved to the new composition.
          </div>
        </div>
        <div class="dialog-footer">
          <button class="btn-cancel" @click="$emit('close')">Cancel</button>
          <button class="btn-confirm" @click="confirm" :disabled="!compName.trim()">OK</button>
        </div>
      </div>
    </div>
  </Teleport>
</template>

<script setup lang="ts">
import { nextTick, ref, watch } from "vue";

const props = defineProps<{
  visible: boolean;
  layerCount: number;
  defaultName?: string;
}>();

const emit = defineEmits<{
  close: [];
  confirm: [name: string];
}>();

const compName = ref(props.defaultName || "Pre-comp 1");
const nameInput = ref<HTMLInputElement | null>(null);

watch(
  () => props.visible,
  (visible) => {
    if (visible) {
      compName.value = props.defaultName || "Pre-comp 1";
      nextTick(() => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const nameInputValue = nameInput.value;
        if (nameInputValue != null && typeof nameInputValue === "object" && typeof nameInputValue.focus === "function") {
          nameInputValue.focus();
        }
        if (nameInputValue != null && typeof nameInputValue === "object" && typeof nameInputValue.select === "function") {
          nameInputValue.select();
        }
      });
    }
  },
);

function confirm() {
  if (compName.value.trim()) {
    emit("confirm", compName.value.trim());
    emit("close");
  }
}
</script>

<style scoped>
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  width: 100%;
  height: 100%;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.dialog-box {
  background: #1e1e1e;
  border: 1px solid #333;
  border-radius: 8px;
  width: 360px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px 16px;
  border-bottom: 1px solid #333;
}

.dialog-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 600;
  color: #fff;
}

.close-btn {
  background: transparent;
  border: none;
  color: #888;
  font-size: 20px;
  cursor: pointer;
  padding: 0;
  line-height: 1;
}
.close-btn:hover { color: #fff; }

.dialog-body {
  padding: 16px;
}

.form-row {
  margin-bottom: 12px;
}

.form-row label {
  display: block;
  color: #aaa;
  font-size: 12px;
  margin-bottom: 6px;
}

.form-row input {
  width: 100%;
  background: #111;
  border: 1px solid #444;
  color: #fff;
  padding: 8px 12px;
  border-radius: 4px;
  font-size: 13px;
}
.form-row input:focus {
  outline: none;
  border-color: #4a90d9;
}

.info-text {
  color: #666;
  font-size: 12px;
  font-style: italic;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 8px;
  padding: 12px 16px;
  border-top: 1px solid #333;
}

.btn-cancel, .btn-confirm {
  padding: 8px 16px;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
}

.btn-cancel {
  background: #333;
  border: 1px solid #444;
  color: #ccc;
}
.btn-cancel:hover { background: #444; }

.btn-confirm {
  background: #4a90d9;
  border: none;
  color: #fff;
}
.btn-confirm:hover:not(:disabled) { background: #5a9fe9; }
.btn-confirm:disabled { opacity: 0.5; cursor: not-allowed; }
</style>
