<template>
  <WorkspaceLayout />
</template>

<script setup lang="ts">
import WorkspaceLayout from './components/layout/WorkspaceLayout.vue';
</script>

<style>
/* Global styles for the app */
* {
  box-sizing: border-box;
}

html, body, #app {
  margin: 0;
  padding: 0;
  width: 100%;
  height: 100%;
  overflow: hidden;
  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Oxygen, Ubuntu, sans-serif;
  font-size: 13px;
  line-height: 1.4;
}

/* Global font size increase for readability */
button, input, select, textarea, label {
  font-size: 13px;
}

/* Ensure small text is still readable */
.small-text, small {
  font-size: 12px;
}
</style>
