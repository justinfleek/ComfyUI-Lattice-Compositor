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
}
</style>
