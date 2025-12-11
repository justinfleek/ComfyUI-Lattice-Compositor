/**
 * Vue Application Entry Point
 * Weyl Motion Graphics Compositor
 */
import { createApp } from 'vue';
import { createPinia } from 'pinia';
import PrimeVue from 'primevue/config';
import App from './App.vue';

// PrimeVue components we'll use
import Button from 'primevue/button';
import Slider from 'primevue/slider';
import Dropdown from 'primevue/dropdown';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import ColorPicker from 'primevue/colorpicker';
import Dialog from 'primevue/dialog';
import Tooltip from 'primevue/tooltip';

// Styles - loaded dynamically to work as embedded lib
const loadStyles = () => {
  // PrimeVue theme
  const themeLink = document.createElement('link');
  themeLink.rel = 'stylesheet';
  themeLink.href = 'https://unpkg.com/primevue/resources/themes/lara-dark-blue/theme.css';
  document.head.appendChild(themeLink);

  // PrimeIcons
  const iconsLink = document.createElement('link');
  iconsLink.rel = 'stylesheet';
  iconsLink.href = 'https://unpkg.com/primeicons/primeicons.css';
  document.head.appendChild(iconsLink);
};

loadStyles();

const app = createApp(App);

// Pinia for state management
const pinia = createPinia();
app.use(pinia);

// PrimeVue
app.use(PrimeVue);

// Register components globally
app.component('PButton', Button);
app.component('PSlider', Slider);
app.component('PDropdown', Dropdown);
app.component('PInputText', InputText);
app.component('PInputNumber', InputNumber);
app.component('PColorPicker', ColorPicker);
app.component('PDialog', Dialog);
app.directive('tooltip', Tooltip);

// Mount to container created by extension.js
const root = document.getElementById('weyl-compositor-root');
if (root) {
  app.mount(root);
} else {
  console.error('[Weyl] Could not find #weyl-compositor-root container');
}

// Listen for messages from ComfyUI
window.addEventListener('weyl:inputs-ready', async (event: Event) => {
  const customEvent = event as CustomEvent;
  const { useCompositorStore } = await import('./stores/compositorStore');
  const store = useCompositorStore();
  store.loadInputs(customEvent.detail);
});

window.addEventListener('weyl:keydown', async (event: Event) => {
  const customEvent = event as CustomEvent;
  // TODO: Implement keyboard service
  console.log('[Weyl] Keydown:', customEvent.detail);
});

console.log('[Weyl] Vue app mounted');
