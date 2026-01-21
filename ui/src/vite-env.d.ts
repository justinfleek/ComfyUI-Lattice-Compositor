/// <reference types="vite/client" />

import type { DefineComponent } from "vue";

declare module "*.vue" {
  // Vue component type declaration - allows any component structure
  // This is intentionally permissive to match Vue's flexible component system
  const component: DefineComponent<any, any, any>;
  export default component;
}

// Global engine instance
import type { LatticeEngine } from "@/engine/LatticeEngine";

declare global {
  interface Window {
    __latticeEngine?: LatticeEngine;
  }
}
