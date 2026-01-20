/// <reference types="vite/client" />

declare module "*.vue" {
  import type { DefineComponent } from "vue";
  const component: DefineComponent<Record<string, unknown>, Record<string, unknown>, unknown>;
  export default component;
}

// Global engine instance
import type { LatticeEngine } from "@/engine/LatticeEngine";

declare global {
  interface Window {
    __latticeEngine?: LatticeEngine;
  }
}
