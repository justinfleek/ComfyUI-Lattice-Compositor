/**
 * Module declarations for packages without TypeScript support
 */

declare module "splitpanes" {
  import { DefineComponent } from "vue";
  export const Splitpanes: DefineComponent<
    {
      horizontal?: boolean;
      pushOtherPanes?: boolean;
      dblClickSplitter?: boolean;
      rtl?: boolean;
    },
    {},
    any
  >;
  export const Pane: DefineComponent<
    {
      size?: number | string;
      minSize?: number | string;
      maxSize?: number | string;
    },
    {},
    any
  >;
}

// Three.js post-processing types (from examples)
declare module "three/examples/jsm/postprocessing/Pass" {
  import * as THREE from "three";
  export class Pass {
    enabled: boolean;
    needsSwap: boolean;
    clear: boolean;
    renderToScreen: boolean;
    setSize(width: number, height: number): void;
    render(
      renderer: THREE.WebGLRenderer,
      writeBuffer: THREE.WebGLRenderTarget,
      readBuffer: THREE.WebGLRenderTarget,
      deltaTime?: number,
      maskActive?: boolean,
    ): void;
    dispose(): void;
  }
}

// Augment THREE namespace for pass types
declare namespace THREE {
  class Pass {
    enabled: boolean;
    needsSwap: boolean;
    clear: boolean;
    renderToScreen: boolean;
    setSize(width: number, height: number): void;
    render(
      renderer: WebGLRenderer,
      writeBuffer: WebGLRenderTarget,
      readBuffer: WebGLRenderTarget,
      deltaTime?: number,
      maskActive?: boolean,
    ): void;
    dispose(): void;
  }
}

declare module "troika-three-text" {
  import * as THREE from "three";

  export class Text extends THREE.Mesh {
    text: string;
    fontSize: number;
    font: string | null;
    color: number | string;
    maxWidth: number;
    textAlign: "left" | "right" | "center" | "justify";
    anchorX: number | string;
    anchorY: number | string;
    letterSpacing: number;
    lineHeight: number;
    outlineWidth: number | string;
    outlineColor: number | string;
    outlineOpacity: number;
    strokeWidth: number | string;
    strokeColor: number | string;
    strokeOpacity: number;
    fillOpacity: number;
    material: THREE.Material;
    depthOffset: number;
    renderOrder: number;
    textRenderInfo: {
      glyphBounds: Float32Array;
      blockBounds: [number, number, number, number];
    } | null;
    sync(callback?: () => void): void;
    dispose(): void;
  }

  export function preloadFont(font: string, callback?: () => void): void;
}
