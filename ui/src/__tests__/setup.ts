/**
 * Test Setup
 *
 * Provides browser API mocks for Node.js test environment.
 * This enables testing of browser-dependent code like MotionBlurProcessor.
 */

import { vi } from 'vitest';

// ============================================================================
// ImageData Mock
// ============================================================================

// Use interface instead of class to avoid TypeScript strictness issues
interface MockImageDataInterface {
  readonly data: Uint8ClampedArray;
  readonly width: number;
  readonly height: number;
  readonly colorSpace: PredefinedColorSpace;
}

class MockImageData {
  readonly data: Uint8ClampedArray;
  readonly width: number;
  readonly height: number;
  readonly colorSpace: PredefinedColorSpace = 'srgb';

  constructor(sw: number, sh: number);
  constructor(data: Uint8ClampedArray, sw: number, sh?: number);
  constructor(dataOrWidth: Uint8ClampedArray | number, swOrHeight: number, sh?: number) {
    if (typeof dataOrWidth === 'number') {
      // new ImageData(width, height)
      this.width = dataOrWidth;
      this.height = swOrHeight;
      this.data = new Uint8ClampedArray(this.width * this.height * 4);
    } else {
      // new ImageData(data, width, height?)
      this.data = dataOrWidth;
      this.width = swOrHeight;
      this.height = sh ?? (dataOrWidth.length / 4 / swOrHeight);
    }
  }
}

// ============================================================================
// OffscreenCanvas Mock
// ============================================================================

class MockOffscreenCanvasRenderingContext2D {
  canvas: MockOffscreenCanvas;
  fillStyle: string | CanvasGradient | CanvasPattern = '#000000';
  strokeStyle: string | CanvasGradient | CanvasPattern = '#000000';
  lineWidth: number = 1;
  globalAlpha: number = 1;
  globalCompositeOperation: GlobalCompositeOperation = 'source-over';
  filter: string = 'none';

  private imageData: MockImageData;

  constructor(canvas: MockOffscreenCanvas) {
    this.canvas = canvas;
    this.imageData = new MockImageData(canvas.width, canvas.height);
  }

  fillRect(x: number, y: number, w: number, h: number): void {
    // Mock implementation - fills with current fillStyle
  }

  clearRect(x: number, y: number, w: number, h: number): void {
    // Mock implementation
  }

  strokeRect(x: number, y: number, w: number, h: number): void {
    // Mock implementation
  }

  drawImage(
    image: CanvasImageSource,
    dx: number,
    dy: number,
    dw?: number,
    dh?: number
  ): void {
    // Mock implementation - copy image data if available
    if (image instanceof MockOffscreenCanvas) {
      const srcCtx = image.getContext('2d') as unknown as MockOffscreenCanvasRenderingContext2D;
      if (srcCtx) {
        const srcData = srcCtx.getImageData(0, 0, image.width, image.height);
        this.putImageData(srcData as unknown as ImageData, dx, dy);
      }
    }
  }

  getImageData(sx: number, sy: number, sw: number, sh: number): ImageData {
    // Return a portion of the image data
    const data = new Uint8ClampedArray(sw * sh * 4);
    // Copy relevant portion (simplified - just returns empty data with correct size)
    return new MockImageData(data, sw, sh) as unknown as ImageData;
  }

  putImageData(imageData: ImageData, dx: number, dy: number): void {
    // Mock implementation - store image data
    this.imageData = imageData as MockImageData;
  }

  createImageData(sw: number, sh: number): ImageData;
  createImageData(imagedata: ImageData): ImageData;
  createImageData(swOrImageData: number | ImageData, sh?: number): ImageData {
    if (typeof swOrImageData === 'number') {
      return new MockImageData(swOrImageData, sh!) as unknown as ImageData;
    }
    return new MockImageData(swOrImageData.width, swOrImageData.height) as unknown as ImageData;
  }

  save(): void {}
  restore(): void {}
  scale(x: number, y: number): void {}
  rotate(angle: number): void {}
  translate(x: number, y: number): void {}
  transform(a: number, b: number, c: number, d: number, e: number, f: number): void {}
  setTransform(a: number, b: number, c: number, d: number, e: number, f: number): void {}
  resetTransform(): void {}

  beginPath(): void {}
  closePath(): void {}
  moveTo(x: number, y: number): void {}
  lineTo(x: number, y: number): void {}
  arc(x: number, y: number, r: number, start: number, end: number, ccw?: boolean): void {}
  arcTo(x1: number, y1: number, x2: number, y2: number, r: number): void {}
  bezierCurveTo(cp1x: number, cp1y: number, cp2x: number, cp2y: number, x: number, y: number): void {}
  quadraticCurveTo(cpx: number, cpy: number, x: number, y: number): void {}
  rect(x: number, y: number, w: number, h: number): void {}
  ellipse(x: number, y: number, rx: number, ry: number, rot: number, start: number, end: number, ccw?: boolean): void {}

  fill(fillRule?: CanvasFillRule): void {}
  stroke(): void {}
  clip(fillRule?: CanvasFillRule): void {}

  isPointInPath(x: number, y: number): boolean { return false; }
  isPointInStroke(x: number, y: number): boolean { return false; }

  measureText(text: string): TextMetrics {
    return {
      width: text.length * 10,
      actualBoundingBoxLeft: 0,
      actualBoundingBoxRight: text.length * 10,
      actualBoundingBoxAscent: 10,
      actualBoundingBoxDescent: 2,
      fontBoundingBoxAscent: 12,
      fontBoundingBoxDescent: 3,
      emHeightAscent: 10,
      emHeightDescent: 2,
      hangingBaseline: 9,
      alphabeticBaseline: 0,
      ideographicBaseline: -2,
    };
  }

  fillText(text: string, x: number, y: number, maxWidth?: number): void {}
  strokeText(text: string, x: number, y: number, maxWidth?: number): void {}

  createLinearGradient(x0: number, y0: number, x1: number, y1: number): CanvasGradient {
    return {
      addColorStop: () => {},
    } as CanvasGradient;
  }

  createRadialGradient(x0: number, y0: number, r0: number, x1: number, y1: number, r1: number): CanvasGradient {
    return {
      addColorStop: () => {},
    } as CanvasGradient;
  }

  createPattern(image: CanvasImageSource, repetition: string | null): CanvasPattern | null {
    return {} as CanvasPattern;
  }
}

class MockOffscreenCanvas {
  width: number;
  height: number;
  oncontextlost: ((this: OffscreenCanvas, ev: Event) => any) | null = null;
  oncontextrestored: ((this: OffscreenCanvas, ev: Event) => any) | null = null;

  private context: MockOffscreenCanvasRenderingContext2D | null = null;

  constructor(width: number, height: number) {
    this.width = width;
    this.height = height;
  }

  getContext(contextId: string, options?: any): any {
    if (contextId === '2d') {
      if (!this.context) {
        this.context = new MockOffscreenCanvasRenderingContext2D(this as any);
      }
      return this.context;
    }
    return null;
  }

  convertToBlob(options?: ImageEncodeOptions): Promise<Blob> {
    return Promise.resolve(new Blob(['mock-image-data'], { type: options?.type || 'image/png' }));
  }

  transferToImageBitmap(): ImageBitmap {
    return {
      width: this.width,
      height: this.height,
      close: () => {},
    } as ImageBitmap;
  }

  addEventListener(type: string, listener: EventListener): void {}
  removeEventListener(type: string, listener: EventListener): void {}
  dispatchEvent(event: Event): boolean { return true; }
}

// ============================================================================
// HTMLCanvasElement Mock (for tests that use regular canvas)
// ============================================================================

class MockHTMLCanvasElement {
  width: number = 300;
  height: number = 150;
  private context: MockOffscreenCanvasRenderingContext2D | null = null;

  getContext(contextId: string, options?: any): any {
    if (contextId === '2d') {
      if (!this.context) {
        const offscreen = new MockOffscreenCanvas(this.width, this.height);
        this.context = offscreen.getContext('2d') as MockOffscreenCanvasRenderingContext2D;
      }
      return this.context;
    }
    return null;
  }

  toDataURL(type?: string, quality?: number): string {
    return 'data:image/png;base64,mockdata';
  }

  toBlob(callback: BlobCallback, type?: string, quality?: number): void {
    callback(new Blob(['mock-image-data'], { type: type || 'image/png' }));
  }
}

// ============================================================================
// createImageBitmap Mock
// ============================================================================

async function mockCreateImageBitmap(
  image: ImageBitmapSource,
  options?: ImageBitmapOptions
): Promise<ImageBitmap>;
async function mockCreateImageBitmap(
  image: ImageBitmapSource,
  sx: number,
  sy: number,
  sw: number,
  sh: number,
  options?: ImageBitmapOptions
): Promise<ImageBitmap>;
async function mockCreateImageBitmap(
  image: ImageBitmapSource,
  sxOrOptions?: number | ImageBitmapOptions,
  sy?: number,
  sw?: number,
  sh?: number,
  options?: ImageBitmapOptions
): Promise<ImageBitmap> {
  let width = 100;
  let height = 100;

  if (image instanceof MockOffscreenCanvas) {
    width = image.width;
    height = image.height;
  } else if (image instanceof MockImageData) {
    width = image.width;
    height = image.height;
  }

  return {
    width,
    height,
    close: () => {},
  } as ImageBitmap;
}

// ============================================================================
// requestAnimationFrame Mock
// ============================================================================

let rafId = 0;
const rafCallbacks = new Map<number, FrameRequestCallback>();

function mockRequestAnimationFrame(callback: FrameRequestCallback): number {
  const id = ++rafId;
  rafCallbacks.set(id, callback);
  // Execute immediately in tests (can be changed for specific tests)
  setTimeout(() => {
    if (rafCallbacks.has(id)) {
      rafCallbacks.delete(id);
      callback(performance.now());
    }
  }, 0);
  return id;
}

function mockCancelAnimationFrame(id: number): void {
  rafCallbacks.delete(id);
}

// ============================================================================
// Install Global Mocks
// ============================================================================

// Only install if not already present (avoid overwriting in browser environment)
if (typeof globalThis.ImageData === 'undefined') {
  (globalThis as any).ImageData = MockImageData;
}

if (typeof globalThis.OffscreenCanvas === 'undefined') {
  (globalThis as any).OffscreenCanvas = MockOffscreenCanvas;
}

if (typeof globalThis.HTMLCanvasElement === 'undefined') {
  (globalThis as any).HTMLCanvasElement = MockHTMLCanvasElement;
}

if (typeof globalThis.createImageBitmap === 'undefined') {
  (globalThis as any).createImageBitmap = mockCreateImageBitmap;
}

if (typeof globalThis.requestAnimationFrame === 'undefined') {
  (globalThis as any).requestAnimationFrame = mockRequestAnimationFrame;
  (globalThis as any).cancelAnimationFrame = mockCancelAnimationFrame;
}

// ============================================================================
// Override document.createElement for canvas elements
// ============================================================================

// Store the original createElement
const originalCreateElement = document.createElement.bind(document);

// Override to return mock canvas for canvas elements
document.createElement = function(tagName: string, options?: ElementCreationOptions): any {
  if (tagName.toLowerCase() === 'canvas') {
    const mockCanvas = {
      width: 300,
      height: 150,
      style: {},
      _context2d: null as MockOffscreenCanvasRenderingContext2D | null,
      getContext(contextId: string, _options?: any): any {
        if (contextId === '2d') {
          if (!this._context2d) {
            const offscreen = new MockOffscreenCanvas(this.width, this.height);
            this._context2d = offscreen.getContext('2d') as MockOffscreenCanvasRenderingContext2D;
            // Sync canvas reference
            (this._context2d as any).canvas = this;
          }
          return this._context2d;
        }
        return null;
      },
      toDataURL(_type?: string, _quality?: number): string {
        return 'data:image/png;base64,mockdata';
      },
      toBlob(callback: BlobCallback, type?: string, _quality?: number): void {
        callback(new Blob(['mock-image-data'], { type: type || 'image/png' }));
      },
      getBoundingClientRect() {
        return { top: 0, left: 0, right: this.width, bottom: this.height, width: this.width, height: this.height, x: 0, y: 0, toJSON: () => ({}) };
      },
      addEventListener() {},
      removeEventListener() {},
      setAttribute() {},
      getAttribute() { return null; },
    };
    return mockCanvas as unknown as HTMLCanvasElement;
  }
  return originalCreateElement(tagName, options);
};

// ============================================================================
// Mock getComputedStyle for SVGLoader
// ============================================================================

// Override getComputedStyle to support SVG element style parsing
const originalGetComputedStyle = globalThis.getComputedStyle;

// Create a comprehensive mock CSSStyleDeclaration for SVG elements
function createMockCSSStyleDeclaration(): CSSStyleDeclaration {
  const styleValues: Record<string, string> = {
    'fill': '#000000',
    'stroke': 'none',
    'stroke-width': '1',
    'fill-opacity': '1',
    'stroke-opacity': '1',
    'opacity': '1',
    'display': 'inline',
    'visibility': 'visible',
    'color': '#000000',
    'font-family': 'sans-serif',
    'font-size': '16px',
    'font-weight': '400',
    'font-style': 'normal',
    'text-decoration': 'none',
    'transform': 'none',
    'clip-path': 'none',
    'mask': 'none',
    'filter': 'none',
  };

  // Use a Proxy to return empty string for any unknown property (not undefined)
  const handler: ProxyHandler<any> = {
    get(target, prop) {
      // Handle known methods/properties
      if (prop === 'getPropertyValue') {
        return (name: string) => styleValues[name] ?? '';
      }
      if (prop === 'getPropertyPriority') {
        return () => '';
      }
      if (prop === 'item') {
        return (_index: number) => '';
      }
      if (prop === 'length') {
        return 0;
      }
      if (prop === 'parentRule') {
        return null;
      }
      if (prop === 'cssText') {
        return '';
      }
      if (prop === 'removeProperty') {
        return () => '';
      }
      if (prop === 'setProperty') {
        return () => {};
      }
      if (prop === Symbol.iterator) {
        return function* () {};
      }
      // For any style property, return the value or empty string
      if (typeof prop === 'string') {
        return styleValues[prop] ?? '';
      }
      return undefined;
    }
  };

  return new Proxy({}, handler) as unknown as CSSStyleDeclaration;
}

(globalThis as any).getComputedStyle = function(element: Element, pseudoElt?: string | null): CSSStyleDeclaration {
  // For SVG elements or any element in test environment
  if (element instanceof SVGElement || element?.constructor?.name?.includes('SVG') || element?.tagName?.toLowerCase() === 'svg') {
    return createMockCSSStyleDeclaration();
  }

  // For other HTML elements, also provide a mock
  if (element instanceof HTMLElement || element?.nodeType === 1) {
    return createMockCSSStyleDeclaration();
  }

  // Fall back to original for other elements
  if (originalGetComputedStyle) {
    try {
      return originalGetComputedStyle(element, pseudoElt);
    } catch {
      return createMockCSSStyleDeclaration();
    }
  }

  // Default mock for non-browser environments
  return createMockCSSStyleDeclaration();
};

// ============================================================================
// SVGElement mock for Three.js SVGLoader
// ============================================================================

if (typeof globalThis.SVGElement === 'undefined') {
  (globalThis as any).SVGElement = class SVGElement extends Element {
    constructor() {
      // @ts-ignore - need to call super
      super();
    }
  };
}

// ============================================================================
// Export for direct use in tests
// ============================================================================

export {
  MockImageData,
  MockOffscreenCanvas,
  MockHTMLCanvasElement,
  mockCreateImageBitmap,
  mockRequestAnimationFrame,
  mockCancelAnimationFrame,
};

// ============================================================================
// Test Utilities
// ============================================================================

/**
 * Create a test ImageData with specified dimensions and fill color
 */
export function createTestImageData(
  width: number = 100,
  height: number = 100,
  fill: number | { r: number; g: number; b: number; a: number } = 128
): ImageData {
  const data = new Uint8ClampedArray(width * height * 4);
  const color = typeof fill === 'number'
    ? { r: fill, g: fill, b: fill, a: 255 }
    : fill;

  for (let i = 0; i < data.length; i += 4) {
    data[i] = color.r;
    data[i + 1] = color.g;
    data[i + 2] = color.b;
    data[i + 3] = color.a;
  }
  return new MockImageData(data, width, height) as unknown as ImageData;
}

/**
 * Create a test OffscreenCanvas with specified dimensions
 */
export function createTestCanvas(width: number, height: number): OffscreenCanvas {
  return new MockOffscreenCanvas(width, height) as unknown as OffscreenCanvas;
}

/**
 * Advance all pending requestAnimationFrame callbacks
 */
export function flushAnimationFrames(): void {
  const callbacks = Array.from(rafCallbacks.values());
  rafCallbacks.clear();
  const now = performance.now();
  callbacks.forEach(cb => cb(now));
}

// ============================================================================
// IndexedDB Mock (Added for auditLog tests)
// ============================================================================

const indexedDBMock = {
  open: vi.fn().mockReturnValue({
    result: {
      createObjectStore: vi.fn(),
      transaction: vi.fn(),
      objectStoreNames: { contains: vi.fn() },
    },
    addEventListener: vi.fn((event, callback) => {
      if (event === 'success') {
        setTimeout(() => callback({ target: { result: {} } }), 0);
      }
    }),
    onupgradeneeded: null,
    onsuccess: null,
    onerror: null,
  }),
};

if (typeof globalThis.indexedDB === 'undefined') {
  vi.stubGlobal('indexedDB', indexedDBMock);
}
