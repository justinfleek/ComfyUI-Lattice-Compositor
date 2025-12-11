/**
 * DepthMapImage - Custom Fabric.js class for depth map visualization
 *
 * Extends FabricImage to render grayscale depth maps with colormap visualization
 * (viridis/plasma). Uses WebGL shader when available, falls back to Canvas2D.
 *
 * IMPORTANT: Fabric.js 6.x uses ES6 classes, NOT createClass()
 */
import { FabricImage, classRegistry } from 'fabric';

export type ColormapType = 'viridis' | 'plasma' | 'grayscale';

interface DepthMapImageOptions {
  colormap?: ColormapType;
  opacity?: number;
  visible?: boolean;
}

// Viridis colormap LUT (256 entries)
const VIRIDIS_LUT = generateViridisLUT();
const PLASMA_LUT = generatePlasmaLUT();

function generateViridisLUT(): Uint8Array {
  const lut = new Uint8Array(256 * 4);
  // Viridis colormap approximation
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    // Viridis polynomial approximation
    const r = Math.round(255 * clamp(0.267004 + t * (0.004874 + t * (-0.259027 + t * (2.066795 + t * (-2.131557 + t * 0.736987))))));
    const g = Math.round(255 * clamp(0.004874 + t * (1.404613 + t * (-0.598103 + t * (-0.229949 + t * (0.659864 + t * -0.238132))))));
    const b = Math.round(255 * clamp(0.329415 + t * (1.384613 + t * (-1.860504 + t * (1.592785 + t * (-0.730173 + t * 0.135610))))));

    lut[i * 4] = r;
    lut[i * 4 + 1] = g;
    lut[i * 4 + 2] = b;
    lut[i * 4 + 3] = 255;
  }
  return lut;
}

function generatePlasmaLUT(): Uint8Array {
  const lut = new Uint8Array(256 * 4);
  // Plasma colormap approximation
  for (let i = 0; i < 256; i++) {
    const t = i / 255;
    const r = Math.round(255 * clamp(0.050383 + t * (2.689401 + t * (-1.802775 + t * (-0.391194 + t * (0.706557 + t * -0.218185))))));
    const g = Math.round(255 * clamp(0.029803 + t * (-0.177105 + t * (0.968330 + t * (0.419198 + t * (-0.991163 + t * 0.517737))))));
    const b = Math.round(255 * clamp(0.527975 + t * (1.546816 + t * (-4.246533 + t * (6.585146 + t * (-4.621553 + t * 1.205227))))));

    lut[i * 4] = r;
    lut[i * 4 + 1] = g;
    lut[i * 4 + 2] = b;
    lut[i * 4 + 3] = 255;
  }
  return lut;
}

function clamp(value: number): number {
  return Math.max(0, Math.min(1, value));
}

export class DepthMapImage extends FabricImage {
  static type = 'DepthMapImage';

  static ownDefaults: Partial<DepthMapImageOptions> = {
    colormap: 'viridis',
    opacity: 0.5,
    visible: true
  };

  declare colormap: ColormapType;
  declare _colorizedCanvas: HTMLCanvasElement | null;
  declare _webglContext: WebGLRenderingContext | null;
  declare _webglProgram: WebGLProgram | null;
  declare _sourceImageData: ImageData | null;

  constructor(element: HTMLImageElement | HTMLCanvasElement, options: DepthMapImageOptions = {}) {
    super(element, {
      ...DepthMapImage.ownDefaults,
      ...options
    });

    this.colormap = options.colormap || 'viridis';
    this._colorizedCanvas = null;
    this._webglContext = null;
    this._webglProgram = null;
    this._sourceImageData = null;

    // Initialize colorization after image loads
    this._initializeColorization();
  }

  /**
   * Initialize the colorization system (WebGL or Canvas2D fallback)
   */
  private _initializeColorization(): void {
    const element = this.getElement() as HTMLImageElement | HTMLCanvasElement;
    if (!element) return;

    // Create offscreen canvas for colorized output
    this._colorizedCanvas = document.createElement('canvas');
    this._colorizedCanvas.width = element.width || (element as HTMLImageElement).naturalWidth;
    this._colorizedCanvas.height = element.height || (element as HTMLImageElement).naturalHeight;

    // Try WebGL first
    if (this._initWebGL()) {
      this._applyColormapWebGL();
    } else {
      this._applyColormapCanvas2D();
    }
  }

  /**
   * Initialize WebGL context and shader program
   */
  private _initWebGL(): boolean {
    if (!this._colorizedCanvas) return false;

    try {
      const gl = this._colorizedCanvas.getContext('webgl', {
        preserveDrawingBuffer: true,
        alpha: true
      });

      if (!gl) return false;

      this._webglContext = gl;

      // Vertex shader
      const vertexShaderSource = `
        attribute vec2 a_position;
        attribute vec2 a_texCoord;
        varying vec2 v_texCoord;
        void main() {
          gl_Position = vec4(a_position, 0.0, 1.0);
          v_texCoord = a_texCoord;
        }
      `;

      // Fragment shader for colormap
      const fragmentShaderSource = `
        precision mediump float;
        uniform sampler2D u_image;
        uniform sampler2D u_colormap;
        varying vec2 v_texCoord;
        void main() {
          vec4 depth = texture2D(u_image, v_texCoord);
          float gray = dot(depth.rgb, vec3(0.299, 0.587, 0.114));
          vec4 color = texture2D(u_colormap, vec2(gray, 0.5));
          gl_FragColor = vec4(color.rgb, depth.a);
        }
      `;

      // Compile shaders
      const vertexShader = this._compileShader(gl, gl.VERTEX_SHADER, vertexShaderSource);
      const fragmentShader = this._compileShader(gl, gl.FRAGMENT_SHADER, fragmentShaderSource);

      if (!vertexShader || !fragmentShader) return false;

      // Create program
      const program = gl.createProgram();
      if (!program) return false;

      gl.attachShader(program, vertexShader);
      gl.attachShader(program, fragmentShader);
      gl.linkProgram(program);

      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
        console.error('[DepthMapImage] Program link error:', gl.getProgramInfoLog(program));
        return false;
      }

      this._webglProgram = program;
      return true;
    } catch (e) {
      console.warn('[DepthMapImage] WebGL init failed:', e);
      return false;
    }
  }

  private _compileShader(gl: WebGLRenderingContext, type: number, source: string): WebGLShader | null {
    const shader = gl.createShader(type);
    if (!shader) return null;

    gl.shaderSource(shader, source);
    gl.compileShader(shader);

    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      console.error('[DepthMapImage] Shader compile error:', gl.getShaderInfoLog(shader));
      gl.deleteShader(shader);
      return null;
    }

    return shader;
  }

  /**
   * Apply colormap using WebGL
   */
  private _applyColormapWebGL(): void {
    const gl = this._webglContext;
    const program = this._webglProgram;
    if (!gl || !program || !this._colorizedCanvas) return;

    gl.useProgram(program);

    // Set up vertex positions (full screen quad)
    const positionBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, positionBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      -1, -1, 1, -1, -1, 1,
      -1, 1, 1, -1, 1, 1
    ]), gl.STATIC_DRAW);

    const positionLocation = gl.getAttribLocation(program, 'a_position');
    gl.enableVertexAttribArray(positionLocation);
    gl.vertexAttribPointer(positionLocation, 2, gl.FLOAT, false, 0, 0);

    // Set up texture coordinates
    const texCoordBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, texCoordBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      0, 1, 1, 1, 0, 0,
      0, 0, 1, 1, 1, 0
    ]), gl.STATIC_DRAW);

    const texCoordLocation = gl.getAttribLocation(program, 'a_texCoord');
    gl.enableVertexAttribArray(texCoordLocation);
    gl.vertexAttribPointer(texCoordLocation, 2, gl.FLOAT, false, 0, 0);

    // Upload source image texture
    const imageTexture = gl.createTexture();
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, imageTexture);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, this.getElement() as HTMLImageElement);

    // Upload colormap LUT texture
    const colormapTexture = gl.createTexture();
    gl.activeTexture(gl.TEXTURE1);
    gl.bindTexture(gl.TEXTURE_2D, colormapTexture);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);

    const lut = this.colormap === 'plasma' ? PLASMA_LUT : VIRIDIS_LUT;
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 256, 1, 0, gl.RGBA, gl.UNSIGNED_BYTE, lut);

    // Set uniforms
    gl.uniform1i(gl.getUniformLocation(program, 'u_image'), 0);
    gl.uniform1i(gl.getUniformLocation(program, 'u_colormap'), 1);

    // Render
    gl.viewport(0, 0, this._colorizedCanvas.width, this._colorizedCanvas.height);
    gl.drawArrays(gl.TRIANGLES, 0, 6);
  }

  /**
   * Apply colormap using Canvas2D (fallback)
   */
  private _applyColormapCanvas2D(): void {
    if (!this._colorizedCanvas) return;

    const ctx = this._colorizedCanvas.getContext('2d');
    if (!ctx) return;

    const element = this.getElement() as HTMLImageElement | HTMLCanvasElement;
    const width = this._colorizedCanvas.width;
    const height = this._colorizedCanvas.height;

    // Draw original image
    ctx.drawImage(element, 0, 0, width, height);

    // Get pixel data
    const imageData = ctx.getImageData(0, 0, width, height);
    const data = imageData.data;

    // Get LUT based on colormap type
    const lut = this.colormap === 'plasma' ? PLASMA_LUT :
                this.colormap === 'viridis' ? VIRIDIS_LUT : null;

    if (!lut) {
      // Grayscale - no transformation needed
      return;
    }

    // Apply colormap
    for (let i = 0; i < data.length; i += 4) {
      // Convert to grayscale
      const gray = Math.round(
        data[i] * 0.299 +
        data[i + 1] * 0.587 +
        data[i + 2] * 0.114
      );

      // Look up colormap value
      data[i] = lut[gray * 4];
      data[i + 1] = lut[gray * 4 + 1];
      data[i + 2] = lut[gray * 4 + 2];
      // Alpha stays unchanged
    }

    ctx.putImageData(imageData, 0, 0);
  }

  /**
   * Set the colormap and re-apply
   */
  setColormap(colormap: ColormapType): void {
    this.colormap = colormap;

    if (this._webglContext && this._webglProgram) {
      this._applyColormapWebGL();
    } else {
      this._applyColormapCanvas2D();
    }

    this.dirty = true;
    this.canvas?.requestRenderAll();
  }

  /**
   * Override render to use colorized canvas
   */
  render(ctx: CanvasRenderingContext2D): void {
    if (this._colorizedCanvas && this.colormap !== 'grayscale') {
      // Temporarily swap the element to colorized canvas
      const originalElement = this.getElement();
      this.setElement(this._colorizedCanvas);
      super.render(ctx);
      this.setElement(originalElement as HTMLImageElement);
    } else {
      super.render(ctx);
    }
  }

  /**
   * Get serializable properties including colormap
   */
  getSerializableData(): Record<string, any> {
    return {
      colormap: this.colormap
    };
  }

  /**
   * Deserialization from JSON
   */
  static fromObject(object: Record<string, any>): Promise<DepthMapImage> {
    return new Promise((resolve, reject) => {
      if (!object.src) {
        reject(new Error('DepthMapImage requires a src property'));
        return;
      }

      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => {
        resolve(new DepthMapImage(img, {
          colormap: object.colormap,
          ...object
        }));
      };
      img.onerror = reject;
      img.src = object.src;
    });
  }

  /**
   * Create from base64 data
   */
  static fromBase64(base64: string, options: DepthMapImageOptions = {}): Promise<DepthMapImage> {
    return new Promise((resolve, reject) => {
      const img = new Image();
      img.crossOrigin = 'anonymous';
      img.onload = () => {
        resolve(new DepthMapImage(img, options));
      };
      img.onerror = reject;
      img.src = base64.startsWith('data:') ? base64 : `data:image/png;base64,${base64}`;
    });
  }
}

// CRITICAL: Register class for serialization
classRegistry.setClass(DepthMapImage);

export default DepthMapImage;
