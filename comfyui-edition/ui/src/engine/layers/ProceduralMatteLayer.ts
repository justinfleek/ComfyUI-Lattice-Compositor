/**
 * ProceduralMatteLayer - Animated Procedural Pattern Generator
 *
 * Generates animated patterns (gradients, noise, wipes, etc.) that can be
 * used as track mattes for other layers. Perfect for:
 *
 * - Animated reveals and transitions
 * - Gradient mattes for compositing
 * - Noise-based effects
 * - Geometric wipes
 *
 * All patterns are rendered to a grayscale canvas where:
 * - White = opaque/visible
 * - Black = transparent/hidden
 */

import * as THREE from "three";
import type { Layer, ProceduralMatteData } from "@/types/project";
import { assertDefined } from "@/utils/typeGuards";
import { KeyframeEvaluator } from "../animation/KeyframeEvaluator";
import { BaseLayer } from "./BaseLayer";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                              // procedural // matte // layer
// ════════════════════════════════════════════════════════════════════════════

export class ProceduralMatteLayer extends BaseLayer {
  // Matte data
  private matteData: ProceduralMatteData;

  // Display mesh
  private mesh: THREE.Mesh | null = null;
  private material: THREE.MeshBasicMaterial | null = null;
  private texture: THREE.CanvasTexture | null = null;

  // Rendering canvas (grayscale output)
  private renderCanvas: HTMLCanvasElement;
  private renderCtx: CanvasRenderingContext2D;

  // Animation evaluator
  private readonly matteEvaluator: KeyframeEvaluator;

  // Dimensions
  private width: number = 512;
  private height: number = 512;

  // Noise seed for deterministic noise
  private noiseSeed: number;

  constructor(layerData: Layer) {
    super(layerData);

    this.matteEvaluator = new KeyframeEvaluator();

    // Extract matte data
    this.matteData = this.extractMatteData(layerData);

    // Initialize random seed - use deterministic seed based on layer ID
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const seed = this.matteData.parameters.seed;
    this.noiseSeed = (seed !== null && seed !== undefined && typeof seed === "number" && Number.isFinite(seed)) ? seed : this.hashLayerId(layerData.id);

    // Create render canvas
    this.renderCanvas = document.createElement("canvas");
    this.renderCanvas.width = this.width;
    this.renderCanvas.height = this.height;
    // Type proof: getContext("2d") returns non-null for HTMLCanvasElement
    const ctx = this.renderCanvas.getContext("2d");
    if (!ctx) {
      throw new TypeError("Failed to get 2d context from HTMLCanvasElement");
    }
    this.renderCtx = ctx;

    // Create mesh
    this.createMesh();

    // Apply initial blend mode
    this.initializeBlendMode();
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Extract matte data with defaults
   */
  private extractMatteData(layerData: Layer): ProceduralMatteData {
    const data = layerData.data as ProceduralMatteData | null;

    if (!data) {
      // Create default linear gradient
      return {
        patternType: "linear_gradient",
        parameters: {},
        animation: {
          enabled: false,
          speed: {
            id: "speed",
            name: "Speed",
            type: "number",
            value: 1,
            animated: false,
            keyframes: [],
          },
          phase: {
            id: "phase",
            name: "Phase",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
          direction: {
            id: "dir",
            name: "Direction",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
        },
        inverted: false,
        levels: {
          inputBlack: {
            id: "ib",
            name: "Input Black",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
          inputWhite: {
            id: "iw",
            name: "Input White",
            type: "number",
            value: 255,
            animated: false,
            keyframes: [],
          },
          gamma: {
            id: "g",
            name: "Gamma",
            type: "number",
            value: 1,
            animated: false,
            keyframes: [],
          },
          outputBlack: {
            id: "ob",
            name: "Output Black",
            type: "number",
            value: 0,
            animated: false,
            keyframes: [],
          },
          outputWhite: {
            id: "ow",
            name: "Output White",
            type: "number",
            value: 255,
            animated: false,
            keyframes: [],
          },
        },
      };
    }

    return data;
  }

  /**
   * Create display mesh
   */
  private createMesh(): void {
    const geometry = new THREE.PlaneGeometry(this.width, this.height);

    this.texture = new THREE.CanvasTexture(this.renderCanvas);
    this.texture.minFilter = THREE.LinearFilter;
    this.texture.magFilter = THREE.LinearFilter;

    this.material = new THREE.MeshBasicMaterial({
      map: this.texture,
      transparent: true,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, this.material);
    this.mesh.name = `matte_${this.id}`;
    this.group.add(this.mesh);
  }

  /**
   * Set dimensions
   */
  setDimensions(width: number, height: number): void {
    // Validate dimensions (NaN/0 would create invalid canvas and geometry)
    const validWidth = Number.isFinite(width) && width > 0 ? width : 512;
    const validHeight = Number.isFinite(height) && height > 0 ? height : 512;

    this.width = validWidth;
    this.height = validHeight;

    this.renderCanvas.width = validWidth;
    this.renderCanvas.height = validHeight;

    // Update geometry
    if (this.mesh) {
      this.mesh.geometry.dispose();
      this.mesh.geometry = new THREE.PlaneGeometry(validWidth, validHeight);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // frame // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(frame: number): void {
    // Render the pattern for this frame
    this.renderPattern(frame);

    // Update texture
    if (this.texture) {
      this.texture.needsUpdate = true;
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    if (properties.data) {
      this.matteData = this.extractMatteData({
        ...properties,
        data: properties.data,
      } as Layer);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // pattern // rendering
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Render the pattern to the canvas
   */
  private renderPattern(frame: number): void {
    const ctx = this.renderCtx;
    const w = this.width;
    const h = this.height;

    // Clear canvas
    ctx.fillStyle = "black";
    ctx.fillRect(0, 0, w, h);

    // Get animation time (explicit types for TypeScript inference)
    const speed: number = this.matteEvaluator.evaluate(
      this.matteData.animation.speed,
      frame,
    );
    const phase: number = this.matteEvaluator.evaluate(
      this.matteData.animation.phase,
      frame,
    );
    // Use composition fps for correct animation timing (not hardcoded 60fps)
    const time = this.matteData.animation.enabled
      ? (frame * speed) / this.compositionFps + phase
      : 0;

    // Render based on pattern type
    switch (this.matteData.patternType) {
      case "linear_gradient":
        this.renderLinearGradient(ctx, w, h, frame, time);
        break;
      case "radial_gradient":
        this.renderRadialGradient(ctx, w, h, frame, time);
        break;
      case "angular_gradient":
        this.renderAngularGradient(ctx, w, h, frame, time);
        break;
      case "ramp":
        this.renderRamp(ctx, w, h, frame, time);
        break;
      case "noise":
        this.renderNoise(ctx, w, h, frame, time);
        break;
      case "checkerboard":
        this.renderCheckerboard(ctx, w, h, frame, time);
        break;
      case "circle":
        this.renderCircle(ctx, w, h, frame, time);
        break;
      case "rectangle":
        this.renderRectangle(ctx, w, h, frame, time);
        break;
      case "iris":
        this.renderIris(ctx, w, h, frame, time);
        break;
      case "radial_wipe":
        this.renderRadialWipe(ctx, w, h, frame, time);
        break;
      case "venetian_blinds":
        this.renderVenetianBlinds(ctx, w, h, frame, time);
        break;
      case "dissolve":
        this.renderDissolve(ctx, w, h, frame, time);
        break;
      case "wave":
        this.renderWave(ctx, w, h, frame, time);
        break;
      default:
        // Default to solid white
        ctx.fillStyle = "white";
        ctx.fillRect(0, 0, w, h);
    }

    // Apply levels
    this.applyLevels(frame);

    // Apply inversion
    if (this.matteData.inverted) {
      this.invertCanvas();
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                // pattern // implementations
  // ════════════════════════════════════════════════════════════════════════════

  private renderLinearGradient(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    // Type proof: angle and blend are required for linear_gradient pattern
    assertDefined(params.angle, "angle parameter is required for linear_gradient pattern");
    assertDefined(params.blend, "blend parameter is required for linear_gradient pattern");
    const angle: number =
      this.matteEvaluator.evaluate(params.angle, frame) + time * 360;
    const blend: number = this.matteEvaluator.evaluate(params.blend, frame);

    const rad = (angle * Math.PI) / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);

    // Calculate gradient endpoints
    const len = Math.max(w, h) * 1.5;
    const cx = w / 2;
    const cy = h / 2;

    const x1 = cx - (cos * len) / 2;
    const y1 = cy - (sin * len) / 2;
    const x2 = cx + (cos * len) / 2;
    const y2 = cy + (sin * len) / 2;

    const gradient = ctx.createLinearGradient(x1, y1, x2, y2);
    const blendHalf = Math.max(0.001, blend / 2);
    gradient.addColorStop(Math.max(0, 0.5 - blendHalf), "black");
    gradient.addColorStop(Math.min(1, 0.5 + blendHalf), "white");

    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, w, h);
  }

  private renderRadialGradient(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    // Type proof: centerX, centerY, and radius are required for radial_gradient pattern
    assertDefined(params.centerX, "centerX parameter is required for radial_gradient pattern");
    assertDefined(params.centerY, "centerY parameter is required for radial_gradient pattern");
    assertDefined(params.radius, "radius parameter is required for radial_gradient pattern");
    const centerX: number = this.matteEvaluator.evaluate(
      params.centerX,
      frame,
    );
    const centerY: number = this.matteEvaluator.evaluate(
      params.centerY,
      frame,
    );
    const radius: number =
      this.matteEvaluator.evaluate(params.radius, frame) + time * 0.5;
    const blend: number = params.blend
      ? this.matteEvaluator.evaluate(params.blend, frame)
      : 0.3;

    const cx = centerX * w;
    const cy = centerY * h;
    const r = (radius * Math.max(w, h)) / 2;

    const gradient = ctx.createRadialGradient(cx, cy, 0, cx, cy, r);
    gradient.addColorStop(Math.max(0, 1 - blend), "white");
    gradient.addColorStop(1, "black");

    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, w, h);
  }

  private renderAngularGradient(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const centerX: number = params.centerX
      ? this.matteEvaluator.evaluate(params.centerX, frame)
      : 0.5;
    const centerY: number = params.centerY
      ? this.matteEvaluator.evaluate(params.centerY, frame)
      : 0.5;
    const rotation: number =
      (params.angle ? this.matteEvaluator.evaluate(params.angle, frame) : 0) +
      time * 360;

    const cx = centerX * w;
    const cy = centerY * h;
    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;

    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const dx = x - cx;
        const dy = y - cy;
        let angle = (Math.atan2(dy, dx) * 180) / Math.PI + rotation;
        angle = ((angle % 360) + 360) % 360;
        const value = Math.round((angle / 360) * 255);
        const idx = (y * w + x) * 4;
        data[idx] = data[idx + 1] = data[idx + 2] = value;
        data[idx + 3] = 255;
      }
    }

    ctx.putImageData(imageData, 0, 0);
  }

  private renderRamp(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    // Type proof: progress is required for ramp pattern
    assertDefined(params.progress, "progress parameter is required for ramp pattern");
    const progress: number = this.matteEvaluator.evaluate(
      params.progress,
      frame,
    );
    const softness: number = params.softness
      ? this.matteEvaluator.evaluate(params.softness, frame)
      : 0.1;
    const angle: number = params.angle
      ? this.matteEvaluator.evaluate(params.angle, frame)
      : 0;

    const animProgress: number = this.matteData.animation.enabled
      ? (progress + time) % 1
      : progress;

    const rad = (angle * Math.PI) / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);

    const len = Math.max(w, h) * 1.5;
    const cx = w / 2;
    const cy = h / 2;

    const x1 = cx - (cos * len) / 2;
    const y1 = cy - (sin * len) / 2;
    const x2 = cx + (cos * len) / 2;
    const y2 = cy + (sin * len) / 2;

    const gradient = ctx.createLinearGradient(x1, y1, x2, y2);
    const soft = Math.max(0.001, softness / 2);
    gradient.addColorStop(Math.max(0, animProgress - soft), "black");
    gradient.addColorStop(Math.min(1, animProgress + soft), "white");

    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, w, h);
  }

  private renderNoise(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const scale: number = params.scale
      ? this.matteEvaluator.evaluate(params.scale, frame)
      : 50;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const octaves = (typeof params.octaves === "number" && Number.isFinite(params.octaves) && params.octaves > 0) ? params.octaves : 4;

    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;
    const timeOffset = time * 10;

    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        let noise = 0;
        let amp = 1;
        let freq = 1 / scale;

        for (let o = 0; o < octaves; o++) {
          noise += this.perlinNoise(x * freq + timeOffset, y * freq) * amp;
          amp *= 0.5;
          freq *= 2;
        }

        // Normalize to 0-255
        const value = Math.round(((noise + 1) / 2) * 255);
        const idx = (y * w + x) * 4;
        data[idx] = data[idx + 1] = data[idx + 2] = value;
        data[idx + 3] = 255;
      }
    }

    ctx.putImageData(imageData, 0, 0);
  }

  private renderCheckerboard(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const tilesX: number = params.tilesX
      ? this.matteEvaluator.evaluate(params.tilesX, frame)
      : 8;
    const tilesY: number = params.tilesY
      ? this.matteEvaluator.evaluate(params.tilesY, frame)
      : 8;
    const rotation: number = params.rotation
      ? this.matteEvaluator.evaluate(params.rotation, frame)
      : 0;

    const tileW = w / tilesX;
    const tileH = h / tilesY;
    const offset = time * tileW;

    ctx.save();
    ctx.translate(w / 2, h / 2);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.translate(-w / 2 - offset, -h / 2);

    for (let y = -1; y <= tilesY + 1; y++) {
      for (let x = -1; x <= tilesX + 1; x++) {
        const isWhite = (x + y) % 2 === 0;
        ctx.fillStyle = isWhite ? "white" : "black";
        ctx.fillRect(x * tileW, y * tileH, tileW, tileH);
      }
    }

    ctx.restore();
  }

  private renderCircle(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const centerX: number = params.centerX
      ? this.matteEvaluator.evaluate(params.centerX, frame)
      : 0.5;
    const centerY: number = params.centerY
      ? this.matteEvaluator.evaluate(params.centerY, frame)
      : 0.5;
    const radius: number = params.radius
      ? this.matteEvaluator.evaluate(params.radius, frame)
      : 0.5;
    const feather: number = params.feather
      ? this.matteEvaluator.evaluate(params.feather, frame)
      : 0;

    const cx = centerX * w;
    const cy = centerY * h;
    const r = ((radius + time * 0.5) * Math.min(w, h)) / 2;

    if (feather > 0) {
      const gradient = ctx.createRadialGradient(
        cx,
        cy,
        Math.max(0, r - feather * 50),
        cx,
        cy,
        r,
      );
      gradient.addColorStop(0, "white");
      gradient.addColorStop(1, "black");
      ctx.fillStyle = gradient;
      ctx.fillRect(0, 0, w, h);
    } else {
      ctx.fillStyle = "white";
      ctx.beginPath();
      ctx.arc(cx, cy, r, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  private renderRectangle(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const centerX: number = params.centerX
      ? this.matteEvaluator.evaluate(params.centerX, frame)
      : 0.5;
    const centerY: number = params.centerY
      ? this.matteEvaluator.evaluate(params.centerY, frame)
      : 0.5;
    const rectWidth: number = params.width
      ? this.matteEvaluator.evaluate(params.width, frame)
      : 0.5;
    const rectHeight: number = params.height
      ? this.matteEvaluator.evaluate(params.height, frame)
      : 0.5;
    const cornerRadius: number = params.cornerRadius
      ? this.matteEvaluator.evaluate(params.cornerRadius, frame)
      : 0;

    const cx = centerX * w;
    const cy = centerY * h;
    const rw = (rectWidth + time * 0.2) * w;
    const rh = (rectHeight + time * 0.2) * h;
    const cr = (cornerRadius * Math.min(rw, rh)) / 2;

    ctx.fillStyle = "white";
    ctx.beginPath();
    ctx.roundRect(cx - rw / 2, cy - rh / 2, rw, rh, cr);
    ctx.fill();
  }

  private renderIris(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const progress: number = params.progress
      ? this.matteEvaluator.evaluate(params.progress, frame)
      : 0.5;
    const feather: number = params.feather
      ? this.matteEvaluator.evaluate(params.feather, frame)
      : 0.1;
    const centerX: number = params.centerX
      ? this.matteEvaluator.evaluate(params.centerX, frame)
      : 0.5;
    const centerY: number = params.centerY
      ? this.matteEvaluator.evaluate(params.centerY, frame)
      : 0.5;

    const animProgress: number = this.matteData.animation.enabled
      ? (progress + time) % 1
      : progress;
    const cx = centerX * w;
    const cy = centerY * h;
    const maxRadius = Math.sqrt(w * w + h * h) / 2;
    const r = animProgress * maxRadius;

    const gradient = ctx.createRadialGradient(
      cx,
      cy,
      Math.max(0, r - feather * 100),
      cx,
      cy,
      r,
    );
    gradient.addColorStop(0, "white");
    gradient.addColorStop(1, "black");

    ctx.fillStyle = gradient;
    ctx.fillRect(0, 0, w, h);
  }

  private renderRadialWipe(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const progress: number = params.progress
      ? this.matteEvaluator.evaluate(params.progress, frame)
      : 0.5;
    const centerX: number = params.centerX
      ? this.matteEvaluator.evaluate(params.centerX, frame)
      : 0.5;
    const centerY: number = params.centerY
      ? this.matteEvaluator.evaluate(params.centerY, frame)
      : 0.5;
    const softness: number = params.softness
      ? this.matteEvaluator.evaluate(params.softness, frame)
      : 0.05;

    const animProgress: number = this.matteData.animation.enabled
      ? (progress + time) % 1
      : progress;
    const cx = centerX * w;
    const cy = centerY * h;
    const angle = animProgress * Math.PI * 2;

    // Render clock wipe using image data for precision
    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;

    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const pixelAngle = Math.atan2(dy, dx) + Math.PI; // 0 to 2PI
        const diff = pixelAngle - angle;
        const dist =
          Math.abs(((diff + Math.PI * 3) % (Math.PI * 2)) - Math.PI) / Math.PI;

        let value = dist < 0.5 ? 255 : 0;
        if (softness > 0) {
          const soft = softness * Math.PI;
          if (Math.abs(dist - 0.5) < soft) {
            value = Math.round(255 * (1 - (dist - 0.5 + soft) / (soft * 2)));
          }
        }

        const idx = (y * w + x) * 4;
        data[idx] = data[idx + 1] = data[idx + 2] = value;
        data[idx + 3] = 255;
      }
    }

    ctx.putImageData(imageData, 0, 0);
  }

  private renderVenetianBlinds(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const progress = params.progress
      ? this.matteEvaluator.evaluate(params.progress, frame)
      : 0.5;
    const slats = params.slats
      ? this.matteEvaluator.evaluate(params.slats, frame)
      : 10;
    const angle = params.angle
      ? this.matteEvaluator.evaluate(params.angle, frame)
      : 0;

    const animProgress = this.matteData.animation.enabled
      ? (progress + time) % 1
      : progress;
    const slatHeight = h / slats;
    const openAmount = animProgress * slatHeight;

    ctx.save();
    ctx.translate(w / 2, h / 2);
    ctx.rotate((angle * Math.PI) / 180);
    ctx.translate(-w / 2, -h / 2);

    for (let i = 0; i < slats; i++) {
      ctx.fillStyle = "white";
      ctx.fillRect(0, i * slatHeight, w, openAmount);
    }

    ctx.restore();
  }

  private renderDissolve(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const progress = params.progress
      ? this.matteEvaluator.evaluate(params.progress, frame)
      : 0.5;
    const blockSize = params.blockSize
      ? this.matteEvaluator.evaluate(params.blockSize, frame)
      : 4;

    const animProgress = this.matteData.animation.enabled
      ? (progress + time) % 1
      : progress;
    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;

    // Generate pseudo-random pattern based on seed
    const blocksX = Math.ceil(w / blockSize);
    const blocksY = Math.ceil(h / blockSize);

    for (let by = 0; by < blocksY; by++) {
      for (let bx = 0; bx < blocksX; bx++) {
        // Deterministic random based on position and seed
        const random = this.hash(bx + by * blocksX + this.noiseSeed);
        const isVisible = random < animProgress;

        const value = isVisible ? 255 : 0;

        // Fill block
        for (let dy = 0; dy < blockSize && by * blockSize + dy < h; dy++) {
          for (let dx = 0; dx < blockSize && bx * blockSize + dx < w; dx++) {
            const x = bx * blockSize + dx;
            const y = by * blockSize + dy;
            const idx = (y * w + x) * 4;
            data[idx] = data[idx + 1] = data[idx + 2] = value;
            data[idx + 3] = 255;
          }
        }
      }
    }

    ctx.putImageData(imageData, 0, 0);
  }

  private renderWave(
    ctx: CanvasRenderingContext2D,
    w: number,
    h: number,
    frame: number,
    time: number,
  ): void {
    const params = this.matteData.parameters;
    const frequency = params.frequency
      ? this.matteEvaluator.evaluate(params.frequency, frame)
      : 4;
    const amplitude = params.amplitude
      ? this.matteEvaluator.evaluate(params.amplitude, frame)
      : 0.5;
    const angle = params.angle
      ? this.matteEvaluator.evaluate(params.angle, frame)
      : 0;
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    const waveType = (typeof params.waveType === "string" && params.waveType.length > 0) ? params.waveType : "sine";

    const imageData = ctx.getImageData(0, 0, w, h);
    const data = imageData.data;
    const rad = (angle * Math.PI) / 180;

    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        // Rotate coordinates
        const rx = (x - w / 2) * Math.cos(rad) - (y - h / 2) * Math.sin(rad);

        // Calculate wave
        const phase = ((rx / w) * frequency + time) * Math.PI * 2;
        let wave: number;

        switch (waveType) {
          case "triangle":
            wave = Math.abs(((phase / Math.PI) % 2) - 1) * 2 - 1;
            break;
          case "square":
            wave = Math.sin(phase) >= 0 ? 1 : -1;
            break;
          case "sawtooth":
            wave = ((phase / Math.PI) % 2) - 1;
            break;
          default: // sine
            wave = Math.sin(phase);
        }

        const value = Math.round(((wave * amplitude + 1) / 2) * 255);
        const idx = (y * w + x) * 4;
        data[idx] = data[idx + 1] = data[idx + 2] = value;
        data[idx + 3] = 255;
      }
    }

    ctx.putImageData(imageData, 0, 0);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                      // post
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Apply levels adjustment
   */
  private applyLevels(frame: number): void {
    const levels = this.matteData.levels;
    const inputBlack = this.matteEvaluator.evaluate(levels.inputBlack, frame);
    const inputWhite = this.matteEvaluator.evaluate(levels.inputWhite, frame);
    const gamma = this.matteEvaluator.evaluate(levels.gamma, frame);
    const outputBlack = this.matteEvaluator.evaluate(levels.outputBlack, frame);
    const outputWhite = this.matteEvaluator.evaluate(levels.outputWhite, frame);

    // Validate values (NaN would corrupt image processing)
    const validInputBlack = Number.isFinite(inputBlack) ? inputBlack : 0;
    const validInputWhite = Number.isFinite(inputWhite) ? inputWhite : 255;
    const validGamma = Number.isFinite(gamma) && gamma > 0 ? gamma : 1;
    const validOutputBlack = Number.isFinite(outputBlack) ? outputBlack : 0;
    const validOutputWhite = Number.isFinite(outputWhite) ? outputWhite : 255;

    // Skip if default values
    if (
      validInputBlack === 0 &&
      validInputWhite === 255 &&
      validGamma === 1 &&
      validOutputBlack === 0 &&
      validOutputWhite === 255
    ) {
      return;
    }

    const imageData = this.renderCtx.getImageData(
      0,
      0,
      this.width,
      this.height,
    );
    const data = imageData.data;
    // Guard against division by zero (when inputWhite === inputBlack)
    const inputRange = Math.max(1, validInputWhite - validInputBlack);
    const outputRange = validOutputWhite - validOutputBlack;

    for (let i = 0; i < data.length; i += 4) {
      let value = data[i];

      // Input levels
      value = Math.max(
        0,
        Math.min(255, ((value - validInputBlack) / inputRange) * 255),
      );

      // Gamma correction
      value = (value / 255) ** (1 / validGamma) * 255;

      // Output levels
      value = validOutputBlack + (value / 255) * outputRange;

      data[i] = data[i + 1] = data[i + 2] = Math.round(value);
    }

    this.renderCtx.putImageData(imageData, 0, 0);
  }

  /**
   * Invert the canvas
   */
  private invertCanvas(): void {
    const imageData = this.renderCtx.getImageData(
      0,
      0,
      this.width,
      this.height,
    );
    const data = imageData.data;

    for (let i = 0; i < data.length; i += 4) {
      data[i] = 255 - data[i];
      data[i + 1] = 255 - data[i + 1];
      data[i + 2] = 255 - data[i + 2];
    }

    this.renderCtx.putImageData(imageData, 0, 0);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // utility // functions
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Simple deterministic hash function
   */
  private hash(n: number): number {
    const x = Math.sin(n) * 43758.5453123;
    return x - Math.floor(x);
  }

  /**
   * Hash a layer ID string to a number for deterministic seeding
   */
  private hashLayerId(id: string): number {
    let hash = 0;
    for (let i = 0; i < id.length; i++) {
      const char = id.charCodeAt(i);
      hash = (hash << 5) - hash + char;
      hash = hash & hash; // Convert to 32bit integer
    }
    return Math.abs(hash) % 65536;
  }

  /**
   * Simple 2D Perlin noise approximation
   */
  private perlinNoise(x: number, y: number): number {
    const xi = Math.floor(x);
    const yi = Math.floor(y);
    const xf = x - xi;
    const yf = y - yi;

    const tl = this.hash(xi + yi * 57 + this.noiseSeed);
    const tr = this.hash(xi + 1 + yi * 57 + this.noiseSeed);
    const bl = this.hash(xi + (yi + 1) * 57 + this.noiseSeed);
    const br = this.hash(xi + 1 + (yi + 1) * 57 + this.noiseSeed);

    // Smoothstep
    const u = xf * xf * (3 - 2 * xf);
    const v = yf * yf * (3 - 2 * yf);

    // Bilinear interpolation
    return (
      (tl + u * (tr - tl) + v * (bl - tl) + u * v * (tl - tr - bl + br)) * 2 - 1
    );
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                          // source // canvas
  // ════════════════════════════════════════════════════════════════════════════

  // Throw explicit error if render canvas is missing
  protected getSourceCanvas(): HTMLCanvasElement {
    const hasRenderCanvas = typeof this.renderCanvas === "object" && this.renderCanvas !== null;
    if (!hasRenderCanvas) {
      throw new Error(`[ProceduralMatteLayer] Layer "${this.id}" cannot provide source canvas: renderCanvas is null. Render canvas creation failed. This is a rendering system error.`);
    }
    return this.renderCanvas;
  }

  protected applyProcessedEffects(processedCanvas: HTMLCanvasElement): void {
    // Copy processed canvas back to render canvas
    this.renderCtx.clearRect(0, 0, this.width, this.height);
    this.renderCtx.drawImage(processedCanvas, 0, 0);

    // Update texture
    if (this.texture) {
      this.texture.needsUpdate = true;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                  // disposal
  // ════════════════════════════════════════════════════════════════════════════

  protected onDispose(): void {
    if (this.texture) {
      this.texture.dispose();
      this.texture = null;
    }

    if (this.material) {
      this.material.dispose();
      this.material = null;
    }

    if (this.mesh) {
      this.mesh.geometry.dispose();
      this.mesh = null;
    }
  }
}
