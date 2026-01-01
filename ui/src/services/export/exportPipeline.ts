/**
 * Export Pipeline
 * Orchestrates the full export process from compositor to ComfyUI
 */

import type {
  ExportConfig,
  ExportResult,
  ExportProgress,
  ExportTarget,
  GenerationProgress,
  DepthMapFormat,
} from '@/types/export';
import type { Layer } from '@/types/project';
import type { CameraKeyframe, Camera3D } from '@/types/camera';

import { renderDepthFrame, convertDepthToFormat, depthToImageData, exportDepthSequence } from './depthRenderer';
import { exportCameraForTarget } from './cameraExportFormats';
import { getComfyUIClient } from '@/services/comfyui/comfyuiClient';
import { generateWorkflowForTarget, validateWorkflow, type WorkflowParams } from '@/services/comfyui/workflowTemplates';
import { EXPORT_PRESETS, DEPTH_FORMAT_SPECS } from '@/config/exportPresets';
import { evaluateLayerCached } from '@/services/layerEvaluationCache';
import type { EvaluatedLayer } from '@/engine/MotionEngine';
import type { LatticeEngine } from '@/engine/LatticeEngine';
import type { EncodedVideo } from './videoEncoder';

// ============================================================================
// Types
// ============================================================================

export interface ExportPipelineOptions {
  layers: Layer[];
  cameraKeyframes: CameraKeyframe[];
  config: ExportConfig;
  onProgress?: (progress: ExportProgress) => void;
  abortSignal?: AbortSignal;
  /** LatticeEngine instance for video export (TTM, Uni3C) */
  engine?: LatticeEngine;
}

export interface RenderedFrame {
  frameIndex: number;
  timestamp: number;
  colorCanvas?: OffscreenCanvas;
  depthCanvas?: OffscreenCanvas;
  depthBuffer?: Float32Array;
}

// ============================================================================
// Export Pipeline Class
// ============================================================================

export class ExportPipeline {
  private layers: Layer[];
  private cameraKeyframes: CameraKeyframe[];
  private config: ExportConfig;
  private onProgress: (progress: ExportProgress) => void;
  private abortSignal?: AbortSignal;
  private aborted = false;
  private engine?: LatticeEngine;

  constructor(options: ExportPipelineOptions) {
    this.layers = options.layers;
    this.cameraKeyframes = options.cameraKeyframes;
    this.config = options.config;
    this.onProgress = options.onProgress || (() => {});
    this.abortSignal = options.abortSignal;
    this.engine = options.engine;

    if (this.abortSignal) {
      this.abortSignal.addEventListener('abort', () => {
        this.aborted = true;
      });
    }
  }

  private checkAborted(): void {
    if (this.aborted) {
      throw new Error('Export aborted');
    }
  }

  private updateProgress(progress: Partial<ExportProgress>): void {
    this.onProgress({
      stage: 'preparing',
      stageProgress: 0,
      overallProgress: 0,
      message: '',
      ...progress,
    });
  }

  // ============================================================================
  // Error Handling Utilities
  // ============================================================================

  /**
   * Safely get 2D rendering context from canvas
   * @throws Error if context cannot be obtained
   */
  private get2DContext(canvas: OffscreenCanvas, operation: string): OffscreenCanvasRenderingContext2D {
    const ctx = canvas.getContext('2d');
    if (!ctx) {
      throw new Error(`Failed to get 2D context for ${operation}. Browser may not support OffscreenCanvas.`);
    }
    return ctx;
  }

  /**
   * Validate a numeric value is finite and not NaN
   */
  private validateNumber(value: unknown, name: string, defaultValue: number): number {
    if (typeof value !== 'number' || !Number.isFinite(value)) {
      console.warn(`[ExportPipeline] Invalid ${name}: ${value}, using default ${defaultValue}`);
      return defaultValue;
    }
    return value;
  }

  /**
   * Clamp a value to a safe range
   */
  private clamp(value: number, min: number, max: number): number {
    return Math.max(min, Math.min(max, value));
  }

  // ============================================================================
  // Main Export Method
  // ============================================================================

  async execute(): Promise<ExportResult> {
    const startTime = Date.now();
    const result: ExportResult = {
      success: false,
      outputFiles: {},
      errors: [],
      warnings: [],
      duration: 0,
    };

    try {
      this.updateProgress({
        stage: 'preparing',
        stageProgress: 0,
        overallProgress: 0,
        message: 'Preparing export...',
      });

      // Validate config
      const configErrors = this.validateConfig();
      if (configErrors.length > 0) {
        result.errors = configErrors;
        return result;
      }

      // Step 1: Render reference frame
      if (this.config.exportReferenceFrame) {
        this.checkAborted();
        await this.renderReferenceFrame(result);
      }

      // Step 2: Render last frame (for first+last workflows)
      if (this.config.exportLastFrame) {
        this.checkAborted();
        await this.renderLastFrame(result);
      }

      // Step 3: Render depth sequence
      if (this.config.exportDepthMap) {
        this.checkAborted();
        await this.renderDepthSequence(result);
      }

      // Step 4: Render control images
      if (this.config.exportControlImages) {
        this.checkAborted();
        await this.renderControlSequence(result);
      }

      // Step 5: Export scene video (SCAIL pose, Uni3C camera)
      if (this.config.exportSceneVideo) {
        this.checkAborted();
        await this.renderSceneVideo(result);
      }

      // Step 6: Export mask video (TTM)
      if (this.config.exportMaskVideo && this.config.maskLayerId) {
        this.checkAborted();
        await this.renderMaskVideo(result);
      }

      // Step 7: Export camera data
      if (this.config.exportCameraData) {
        this.checkAborted();
        await this.exportCameraData(result);
      }

      // Step 8: Generate workflow
      this.checkAborted();
      await this.generateWorkflow(result);

      // Step 7: Queue workflow if auto-queue enabled
      if (this.config.autoQueueWorkflow && this.config.comfyuiServer) {
        this.checkAborted();
        await this.queueWorkflow(result);
      }

      result.success = result.errors.length === 0;

    } catch (error) {
      if (error instanceof Error && error.message === 'Export aborted') {
        result.errors.push('Export was cancelled');
      } else {
        result.errors.push(error instanceof Error ? error.message : 'Unknown error');
      }
    }

    result.duration = Date.now() - startTime;
    return result;
  }

  // ============================================================================
  // Validation
  // ============================================================================

  private validateConfig(): string[] {
    const errors: string[] = [];

    // Validate dimensions
    if (!Number.isFinite(this.config.width) || this.config.width < 64 || this.config.width > 4096) {
      errors.push(`Width must be between 64 and 4096 (got: ${this.config.width})`);
    }

    if (!Number.isFinite(this.config.height) || this.config.height < 64 || this.config.height > 4096) {
      errors.push(`Height must be between 64 and 4096 (got: ${this.config.height})`);
    }

    // Validate dimensions are integers
    if (this.config.width !== Math.floor(this.config.width)) {
      errors.push('Width must be an integer');
    }
    if (this.config.height !== Math.floor(this.config.height)) {
      errors.push('Height must be an integer');
    }

    // Validate frame settings
    if (!Number.isFinite(this.config.frameCount) || this.config.frameCount < 1 || this.config.frameCount > 1000) {
      errors.push(`Frame count must be between 1 and 1000 (got: ${this.config.frameCount})`);
    }

    if (!Number.isFinite(this.config.fps) || this.config.fps < 1 || this.config.fps > 120) {
      errors.push(`FPS must be between 1 and 120 (got: ${this.config.fps})`);
    }

    // Validate frame range
    if (!Number.isFinite(this.config.startFrame) || this.config.startFrame < 0) {
      errors.push(`Start frame must be >= 0 (got: ${this.config.startFrame})`);
    }

    if (!Number.isFinite(this.config.endFrame)) {
      errors.push(`End frame must be a valid number (got: ${this.config.endFrame})`);
    }

    if (this.config.startFrame >= this.config.endFrame) {
      errors.push(`Start frame (${this.config.startFrame}) must be less than end frame (${this.config.endFrame})`);
    }

    if (this.config.endFrame > this.config.frameCount) {
      errors.push(`End frame (${this.config.endFrame}) exceeds frame count (${this.config.frameCount})`);
    }

    // Validate mask layer ID if mask export requested
    if (this.config.exportMaskVideo && !this.config.maskLayerId) {
      errors.push('Mask video export requires maskLayerId in config');
    }

    // Validate prompt
    if (this.needsPrompt()) {
      const trimmedPrompt = (this.config.prompt || '').trim();
      if (!trimmedPrompt) {
        errors.push('Prompt is required for this export target (cannot be empty or whitespace-only)');
      }
    }

    // Validate optional numeric fields
    if (this.config.seed !== undefined && (!Number.isFinite(this.config.seed) || this.config.seed < 0)) {
      errors.push(`Seed must be a non-negative number (got: ${this.config.seed})`);
    }

    if (this.config.steps !== undefined && (!Number.isFinite(this.config.steps) || this.config.steps < 1 || this.config.steps > 150)) {
      errors.push(`Steps must be between 1 and 150 (got: ${this.config.steps})`);
    }

    if (this.config.cfgScale !== undefined && (!Number.isFinite(this.config.cfgScale) || this.config.cfgScale < 0 || this.config.cfgScale > 30)) {
      errors.push(`CFG scale must be between 0 and 30 (got: ${this.config.cfgScale})`);
    }

    return errors;
  }

  private needsPrompt(): boolean {
    const noPromptTargets: ExportTarget[] = ['controlnet-depth', 'controlnet-canny', 'controlnet-lineart'];
    return !noPromptTargets.includes(this.config.target);
  }

  // ============================================================================
  // Frame Rendering
  // ============================================================================

  private async renderReferenceFrame(result: ExportResult): Promise<void> {
    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 5,
      message: 'Rendering reference frame...',
    });

    const canvas = new OffscreenCanvas(this.config.width, this.config.height);
    const ctx = this.get2DContext(canvas, 'reference frame rendering');

    // Render the first frame
    await this.renderFrameToCanvas(ctx, this.config.startFrame);

    // Convert to blob and save
    const blob = await canvas.convertToBlob({ type: 'image/png' });
    const filename = `${this.config.filenamePrefix || 'export'}_reference.png`;

    // If ComfyUI server is configured, upload
    if (this.config.comfyuiServer) {
      try {
        const client = getComfyUIClient(this.config.comfyuiServer);
        const uploadResult = await client.uploadImage(blob, filename);
        result.outputFiles.referenceImage = uploadResult.name;
      } catch (error) {
        result.errors.push(`Failed to upload reference frame: ${error instanceof Error ? error.message : 'Unknown error'}`);
        // Fall back to local save
        result.outputFiles.referenceImage = await this.saveBlobLocally(blob, filename);
        result.warnings.push('Reference frame saved locally due to upload failure');
      }
    } else {
      // Save locally (browser download)
      result.outputFiles.referenceImage = await this.saveBlobLocally(blob, filename);
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 100,
      overallProgress: 10,
      message: 'Reference frame complete',
    });
  }

  private async renderLastFrame(result: ExportResult): Promise<void> {
    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 12,
      message: 'Rendering last frame...',
    });

    const canvas = new OffscreenCanvas(this.config.width, this.config.height);
    const ctx = this.get2DContext(canvas, 'last frame rendering');

    // Render the last frame (endFrame is exclusive, so use endFrame - 1)
    const lastFrameIndex = Math.max(this.config.startFrame, this.config.endFrame - 1);
    await this.renderFrameToCanvas(ctx, lastFrameIndex);

    // Convert to blob and save
    const blob = await canvas.convertToBlob({ type: 'image/png' });
    const filename = `${this.config.filenamePrefix || 'export'}_last.png`;

    if (this.config.comfyuiServer) {
      try {
        const client = getComfyUIClient(this.config.comfyuiServer);
        const uploadResult = await client.uploadImage(blob, filename);
        result.outputFiles.lastImage = uploadResult.name;
      } catch (error) {
        result.errors.push(`Failed to upload last frame: ${error instanceof Error ? error.message : 'Unknown error'}`);
        result.outputFiles.lastImage = await this.saveBlobLocally(blob, filename);
        result.warnings.push('Last frame saved locally due to upload failure');
      }
    } else {
      result.outputFiles.lastImage = await this.saveBlobLocally(blob, filename);
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 100,
      overallProgress: 15,
      message: 'Last frame complete',
    });
  }

  private async renderFrameToCanvas(
    ctx: OffscreenCanvasRenderingContext2D,
    frameIndex: number
  ): Promise<void> {
    // Clear canvas
    ctx.clearRect(0, 0, ctx.canvas.width, ctx.canvas.height);

    // Sort layers by z-index (back to front)
    const sortedLayers = [...this.layers]
      .filter(layer => layer.visible)
      .sort((a, b) => {
        const az = a.transform?.position?.value?.z ?? 0;
        const bz = b.transform?.position?.value?.z ?? 0;
        return az - bz;
      });

    // Render each layer
    for (const layer of sortedLayers) {
      await this.renderLayerToCanvas(ctx, layer, frameIndex);
    }
  }

  private async renderLayerToCanvas(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    frameIndex: number
  ): Promise<void> {
    // CRITICAL FIX: Evaluate layer properties with keyframes, expressions, and data-driven values
    // Previously this used static .value which ignored all animation
    // BUG-038 FIX: Pass fps from config to ensure expressions evaluate with correct time
    const evaluated = evaluateLayerCached(layer, frameIndex, this.config.fps);

    // Skip if layer is not visible at this frame
    if (!evaluated.visible) {
      return;
    }

    // Get evaluated transform (includes keyframe interpolation + expressions)
    const pos = evaluated.transform.position;
    const scaleVal = evaluated.transform.scale;
    const rotation = typeof evaluated.transform.rotation === 'number'
      ? evaluated.transform.rotation
      : (evaluated.transform.rotation as any)?.z ?? 0;
    const opacity = evaluated.opacity;

    // Validate transform values - protect against NaN/Infinity from bad expressions
    const safeOpacity = this.clamp(this.validateNumber(opacity, `layer ${layer.id} opacity`, 100), 0, 100);
    const safePosX = this.validateNumber(pos.x, `layer ${layer.id} position.x`, 0);
    const safePosY = this.validateNumber(pos.y, `layer ${layer.id} position.y`, 0);
    const safeRotation = this.validateNumber(rotation, `layer ${layer.id} rotation`, 0);
    const safeScaleX = this.validateNumber(scaleVal.x, `layer ${layer.id} scale.x`, 100);
    const safeScaleY = this.validateNumber(scaleVal.y, `layer ${layer.id} scale.y`, 100);

    ctx.save();

    // Apply transforms with validated values
    ctx.globalAlpha = safeOpacity / 100;
    ctx.translate(safePosX, safePosY);
    ctx.rotate((safeRotation * Math.PI) / 180);
    ctx.scale(safeScaleX / 100, safeScaleY / 100);

    // Draw layer content
    const layerData = layer.data as any;
    if (layer.type === 'image' && layerData?.src) {
      // Create image from content URL
      const img = await this.loadImage(layerData.src);
      ctx.drawImage(img, -img.width / 2, -img.height / 2);
    } else if (layer.type === 'solid' && layerData?.color) {
      ctx.fillStyle = layerData.color || '#000000';
      const width = layerData.width ?? 100;
      const height = layerData.height ?? 100;
      ctx.fillRect(-width / 2, -height / 2, width, height);
    } else if (layer.type === 'text' && layerData?.text) {
      // Render text with evaluated properties
      const textContent = evaluated.properties.textContent ?? layerData.text;
      const fontSize = evaluated.properties.fontSize ?? layerData.fontSize ?? 48;
      const fontFamily = layerData.fontFamily ?? 'Arial';
      const fillColor = layerData.fillColor ?? '#ffffff';

      ctx.fillStyle = fillColor;
      ctx.font = `${fontSize}px ${fontFamily}`;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(String(textContent), 0, 0);
    }

    ctx.restore();
  }

  private loadImage(src: string, timeoutMs: number = 30000): Promise<HTMLImageElement> {
    return new Promise((resolve, reject) => {
      const img = new Image();
      let timeoutId: ReturnType<typeof setTimeout> | null = null;

      const cleanup = () => {
        if (timeoutId) {
          clearTimeout(timeoutId);
          timeoutId = null;
        }
        img.onload = null;
        img.onerror = null;
      };

      img.onload = () => {
        cleanup();
        resolve(img);
      };

      img.onerror = (event) => {
        cleanup();
        reject(new Error(`Failed to load image: ${src.substring(0, 100)}${src.length > 100 ? '...' : ''}`));
      };

      // Set timeout to prevent hanging on slow/broken URLs
      timeoutId = setTimeout(() => {
        cleanup();
        // Abort image loading by clearing src
        img.src = '';
        reject(new Error(`Image load timeout after ${timeoutMs}ms: ${src.substring(0, 50)}...`));
      }, timeoutMs);

      // Handle data URLs and blob URLs specially
      if (src.startsWith('data:') || src.startsWith('blob:')) {
        img.src = src;
      } else {
        // For regular URLs, set crossOrigin to handle CORS
        img.crossOrigin = 'anonymous';
        img.src = src;
      }
    });
  }

  // ============================================================================
  // Depth Sequence Rendering
  // ============================================================================

  private async renderDepthSequence(result: ExportResult): Promise<void> {
    const frameCount = this.config.endFrame - this.config.startFrame;
    const depthFiles: string[] = [];

    // Use engine depth capture if available (proper Three.js depth buffer)
    // Otherwise fall back to manual layer-based depth calculation
    const useEngineDepth = this.engine !== undefined;

    if (useEngineDepth && this.engine) {
      // Store original state
      const originalFrame = this.engine.getState().currentFrame;

      for (let i = 0; i < frameCount; i++) {
        this.checkAborted();

        const frameIndex = this.config.startFrame + i;
        const progress = (i / frameCount) * 100;

        this.updateProgress({
          stage: 'rendering_depth',
          stageProgress: progress,
          overallProgress: 15 + (progress * 0.25),
          currentFrame: i + 1,
          totalFrames: frameCount,
          message: `Rendering depth frame ${i + 1}/${frameCount} (Three.js)`,
        });

        // Set frame and render
        this.engine.setFrame(frameIndex);

        // Capture depth from Three.js depth buffer
        const depthCapture = this.engine.captureDepth();

        // Convert to format-specific depth
        const convertedDepth = convertDepthToFormat(
          {
            depthBuffer: depthCapture.depthBuffer,
            width: depthCapture.width,
            height: depthCapture.height,
            minDepth: depthCapture.near,
            maxDepth: depthCapture.far,
          },
          this.config.depthFormat
        );

        // Create image data
        const imageData = depthToImageData(
          convertedDepth,
          depthCapture.width,
          depthCapture.height
        );

        // Convert to canvas and blob
        const canvas = new OffscreenCanvas(depthCapture.width, depthCapture.height);
        const ctx = this.get2DContext(canvas, `depth frame ${i} rendering`);
        ctx.putImageData(imageData, 0, 0);

        const blob = await canvas.convertToBlob({ type: 'image/png' });
        const filename = `${this.config.filenamePrefix}_depth_${String(i).padStart(5, '0')}.png`;

        if (this.config.comfyuiServer) {
          try {
            const client = getComfyUIClient(this.config.comfyuiServer);
            const uploadResult = await client.uploadImage(blob, filename, 'input', 'depth_sequence');
            depthFiles.push(uploadResult.name);
          } catch (error) {
            // Fall back to local save on upload failure
            console.warn(`[ExportPipeline] Depth frame ${i} upload failed, saving locally:`, error);
            depthFiles.push(await this.saveBlobLocally(blob, filename));
          }
        } else {
          depthFiles.push(await this.saveBlobLocally(blob, filename));
        }
      }

      // Restore original frame
      this.engine.setFrame(originalFrame);
    } else {
      // Fallback: manual layer-based depth calculation
      for (let i = 0; i < frameCount; i++) {
        this.checkAborted();

        const frameIndex = this.config.startFrame + i;
        const progress = (i / frameCount) * 100;

        this.updateProgress({
          stage: 'rendering_depth',
          stageProgress: progress,
          overallProgress: 15 + (progress * 0.25),
          currentFrame: i + 1,
          totalFrames: frameCount,
          message: `Rendering depth frame ${i + 1}/${frameCount} (layer-based)`,
        });

        // Use default camera for manual depth calculation
        const defaultCamera: Camera3D = {
          id: 'default',
          name: 'Default Camera',
          type: 'one-node',
          position: { x: 0, y: 0, z: 1000 },
          pointOfInterest: { x: 0, y: 0, z: 0 },
          orientation: { x: 0, y: 0, z: 0 },
          xRotation: 0,
          yRotation: 0,
          zRotation: 0,
          zoom: 1,
          focalLength: 50,
          angleOfView: 60,
          filmSize: 36,
          measureFilmSize: 'horizontal',
          nearClip: 0.1,
          farClip: 100,
          depthOfField: {
            enabled: false,
            focusDistance: 100,
            aperture: 1.2,
            fStop: 2.8,
            blurLevel: 1,
            lockToZoom: false,
          },
          iris: {
            shape: 7,
            rotation: 0,
            roundness: 0,
            aspectRatio: 1,
            diffractionFringe: 0,
          },
          highlight: {
            gain: 0,
            threshold: 1,
            saturation: 1,
          },
          autoOrient: 'off',
        };

        const depthResult = renderDepthFrame({
          width: this.config.width,
          height: this.config.height,
          nearClip: 0.1,
          farClip: 100,
          camera: defaultCamera,
          layers: this.layers,
          frame: frameIndex,
        });

        // Convert to target format
        const convertedDepth = convertDepthToFormat(
          depthResult,
          this.config.depthFormat
        );

        // Create image data
        const imageData = depthToImageData(
          convertedDepth,
          this.config.width,
          this.config.height
        );

        // Convert to canvas and blob
        const canvas = new OffscreenCanvas(this.config.width, this.config.height);
        const ctx = this.get2DContext(canvas, `depth frame ${i} rendering (fallback)`);
        ctx.putImageData(imageData, 0, 0);

        const blob = await canvas.convertToBlob({ type: 'image/png' });
        const filename = `${this.config.filenamePrefix}_depth_${String(i).padStart(5, '0')}.png`;

        if (this.config.comfyuiServer) {
          try {
            const client = getComfyUIClient(this.config.comfyuiServer);
            const uploadResult = await client.uploadImage(blob, filename, 'input', 'depth_sequence');
            depthFiles.push(uploadResult.name);
          } catch (error) {
            console.warn(`[ExportPipeline] Depth frame ${i} upload failed, saving locally:`, error);
            depthFiles.push(await this.saveBlobLocally(blob, filename));
          }
        } else {
          depthFiles.push(await this.saveBlobLocally(blob, filename));
        }
      }
    }

    result.outputFiles.depthSequence = depthFiles;

    this.updateProgress({
      stage: 'rendering_depth',
      stageProgress: 100,
      overallProgress: 40,
      message: 'Depth sequence complete',
    });
  }

  // ============================================================================
  // Control Image Rendering
  // ============================================================================

  private async renderControlSequence(result: ExportResult): Promise<void> {
    const frameCount = this.config.endFrame - this.config.startFrame;
    const controlFiles: string[] = [];

    for (let i = 0; i < frameCount; i++) {
      this.checkAborted();

      const frameIndex = this.config.startFrame + i;
      const progress = (i / frameCount) * 100;

      this.updateProgress({
        stage: 'rendering_control',
        stageProgress: progress,
        overallProgress: 40 + (progress * 0.2),
        currentFrame: i + 1,
        totalFrames: frameCount,
        message: `Rendering control frame ${i + 1}/${frameCount}`,
      });

      // Render the frame
      const canvas = new OffscreenCanvas(this.config.width, this.config.height);
      const ctx = this.get2DContext(canvas, `control frame ${i} rendering`);
      await this.renderFrameToCanvas(ctx, frameIndex);

      // Apply control preprocessing based on type
      const controlCanvas = await this.applyControlPreprocessing(canvas, this.config.controlType || 'depth');

      const blob = await controlCanvas.convertToBlob({ type: 'image/png' });
      const filename = `${this.config.filenamePrefix}_control_${String(i).padStart(5, '0')}.png`;

      if (this.config.comfyuiServer) {
        try {
          const client = getComfyUIClient(this.config.comfyuiServer);
          const uploadResult = await client.uploadImage(blob, filename, 'input', 'control_sequence');
          controlFiles.push(uploadResult.name);
        } catch (error) {
          console.warn(`[ExportPipeline] Control frame ${i} upload failed, saving locally:`, error);
          controlFiles.push(await this.saveBlobLocally(blob, filename));
        }
      } else {
        controlFiles.push(await this.saveBlobLocally(blob, filename));
      }
    }

    result.outputFiles.controlSequence = controlFiles;

    this.updateProgress({
      stage: 'rendering_control',
      stageProgress: 100,
      overallProgress: 60,
      message: 'Control sequence complete',
    });
  }

  /**
   * Render scene as video for SCAIL pose or Uni3C camera motion
   * Requires LatticeEngine to be passed in options
   */
  private async renderSceneVideo(result: ExportResult): Promise<void> {
    if (!this.engine) {
      result.warnings.push('Scene video export requires LatticeEngine - skipped');
      return;
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 45,
      message: 'Rendering scene video...',
    });

    try {
      // Determine if we should apply camera animation
      // For Uni3C, we want camera motion; for SCAIL, we want static camera
      const applyCamera = this.config.target.startsWith('uni3c');

      const video = await this.engine.exportSceneAsVideo({
        startFrame: this.config.startFrame,
        endFrame: this.config.endFrame,
        fps: this.config.fps,
        width: this.config.width,
        height: this.config.height,
        codec: 'avc',
        applyCamera,
        onProgress: (frame, total) => {
          const percent = (frame / total) * 100;
          this.updateProgress({
            stage: 'rendering_frames',
            stageProgress: percent,
            overallProgress: 45 + (percent * 0.1),
            currentFrame: frame,
            totalFrames: total,
            message: `Rendering scene frame ${frame}/${total}...`,
          });
        },
      });

      // Save video
      const filename = `${this.config.filenamePrefix}_scene.mp4`;
      if (this.config.comfyuiServer) {
        try {
          const client = getComfyUIClient(this.config.comfyuiServer);
          // Upload video as file (ComfyUI stores in input folder)
          const file = new File([video.blob], filename, { type: video.mimeType });
          const uploadResult = await client.uploadImage(file, filename);
          result.outputFiles.sceneVideo = uploadResult.name;
        } catch (uploadError) {
          console.warn('[ExportPipeline] Scene video upload failed, saving locally:', uploadError);
          result.outputFiles.sceneVideo = await this.saveBlobLocally(video.blob, filename);
          result.warnings.push('Scene video saved locally due to upload failure');
        }
      } else {
        result.outputFiles.sceneVideo = await this.saveBlobLocally(video.blob, filename);
      }

      this.updateProgress({
        stage: 'rendering_frames',
        stageProgress: 100,
        overallProgress: 55,
        message: 'Scene video complete',
      });
    } catch (error) {
      result.errors.push(`Scene video render failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }

  /**
   * Render layer mask as video for TTM
   * Requires LatticeEngine to be passed in options
   */
  private async renderMaskVideo(result: ExportResult): Promise<void> {
    if (!this.engine) {
      result.warnings.push('Mask video export requires LatticeEngine - skipped');
      return;
    }

    if (!this.config.maskLayerId) {
      result.warnings.push('Mask video export requires maskLayerId in config - skipped');
      return;
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 55,
      message: 'Rendering mask video...',
    });

    try {
      const video = await this.engine.exportLayerAsMaskVideo({
        layerId: this.config.maskLayerId,
        startFrame: this.config.startFrame,
        endFrame: this.config.endFrame,
        fps: this.config.fps,
        width: this.config.width,
        height: this.config.height,
        codec: 'avc',
        binaryMask: true,
        onProgress: (frame, total) => {
          const percent = (frame / total) * 100;
          this.updateProgress({
            stage: 'rendering_frames',
            stageProgress: percent,
            overallProgress: 55 + (percent * 0.1),
            currentFrame: frame,
            totalFrames: total,
            message: `Rendering mask frame ${frame}/${total}...`,
          });
        },
      });

      // Save video
      const filename = `${this.config.filenamePrefix}_mask.mp4`;
      if (this.config.comfyuiServer) {
        try {
          const client = getComfyUIClient(this.config.comfyuiServer);
          const file = new File([video.blob], filename, { type: video.mimeType });
          const uploadResult = await client.uploadImage(file, filename);
          result.outputFiles.maskVideo = uploadResult.name;
        } catch (uploadError) {
          console.warn('[ExportPipeline] Mask video upload failed, saving locally:', uploadError);
          result.outputFiles.maskVideo = await this.saveBlobLocally(video.blob, filename);
          result.warnings.push('Mask video saved locally due to upload failure');
        }
      } else {
        result.outputFiles.maskVideo = await this.saveBlobLocally(video.blob, filename);
      }

      this.updateProgress({
        stage: 'rendering_frames',
        stageProgress: 100,
        overallProgress: 65,
        message: 'Mask video complete',
      });
    } catch (error) {
      result.errors.push(`Mask video render failed: ${error instanceof Error ? error.message : 'Unknown error'}`);
    }
  }

  private async applyControlPreprocessing(
    input: OffscreenCanvas,
    controlType: string
  ): Promise<OffscreenCanvas> {
    const output = new OffscreenCanvas(input.width, input.height);
    const ctx = this.get2DContext(output, 'control preprocessing output');
    const inputCtx = this.get2DContext(input, 'control preprocessing input');
    const imageData = inputCtx.getImageData(0, 0, input.width, input.height);
    const data = imageData.data;

    switch (controlType) {
      case 'canny':
        // Simple edge detection (Sobel-like)
        this.applyEdgeDetection(data, input.width, input.height);
        break;

      case 'lineart':
        // Edge-based lineart detection (Sobel + adaptive threshold)
        this.applyLineart(data, input.width, input.height);
        break;

      case 'softedge':
        // Softer edge detection
        this.applySoftEdge(data, input.width, input.height);
        break;

      default:
        // No preprocessing for depth, normal, etc.
        break;
    }

    ctx.putImageData(imageData, 0, 0);
    return output;
  }

  private applyEdgeDetection(data: Uint8ClampedArray, width: number, height: number): void {
    const grayscale = new Float32Array(width * height);

    // Convert to grayscale
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      grayscale[i] = (data[idx] * 0.299 + data[idx + 1] * 0.587 + data[idx + 2] * 0.114) / 255;
    }

    // Simple Sobel-like edge detection
    const edges = new Float32Array(width * height);
    for (let y = 1; y < height - 1; y++) {
      for (let x = 1; x < width - 1; x++) {
        const idx = y * width + x;

        const gx =
          -grayscale[idx - width - 1] + grayscale[idx - width + 1] +
          -2 * grayscale[idx - 1] + 2 * grayscale[idx + 1] +
          -grayscale[idx + width - 1] + grayscale[idx + width + 1];

        const gy =
          -grayscale[idx - width - 1] - 2 * grayscale[idx - width] - grayscale[idx - width + 1] +
          grayscale[idx + width - 1] + 2 * grayscale[idx + width] + grayscale[idx + width + 1];

        edges[idx] = Math.min(1, Math.sqrt(gx * gx + gy * gy) * 2);
      }
    }

    // Write back
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      const val = Math.floor(edges[i] * 255);
      data[idx] = val;
      data[idx + 1] = val;
      data[idx + 2] = val;
    }
  }

  private applyLineart(data: Uint8ClampedArray, width?: number, height?: number): void {
    // Real lineart: edge detection + adaptive threshold + line enhancement
    // This produces results closer to LineArtPreprocessor in ComfyUI

    if (!width || !height) {
      // Fallback to simple threshold if dimensions not provided
      for (let i = 0; i < data.length; i += 4) {
        const gray = data[i] * 0.299 + data[i + 1] * 0.587 + data[i + 2] * 0.114;
        const val = gray > 128 ? 255 : 0;
        data[i] = val;
        data[i + 1] = val;
        data[i + 2] = val;
      }
      return;
    }

    // Step 1: Convert to grayscale
    const grayscale = new Float32Array(width * height);
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      grayscale[i] = (data[idx] * 0.299 + data[idx + 1] * 0.587 + data[idx + 2] * 0.114) / 255;
    }

    // Step 2: Sobel edge detection (per-channel for better detail)
    const edges = new Float32Array(width * height);
    const sobelX = [-1, 0, 1, -2, 0, 2, -1, 0, 1];
    const sobelY = [-1, -2, -1, 0, 0, 0, 1, 2, 1];

    for (let y = 1; y < height - 1; y++) {
      for (let x = 1; x < width - 1; x++) {
        let gx = 0, gy = 0;
        for (let ky = -1; ky <= 1; ky++) {
          for (let kx = -1; kx <= 1; kx++) {
            const idx = (y + ky) * width + (x + kx);
            const ki = (ky + 1) * 3 + (kx + 1);
            gx += grayscale[idx] * sobelX[ki];
            gy += grayscale[idx] * sobelY[ki];
          }
        }
        edges[y * width + x] = Math.sqrt(gx * gx + gy * gy);
      }
    }

    // Step 3: Find edge threshold using Otsu's method (simplified)
    let maxEdge = 0;
    for (let i = 0; i < edges.length; i++) {
      if (edges[i] > maxEdge) maxEdge = edges[i];
    }
    const threshold = maxEdge * 0.15; // 15% of max edge strength

    // Step 4: Apply threshold and invert (black lines on white)
    for (let i = 0; i < width * height; i++) {
      const idx = i * 4;
      // Lineart: edges become black lines on white background
      const isEdge = edges[i] > threshold;
      const val = isEdge ? 0 : 255;
      data[idx] = val;
      data[idx + 1] = val;
      data[idx + 2] = val;
    }
  }

  private applySoftEdge(data: Uint8ClampedArray, width: number, height: number): void {
    // Similar to edge detection but with Gaussian blur
    this.applyEdgeDetection(data, width, height);

    // Apply simple box blur
    const temp = new Uint8ClampedArray(data);
    const kernel = 2;

    for (let y = kernel; y < height - kernel; y++) {
      for (let x = kernel; x < width - kernel; x++) {
        let sum = 0;
        let count = 0;

        for (let ky = -kernel; ky <= kernel; ky++) {
          for (let kx = -kernel; kx <= kernel; kx++) {
            const idx = ((y + ky) * width + (x + kx)) * 4;
            sum += temp[idx];
            count++;
          }
        }

        const idx = (y * width + x) * 4;
        const val = Math.floor(sum / count);
        data[idx] = val;
        data[idx + 1] = val;
        data[idx + 2] = val;
      }
    }
  }

  // ============================================================================
  // Camera Data Export
  // ============================================================================

  private async exportCameraData(result: ExportResult): Promise<void> {
    this.updateProgress({
      stage: 'exporting_camera',
      stageProgress: 0,
      overallProgress: 60,
      message: 'Exporting camera data...',
    });

    // Create a default camera for export if none provided
    const exportCamera: Camera3D = {
      id: 'export',
      name: 'Export Camera',
      type: 'one-node',
      position: { x: 0, y: 0, z: 1000 },
      pointOfInterest: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      xRotation: 0,
      yRotation: 0,
      zRotation: 0,
      zoom: 1,
      focalLength: 50,
      angleOfView: 60,
      filmSize: 36,
      measureFilmSize: 'horizontal',
      nearClip: 0.1,
      farClip: 100,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 1.2,
        fStop: 2.8,
        blurLevel: 1,
        lockToZoom: false,
      },
      iris: { shape: 7, rotation: 0, roundness: 0, aspectRatio: 1, diffractionFringe: 0 },
      highlight: { gain: 0, threshold: 1, saturation: 1 },
      autoOrient: 'off',
    };

    const cameraData = exportCameraForTarget(
      this.config.target,
      exportCamera,
      this.cameraKeyframes,
      this.config.endFrame - this.config.startFrame,
      this.config.width,
      this.config.height,
      this.config.fps
    );

    const filename = `${this.config.filenamePrefix}_camera.json`;
    const blob = new Blob([JSON.stringify(cameraData, null, 2)], { type: 'application/json' });

    if (this.config.comfyuiServer) {
      // Save as metadata (not uploaded to ComfyUI)
      result.outputFiles.cameraData = filename;
    } else {
      result.outputFiles.cameraData = await this.saveBlobLocally(blob, filename);
    }

    this.updateProgress({
      stage: 'exporting_camera',
      stageProgress: 100,
      overallProgress: 65,
      message: 'Camera data exported',
    });
  }

  // ============================================================================
  // Workflow Generation
  // ============================================================================

  private async generateWorkflow(result: ExportResult): Promise<void> {
    this.updateProgress({
      stage: 'generating_workflow',
      stageProgress: 0,
      overallProgress: 65,
      message: 'Generating workflow...',
    });

    // Build workflow parameters
    const params: WorkflowParams = {
      referenceImage: result.outputFiles.referenceImage,
      lastFrameImage: result.outputFiles.lastImage,
      depthSequence: result.outputFiles.depthSequence,
      controlImages: result.outputFiles.controlSequence,
      prompt: this.config.prompt,
      negativePrompt: this.config.negativePrompt,
      width: this.config.width,
      height: this.config.height,
      frameCount: this.config.endFrame - this.config.startFrame,
      fps: this.config.fps,
      seed: this.config.seed,
      steps: this.config.steps,
      cfgScale: this.config.cfgScale,
      outputFilename: this.config.filenamePrefix,
    };

    // Add target-specific camera data
    if (result.outputFiles.cameraData) {
      params.cameraData = result.outputFiles.cameraData;
    }

    // Generate workflow
    const workflow = generateWorkflowForTarget(this.config.target, params);

    // Validate
    const validation = validateWorkflow(workflow);
    if (!validation.valid) {
      result.errors.push(...validation.errors);
    }
    result.warnings.push(...validation.warnings);

    // Save workflow
    const filename = `${this.config.filenamePrefix}_workflow.json`;
    const blob = new Blob([JSON.stringify(workflow, null, 2)], { type: 'application/json' });

    result.outputFiles.workflowJson = await this.saveBlobLocally(blob, filename);

    this.updateProgress({
      stage: 'generating_workflow',
      stageProgress: 100,
      overallProgress: 70,
      message: 'Workflow generated',
    });
  }

  // ============================================================================
  // ComfyUI Queue
  // ============================================================================

  private async queueWorkflow(result: ExportResult): Promise<void> {
    if (!this.config.comfyuiServer || !result.outputFiles.workflowJson) {
      return;
    }

    this.updateProgress({
      stage: 'queuing',
      stageProgress: 0,
      overallProgress: 70,
      message: 'Connecting to ComfyUI...',
    });

    const client = getComfyUIClient(this.config.comfyuiServer);

    // Check connection
    const connected = await client.checkConnection();
    if (!connected) {
      result.errors.push('Could not connect to ComfyUI server');
      return;
    }

    // Load workflow from file
    const response = await fetch(result.outputFiles.workflowJson);
    const workflow = await response.json();

    this.updateProgress({
      stage: 'queuing',
      stageProgress: 50,
      overallProgress: 75,
      message: 'Queueing workflow...',
    });

    // Queue the workflow
    const promptResult = await client.queuePrompt(workflow);
    result.outputFiles.promptId = promptResult.prompt_id;

    if (promptResult.node_errors && Object.keys(promptResult.node_errors).length > 0) {
      result.errors.push('Workflow has node errors: ' + JSON.stringify(promptResult.node_errors));
      return;
    }

    this.updateProgress({
      stage: 'generating',
      stageProgress: 0,
      overallProgress: 80,
      message: 'Generating video...',
    });

    // Wait for completion
    try {
      await client.waitForPrompt(promptResult.prompt_id, (progress: GenerationProgress) => {
        this.updateProgress({
          stage: 'generating',
          stageProgress: progress.percentage,
          overallProgress: 80 + (progress.percentage * 0.15),
          message: `Generating: ${progress.percentage.toFixed(0)}%`,
          preview: progress.preview,
        });
      });

      this.updateProgress({
        stage: 'complete',
        stageProgress: 100,
        overallProgress: 100,
        message: 'Export complete!',
      });

    } catch (error) {
      result.errors.push(error instanceof Error ? error.message : 'Generation failed');
    }
  }

  // ============================================================================
  // Utilities
  // ============================================================================

  private async saveBlobLocally(blob: Blob, filename: string): Promise<string> {
    // Create object URL for download
    const url = URL.createObjectURL(blob);

    // Trigger download
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);

    // Keep URL for reference (cleanup handled elsewhere)
    return url;
  }

  // ============================================================================
  // Video Export (TTM, Uni3C)
  // Requires LatticeEngine to be passed in options
  // ============================================================================

  /**
   * Export scene as video for Uni3C camera motion
   * Uses LatticeEngine.exportSceneAsVideo() for proper Three.js rendering
   *
   * @param applyCamera - Whether to animate camera during export
   * @returns Encoded video blob, or null if engine not available
   */
  async exportSceneVideo(applyCamera: boolean = true): Promise<EncodedVideo | null> {
    if (!this.engine) {
      console.warn('ExportPipeline: Engine required for video export');
      return null;
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 20,
      message: 'Rendering scene video...',
    });

    try {
      const video = await this.engine.exportSceneAsVideo({
        startFrame: this.config.startFrame,
        endFrame: this.config.endFrame,
        fps: this.config.fps,
        width: this.config.width,
        height: this.config.height,
        codec: 'avc', // H.264 for compatibility
        applyCamera,
        onProgress: (frame, total) => {
          const percent = (frame / total) * 100;
          this.updateProgress({
            stage: 'rendering_frames',
            stageProgress: percent,
            overallProgress: 20 + (percent * 0.3),
            currentFrame: frame,
            totalFrames: total,
            message: `Rendering frame ${frame}/${total}...`,
          });
        },
      });

      return video;
    } catch (error) {
      console.error('Scene video export failed:', error);
      return null;
    }
  }

  /**
   * Export a single layer as binary mask video for TTM
   * Uses LatticeEngine.exportLayerAsMaskVideo() for proper Three.js rendering
   *
   * @param layerId - The layer to render as mask
   * @returns Encoded mask video blob, or null if engine not available
   */
  async exportLayerMaskVideo(layerId: string): Promise<EncodedVideo | null> {
    if (!this.engine) {
      console.warn('ExportPipeline: Engine required for mask video export');
      return null;
    }

    this.updateProgress({
      stage: 'rendering_frames',
      stageProgress: 0,
      overallProgress: 35,
      message: 'Rendering mask video...',
    });

    try {
      const video = await this.engine.exportLayerAsMaskVideo({
        layerId,
        startFrame: this.config.startFrame,
        endFrame: this.config.endFrame,
        fps: this.config.fps,
        width: this.config.width,
        height: this.config.height,
        codec: 'avc',
        binaryMask: true,
        onProgress: (frame, total) => {
          const percent = (frame / total) * 100;
          this.updateProgress({
            stage: 'rendering_frames',
            stageProgress: percent,
            overallProgress: 35 + (percent * 0.2),
            currentFrame: frame,
            totalFrames: total,
            message: `Rendering mask frame ${frame}/${total}...`,
          });
        },
      });

      return video;
    } catch (error) {
      console.error('Mask video export failed:', error);
      return null;
    }
  }

  /**
   * Export TTM data package (reference video + mask video)
   * For use with WanVideoAddTTMLatents node
   *
   * @param animatedLayerId - The layer that will be animated (defines mask)
   * @returns Object with video blobs and filenames
   */
  async exportTTMPackage(animatedLayerId: string): Promise<{
    referenceVideo: EncodedVideo | null;
    maskVideo: EncodedVideo | null;
    error?: string;
  }> {
    if (!this.engine) {
      return {
        referenceVideo: null,
        maskVideo: null,
        error: 'LatticeEngine required for TTM export. Pass engine in ExportPipelineOptions.',
      };
    }

    // Export reference video (full scene with motion)
    const referenceVideo = await this.exportSceneVideo(false);
    if (!referenceVideo) {
      return {
        referenceVideo: null,
        maskVideo: null,
        error: 'Failed to render reference video',
      };
    }

    // Export mask video (just the animated layer as white on black)
    const maskVideo = await this.exportLayerMaskVideo(animatedLayerId);
    if (!maskVideo) {
      return {
        referenceVideo,
        maskVideo: null,
        error: 'Failed to render mask video',
      };
    }

    return { referenceVideo, maskVideo };
  }

  /**
   * Export Uni3C camera video package
   * For use with WanVideoUni3C_embeds render_latent input
   *
   * @returns Scene video with camera animation applied
   */
  async exportUni3CCameraVideo(): Promise<{
    cameraVideo: EncodedVideo | null;
    error?: string;
  }> {
    if (!this.engine) {
      return {
        cameraVideo: null,
        error: 'LatticeEngine required for Uni3C export. Pass engine in ExportPipelineOptions.',
      };
    }

    // Export scene with camera animation
    const cameraVideo = await this.exportSceneVideo(true);
    if (!cameraVideo) {
      return {
        cameraVideo: null,
        error: 'Failed to render camera motion video',
      };
    }

    return { cameraVideo };
  }

  /**
   * Check if video export is available (engine was provided)
   */
  hasVideoExportCapability(): boolean {
    return this.engine !== undefined;
  }
}

// ============================================================================
// Convenience Function
// ============================================================================

export async function exportToComfyUI(
  layers: Layer[],
  cameraKeyframes: CameraKeyframe[],
  config: ExportConfig,
  onProgress?: (progress: ExportProgress) => void
): Promise<ExportResult> {
  const pipeline = new ExportPipeline({
    layers,
    cameraKeyframes,
    config,
    onProgress,
  });

  return pipeline.execute();
}

// ============================================================================
// Quick Export Functions
// ============================================================================

export async function quickExportDepthSequence(
  layers: Layer[],
  width: number,
  height: number,
  frameCount: number,
  format: DepthMapFormat = 'midas',
  onProgress?: (progress: ExportProgress) => void
): Promise<ExportResult> {
  const config: ExportConfig = {
    target: 'controlnet-depth',
    width,
    height,
    frameCount,
    fps: 24,
    startFrame: 0,
    endFrame: frameCount,
    outputDir: '',
    filenamePrefix: 'depth_export',
    exportDepthMap: true,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: false,
    exportLastFrame: false,
    depthFormat: format,
    prompt: '',
    negativePrompt: '',
    autoQueueWorkflow: false,
  };

  return exportToComfyUI(layers, [], config, onProgress);
}

export async function quickExportReferenceFrame(
  layers: Layer[],
  width: number,
  height: number
): Promise<string | null> {
  const config: ExportConfig = {
    target: 'wan22-i2v',
    width,
    height,
    frameCount: 1,
    fps: 24,
    startFrame: 0,
    endFrame: 1,
    outputDir: '',
    filenamePrefix: 'reference',
    exportDepthMap: false,
    exportControlImages: false,
    exportCameraData: false,
    exportReferenceFrame: true,
    exportLastFrame: false,
    depthFormat: 'midas',
    prompt: '',
    negativePrompt: '',
    autoQueueWorkflow: false,
  };

  const result = await exportToComfyUI(layers, [], config);
  return result.outputFiles.referenceImage || null;
}
