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
import type { Layer } from '@/types';
import type { CameraKeyframe } from '@/services/export/cameraExportFormats';

import { renderDepthFrame, convertDepthToFormat, depthToImageData, exportDepthSequence } from './depthRenderer';
import { exportCameraForTarget } from './cameraExportFormats';
import { getComfyUIClient } from '@/services/comfyui/comfyuiClient';
import { generateWorkflowForTarget, validateWorkflow, type WorkflowParams } from '@/services/comfyui/workflowTemplates';
import { EXPORT_PRESETS, DEPTH_FORMAT_SPECS } from '@/config/exportPresets';

// ============================================================================
// Types
// ============================================================================

export interface ExportPipelineOptions {
  layers: Layer[];
  cameraKeyframes: CameraKeyframe[];
  config: ExportConfig;
  onProgress?: (progress: ExportProgress) => void;
  abortSignal?: AbortSignal;
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

  constructor(options: ExportPipelineOptions) {
    this.layers = options.layers;
    this.cameraKeyframes = options.cameraKeyframes;
    this.config = options.config;
    this.onProgress = options.onProgress || (() => {});
    this.abortSignal = options.abortSignal;

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

      // Step 5: Export camera data
      if (this.config.exportCameraData) {
        this.checkAborted();
        await this.exportCameraData(result);
      }

      // Step 6: Generate workflow
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

    if (this.config.width < 64 || this.config.width > 4096) {
      errors.push('Width must be between 64 and 4096');
    }

    if (this.config.height < 64 || this.config.height > 4096) {
      errors.push('Height must be between 64 and 4096');
    }

    if (this.config.frameCount < 1 || this.config.frameCount > 1000) {
      errors.push('Frame count must be between 1 and 1000');
    }

    if (this.config.fps < 1 || this.config.fps > 120) {
      errors.push('FPS must be between 1 and 120');
    }

    if (this.config.startFrame < 0 || this.config.startFrame >= this.config.frameCount) {
      errors.push('Invalid start frame');
    }

    if (this.config.endFrame <= this.config.startFrame || this.config.endFrame > this.config.frameCount) {
      errors.push('Invalid end frame');
    }

    if (!this.config.prompt && this.needsPrompt()) {
      errors.push('Prompt is required for this export target');
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
    const ctx = canvas.getContext('2d')!;

    // Render the first frame
    await this.renderFrameToCanvas(ctx, this.config.startFrame);

    // Convert to blob and save
    const blob = await canvas.convertToBlob({ type: 'image/png' });
    const filename = `${this.config.filenamePrefix}_reference.png`;

    // If ComfyUI server is configured, upload
    if (this.config.comfyuiServer) {
      const client = getComfyUIClient(this.config.comfyuiServer);
      const uploadResult = await client.uploadImage(blob, filename);
      result.outputFiles.referenceImage = uploadResult.name;
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
    const ctx = canvas.getContext('2d')!;

    // Render the last frame
    await this.renderFrameToCanvas(ctx, this.config.endFrame - 1);

    // Convert to blob and save
    const blob = await canvas.convertToBlob({ type: 'image/png' });
    const filename = `${this.config.filenamePrefix}_last.png`;

    if (this.config.comfyuiServer) {
      const client = getComfyUIClient(this.config.comfyuiServer);
      const uploadResult = await client.uploadImage(blob, filename);
      result.outputFiles.lastImage = uploadResult.name;
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
      .sort((a, b) => a.position.z - b.position.z);

    // Render each layer
    for (const layer of sortedLayers) {
      await this.renderLayerToCanvas(ctx, layer, frameIndex);
    }
  }

  private async renderLayerToCanvas(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    _frameIndex: number
  ): Promise<void> {
    // Get layer's current transform (interpolated from keyframes if applicable)
    const x = layer.position.x;
    const y = layer.position.y;
    const scale = layer.scale;
    const rotation = layer.rotation;
    const opacity = layer.opacity;

    ctx.save();

    // Apply transforms
    ctx.globalAlpha = opacity;
    ctx.translate(x, y);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.scale(scale, scale);

    // Draw layer content
    if (layer.type === 'image' && layer.content) {
      // Create image from content URL
      const img = await this.loadImage(layer.content);
      ctx.drawImage(img, -img.width / 2, -img.height / 2);
    } else if (layer.type === 'solid') {
      ctx.fillStyle = layer.content || '#000000';
      ctx.fillRect(-50, -50, 100, 100);
    }

    ctx.restore();
  }

  private loadImage(src: string): Promise<HTMLImageElement> {
    return new Promise((resolve, reject) => {
      const img = new Image();
      img.onload = () => resolve(img);
      img.onerror = reject;
      img.src = src;
    });
  }

  // ============================================================================
  // Depth Sequence Rendering
  // ============================================================================

  private async renderDepthSequence(result: ExportResult): Promise<void> {
    const frameCount = this.config.endFrame - this.config.startFrame;
    const depthFiles: string[] = [];

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
        message: `Rendering depth frame ${i + 1}/${frameCount}`,
      });

      // Render depth for this frame
      const depthBuffer = renderDepthFrame(
        this.layers,
        this.config.width,
        this.config.height
      );

      // Convert to target format
      const formatSpec = DEPTH_FORMAT_SPECS[this.config.depthFormat];
      const convertedDepth = convertDepthToFormat(
        depthBuffer,
        this.config.depthFormat,
        {
          invert: formatSpec.invert,
          normalize: formatSpec.normalize,
          nearClip: 0.1,
          farClip: 100,
        }
      );

      // Create image data
      const imageData = depthToImageData(
        convertedDepth,
        this.config.width,
        this.config.height,
        formatSpec.bitDepth
      );

      // Convert to canvas and blob
      const canvas = new OffscreenCanvas(this.config.width, this.config.height);
      const ctx = canvas.getContext('2d')!;
      ctx.putImageData(imageData, 0, 0);

      const blob = await canvas.convertToBlob({ type: 'image/png' });
      const filename = `${this.config.filenamePrefix}_depth_${String(i).padStart(5, '0')}.png`;

      if (this.config.comfyuiServer) {
        const client = getComfyUIClient(this.config.comfyuiServer);
        const uploadResult = await client.uploadImage(blob, filename, 'input', 'depth_sequence');
        depthFiles.push(uploadResult.name);
      } else {
        depthFiles.push(await this.saveBlobLocally(blob, filename));
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
      const ctx = canvas.getContext('2d')!;
      await this.renderFrameToCanvas(ctx, frameIndex);

      // Apply control preprocessing based on type
      const controlCanvas = await this.applyControlPreprocessing(canvas, this.config.controlType || 'depth');

      const blob = await controlCanvas.convertToBlob({ type: 'image/png' });
      const filename = `${this.config.filenamePrefix}_control_${String(i).padStart(5, '0')}.png`;

      if (this.config.comfyuiServer) {
        const client = getComfyUIClient(this.config.comfyuiServer);
        const uploadResult = await client.uploadImage(blob, filename, 'input', 'control_sequence');
        controlFiles.push(uploadResult.name);
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

  private async applyControlPreprocessing(
    input: OffscreenCanvas,
    controlType: string
  ): Promise<OffscreenCanvas> {
    const output = new OffscreenCanvas(input.width, input.height);
    const ctx = output.getContext('2d')!;
    const inputCtx = input.getContext('2d')!;
    const imageData = inputCtx.getImageData(0, 0, input.width, input.height);
    const data = imageData.data;

    switch (controlType) {
      case 'canny':
        // Simple edge detection (Sobel-like)
        this.applyEdgeDetection(data, input.width, input.height);
        break;

      case 'lineart':
        // Convert to grayscale with high contrast
        this.applyLineart(data);
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

  private applyLineart(data: Uint8ClampedArray): void {
    for (let i = 0; i < data.length; i += 4) {
      const gray = data[i] * 0.299 + data[i + 1] * 0.587 + data[i + 2] * 0.114;
      const val = gray > 128 ? 255 : 0;
      data[i] = val;
      data[i + 1] = val;
      data[i + 2] = val;
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

    const cameraData = exportCameraForTarget(
      this.cameraKeyframes,
      this.config.target,
      {
        frameCount: this.config.endFrame - this.config.startFrame,
        fps: this.config.fps,
        width: this.config.width,
        height: this.config.height,
      }
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
