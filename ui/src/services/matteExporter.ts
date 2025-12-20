/**
 * Matte Export Service
 *
 * Generates frame sequences with text and particles excluded for Wan video generation.
 */
import type { WeylProject, Layer, TextData, SplineData, ParticleLayerData } from '@/types/project';
import { interpolateProperty } from './interpolation';
import { ArcLengthParameterizer, pathCommandsToBezier } from './arcLength';
import { ParticleSystem } from './particleSystem';

export interface ExportProgress {
  frame: number;
  total: number;
  percent: number;
}

export type ProgressCallback = (progress: ExportProgress) => void;

export interface ExportOptions {
  width: number;
  height: number;
  matteMode: 'exclude_text' | 'include_all';
}

export interface DimensionValidation {
  valid: boolean;
  correctedWidth: number;
  correctedHeight: number;
  message?: string;
}

class MatteExporter {
  private offscreenCanvas: OffscreenCanvas | null = null;
  private ctx: OffscreenCanvasRenderingContext2D | null = null;
  private particleSystems: Map<string, ParticleSystem> = new Map();

  /**
   * Validate dimensions for Wan model requirements
   * Dimensions must be divisible by 8
   */
  validateDimensions(width: number, height: number): DimensionValidation {
    // Must be divisible by 8
    const correctedWidth = Math.round(width / 8) * 8;
    const correctedHeight = Math.round(height / 8) * 8;

    // Minimum 256px
    const finalWidth = Math.max(256, correctedWidth);
    const finalHeight = Math.max(256, correctedHeight);

    const valid = width === finalWidth && height === finalHeight;

    return {
      valid,
      correctedWidth: finalWidth,
      correctedHeight: finalHeight,
      message: valid ? undefined : `Adjusted to ${finalWidth}x${finalHeight} (divisible by 8)`
    };
  }

  /**
   * Get standard resolution presets with 8-divisible dimensions
   */
  getResolutionPresets(): Array<{ label: string; width: number; height: number }> {
    return [
      { label: '480p (848x480)', width: 848, height: 480 },
      { label: '720p (1280x720)', width: 1280, height: 720 },
      { label: '1080p (1920x1080)', width: 1920, height: 1080 }
    ];
  }

  /**
   * Generate matte sequence for all frames
   *
   * Wan mask format:
   * - White (255) = Keep original / generate content
   * - Black (0) = Exclude from generation
   *
   * For text exclusion: Text regions are BLACK, everything else WHITE
   */
  async generateMatteSequence(
    project: WeylProject,
    options: ExportOptions,
    onProgress?: ProgressCallback
  ): Promise<Blob[]> {
    const { frameCount } = project.composition;
    const { width, height } = options;

    // Initialize offscreen canvas
    this.offscreenCanvas = new OffscreenCanvas(width, height);
    this.ctx = this.offscreenCanvas.getContext('2d')!;

    // Initialize particle systems for particle layers
    this.initializeParticleSystems(project);

    const frames: Blob[] = [];

    for (let frame = 0; frame < frameCount; frame++) {
      // Report progress
      if (onProgress) {
        onProgress({
          frame,
          total: frameCount,
          percent: Math.round((frame / frameCount) * 100)
        });
      }

      // Step particle systems to current frame
      this.stepParticleSystemsToFrame(project, frame);

      // Generate frame
      const frameBlob = await this.generateFrame(project, frame, options);
      frames.push(frameBlob);
    }

    // Clean up particle systems
    this.particleSystems.clear();

    // Final progress update
    if (onProgress) {
      onProgress({
        frame: frameCount,
        total: frameCount,
        percent: 100
      });
    }

    return frames;
  }

  /**
   * Generate a single matte frame
   */
  async generateFrame(
    project: WeylProject,
    frame: number,
    options: ExportOptions
  ): Promise<Blob> {
    const ctx = this.ctx!;
    const { width, height } = options;

    // Clear with WHITE (include everything by default)
    ctx.fillStyle = '#FFFFFF';
    ctx.fillRect(0, 0, width, height);

    // If include_all mode, return white frame
    if (options.matteMode === 'include_all') {
      return await this.offscreenCanvas!.convertToBlob({ type: 'image/png' });
    }

    // Set BLACK for exclusion
    ctx.fillStyle = '#000000';

    // Calculate scale factor for resolution difference
    const scaleX = width / project.composition.width;
    const scaleY = height / project.composition.height;

    // Find text layers that are visible at this frame
    const textLayers = project.layers.filter(layer => {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      return layer.type === 'text' &&
        layer.visible &&
        frame >= start &&
        frame <= end;
    });

    for (const layer of textLayers) {
      await this.renderTextLayerToMatte(ctx, layer, project, frame, scaleX, scaleY);
    }

    // Find particle layers that are visible at this frame
    const particleLayers = project.layers.filter(layer => {
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      return layer.type === 'particles' &&
        layer.visible &&
        frame >= start &&
        frame <= end;
    });

    for (const layer of particleLayers) {
      this.renderParticleLayerToMatte(ctx, layer, width, height);
    }

    // Convert to PNG blob
    return await this.offscreenCanvas!.convertToBlob({ type: 'image/png' });
  }

  /**
   * Generate a preview frame (for UI display)
   */
  async generatePreviewFrame(
    project: WeylProject,
    frame: number,
    options: ExportOptions
  ): Promise<string> {
    // Ensure canvas is initialized
    if (!this.offscreenCanvas ||
        this.offscreenCanvas.width !== options.width ||
        this.offscreenCanvas.height !== options.height) {
      this.offscreenCanvas = new OffscreenCanvas(options.width, options.height);
      this.ctx = this.offscreenCanvas.getContext('2d')!;
    }

    const blob = await this.generateFrame(project, frame, options);
    return URL.createObjectURL(blob);
  }

  /**
   * Render text layer as black region on matte
   */
  private async renderTextLayerToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    project: WeylProject,
    frame: number,
    scaleX: number,
    scaleY: number
  ): Promise<void> {
    const textData = layer.data as TextData;
    if (!textData) return;

    // Get animated font size
    const fontSizeProp = layer.properties.find(p => p.name === 'fontSize');
    const fontSize = fontSizeProp
      ? interpolateProperty(fontSizeProp, frame)
      : textData.fontSize;

    // Scale font size
    const scaledFontSize = fontSize * Math.min(scaleX, scaleY);

    ctx.font = `${textData.fontWeight} ${scaledFontSize}px "${textData.fontFamily}"`;

    // Check if text is on a path
    if (textData.pathLayerId) {
      await this.renderTextOnPathToMatte(ctx, layer, textData, project, frame, scaledFontSize, scaleX, scaleY);
    } else {
      this.renderTextBlockToMatte(ctx, layer, textData, frame, scaledFontSize, scaleX, scaleY);
    }
  }

  /**
   * Render text that follows a spline path
   * Per-character rectangles following path
   */
  private async renderTextOnPathToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    project: WeylProject,
    frame: number,
    fontSize: number,
    scaleX: number,
    scaleY: number
  ): Promise<void> {
    // Find the path layer
    const pathLayer = project.layers.find(l => l.id === textData.pathLayerId);
    if (!pathLayer || pathLayer.type !== 'spline') return;

    const splineData = pathLayer.data as SplineData;
    if (!splineData?.controlPoints || splineData.controlPoints.length < 2) return;

    // Build path commands from control points
    const pathCommands = this.buildPathCommands(splineData);
    if (!pathCommands || pathCommands.length < 2) return;

    // Parse path to Bezier curve
    const bezierCurve = pathCommandsToBezier(pathCommands);
    if (!bezierCurve) return;

    // Create arc length parameterizer
    const parameterizer = new ArcLengthParameterizer(bezierCurve);

    // Get animated path offset
    const offsetProp = layer.properties.find(p => p.name === 'pathOffset');
    const pathOffset = offsetProp
      ? interpolateProperty(offsetProp, frame)
      : textData.pathOffset;

    const totalLength = parameterizer.totalLength;
    let currentDistance = pathOffset * totalLength;

    // Render each character as a black rectangle
    const padding = 4 * Math.min(scaleX, scaleY); // Scale padding

    for (const char of textData.text) {
      if (char === ' ') {
        // Skip spaces but add width
        const spaceWidth = ctx.measureText(' ').width;
        currentDistance += spaceWidth + textData.letterSpacing;
        continue;
      }

      const charWidth = ctx.measureText(char).width;

      // Clamp distance
      const clampedDistance = Math.max(0, Math.min(currentDistance, totalLength));

      const { point, tangent } = parameterizer.getPointAtDistance(clampedDistance);
      const angle = Math.atan2(tangent.y, tangent.x);

      // Scale the position
      const scaledX = point.x * scaleX;
      const scaledY = point.y * scaleY;

      ctx.save();
      ctx.translate(scaledX, scaledY);
      ctx.rotate(angle);

      // Draw black rectangle covering the character
      ctx.fillRect(
        -padding,
        -fontSize - padding,
        charWidth + padding * 2,
        fontSize + padding * 2
      );

      ctx.restore();

      currentDistance += charWidth + textData.letterSpacing;
    }
  }

  /**
   * Build path commands from spline control points
   */
  private buildPathCommands(splineData: SplineData): any[] | null {
    const cp = splineData.controlPoints;
    if (!cp || cp.length < 2) return null;

    const pathCommands: any[] = [];

    // Move to first point
    pathCommands.push(['M', cp[0].x, cp[0].y]);

    // Create cubic bezier curves between points
    for (let i = 0; i < cp.length - 1; i++) {
      const p1 = cp[i];
      const p2 = cp[i + 1];

      // Get handle positions (or use point position if no handle)
      const h1 = p1.handleOut || { x: p1.x, y: p1.y };
      const h2 = p2.handleIn || { x: p2.x, y: p2.y };

      pathCommands.push([
        'C',
        h1.x, h1.y,
        h2.x, h2.y,
        p2.x, p2.y
      ]);
    }

    return pathCommands;
  }

  /**
   * Render regular text block (not on path)
   * Standard text bounding box
   */
  private renderTextBlockToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    textData: TextData,
    frame: number,
    fontSize: number,
    scaleX: number,
    scaleY: number
  ): void {
    // Get transform
    const positionProp = layer.transform.position;
    const position = interpolateProperty(positionProp, frame);

    const rotationProp = layer.transform.rotation;
    const rotation = interpolateProperty(rotationProp, frame);

    const scaleProp = layer.transform.scale;
    const scale = interpolateProperty(scaleProp, frame);

    ctx.save();

    // Scale position
    ctx.translate(position.x * scaleX, position.y * scaleY);
    ctx.rotate((rotation * Math.PI) / 180);
    ctx.scale(scale.x, scale.y);

    // Measure text
    const metrics = ctx.measureText(textData.text);
    const textWidth = metrics.width;
    const textHeight = fontSize;

    // Draw black rectangle
    const padding = 4;
    ctx.fillRect(
      -padding,
      -textHeight - padding,
      textWidth + padding * 2,
      textHeight + padding * 2
    );

    ctx.restore();
  }

  /**
   * Download frames as ZIP
   */
  async downloadAsZip(
    frames: Blob[],
    filename: string = 'matte_sequence',
    onProgress?: (percent: number) => void
  ): Promise<void> {
    // Dynamic import JSZip
    const JSZip = (await import('jszip')).default;
    const zip = new JSZip();

    // Add frames to zip
    frames.forEach((blob, index) => {
      const frameName = `${filename}_${String(index).padStart(4, '0')}.png`;
      zip.file(frameName, blob);
    });

    // Generate zip with progress
    const content = await zip.generateAsync(
      { type: 'blob' },
      (metadata) => {
        if (onProgress) {
          onProgress(Math.round(metadata.percent));
        }
      }
    );

    // Download
    const url = URL.createObjectURL(content);
    const link = document.createElement('a');
    link.href = url;
    link.download = `${filename}.zip`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);

    URL.revokeObjectURL(url);
  }

  /**
   * Initialize particle systems for all particle layers
   */
  private initializeParticleSystems(project: WeylProject): void {
    this.particleSystems.clear();

    const particleLayers = project.layers.filter(
      layer => layer.type === 'particles'
    );

    for (const layer of particleLayers) {
      const data = layer.data as ParticleLayerData;
      if (!data) continue;

      const system = new ParticleSystem(data.systemConfig);

      // Add emitters
      for (const emitter of data.emitters) {
        system.addEmitter(emitter);
      }

      // Add gravity wells
      for (const well of data.gravityWells) {
        system.addGravityWell(well);
      }

      // Add vortices
      for (const vortex of data.vortices) {
        system.addVortex(vortex);
      }

      // Add modulations
      for (const mod of data.modulations) {
        system.addModulation(mod);
      }

      // Run warmup period
      const warmupFrames = data.systemConfig.warmupPeriod || 0;
      for (let i = 0; i < warmupFrames; i++) {
        system.step();
      }

      this.particleSystems.set(layer.id, system);
    }
  }

  /**
   * Step particle systems to the current frame
   * For sequential export, we step from frame 0 through each frame
   */
  private stepParticleSystemsToFrame(project: WeylProject, frame: number): void {
    // Only step if this isn't the first frame (systems already initialized at frame 0)
    if (frame === 0) return;

    // Step all visible particle systems
    for (const layer of project.layers) {
      if (layer.type !== 'particles') continue;

      const system = this.particleSystems.get(layer.id);
      if (!system) continue;

      // Only step if layer is visible at this frame
      const start = layer.startFrame ?? layer.inPoint ?? 0;
      const end = layer.endFrame ?? layer.outPoint ?? 80;
      if (layer.visible && frame >= start && frame <= end) {
        system.step();
      }
    }
  }

  /**
   * Render particle layer as black regions on matte
   */
  private renderParticleLayerToMatte(
    ctx: OffscreenCanvasRenderingContext2D,
    layer: Layer,
    width: number,
    height: number
  ): void {
    const system = this.particleSystems.get(layer.id);
    if (!system) return;

    // Get the particle mask from the system
    const maskData = system.renderToMask(width, height);

    // Create a temporary canvas to hold the mask
    const tempCanvas = new OffscreenCanvas(width, height);
    const tempCtx = tempCanvas.getContext('2d')!;
    tempCtx.putImageData(maskData, 0, 0);

    // Composite the mask onto the main canvas
    // The mask already has black particles on white background
    // We use 'multiply' to combine - white stays white, black stays black
    ctx.globalCompositeOperation = 'multiply';
    ctx.drawImage(tempCanvas, 0, 0);
    ctx.globalCompositeOperation = 'source-over';
  }

  /**
   * Clean up resources
   */
  dispose(): void {
    this.offscreenCanvas = null;
    this.ctx = null;
    this.particleSystems.clear();
  }
}

export const matteExporter = new MatteExporter();
export default matteExporter;
