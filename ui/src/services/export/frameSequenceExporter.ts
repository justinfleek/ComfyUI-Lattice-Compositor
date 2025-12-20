/**
 * Frame Sequence Exporter
 *
 * Exports rendered frames as image sequences in various formats.
 * Browser-native formats (PNG, JPEG, WebP) are handled client-side.
 * Professional formats (EXR, DPX, TIFF 16-bit) require backend processing.
 */

import JSZip from 'jszip';

export type FrameFormat =
  | 'png'       // Lossless, 8-bit RGBA
  | 'jpeg'      // Lossy, 8-bit RGB
  | 'webp'      // Modern, supports lossless
  | 'tiff'      // Via backend - 8/16-bit
  | 'exr'       // Via backend - HDR 32-bit float
  | 'dpx'       // Via backend - 10/16-bit film format
  ;

export interface FrameExportOptions {
  format: FrameFormat;
  quality: number;           // 0-100 for lossy formats
  filenamePattern: string;   // e.g., "frame_{frame:04d}"
  outputDir: string;
  startFrame: number;
  endFrame: number;
  // For HDR formats
  bitDepth?: 8 | 10 | 16 | 32;
  colorSpace?: 'sRGB' | 'Linear' | 'ACEScg' | 'Rec709';
}

export interface ExportedFrame {
  frameNumber: number;
  filename: string;
  blob?: Blob;
  dataUrl?: string;
  size: number;
}

export interface FrameSequenceResult {
  success: boolean;
  frames: ExportedFrame[];
  totalSize: number;
  errors: string[];
  warnings: string[];
}

// MIME types for browser-supported formats
const FORMAT_MIME: Record<string, string> = {
  png: 'image/png',
  jpeg: 'image/jpeg',
  webp: 'image/webp',
};

// Formats that require backend processing
const BACKEND_FORMATS = ['tiff', 'exr', 'dpx'];

/**
 * Check if format is supported natively in browser
 */
export function isBrowserFormat(format: FrameFormat): boolean {
  return !BACKEND_FORMATS.includes(format);
}

/**
 * Format frame number with padding
 */
export function formatFrameNumber(pattern: string, frame: number): string {
  // Handle {frame:04d} style patterns
  return pattern.replace(/\{frame:(\d+)d\}/g, (_, digits) => {
    return frame.toString().padStart(parseInt(digits), '0');
  });
}

/**
 * Generate filename for a frame
 */
export function generateFilename(
  pattern: string,
  frame: number,
  format: FrameFormat
): string {
  const base = formatFrameNumber(pattern, frame);
  return `${base}.${format}`;
}

/**
 * Export a single canvas frame to blob (browser formats only)
 */
export async function exportCanvasToBlob(
  canvas: HTMLCanvasElement | OffscreenCanvas,
  format: FrameFormat,
  quality: number = 95
): Promise<Blob> {
  const mime = FORMAT_MIME[format];
  if (!mime) {
    throw new Error(`Format ${format} not supported in browser`);
  }

  const qualityValue = format === 'png' ? undefined : quality / 100;

  if (canvas instanceof OffscreenCanvas) {
    return await canvas.convertToBlob({ type: mime, quality: qualityValue });
  } else {
    return new Promise((resolve, reject) => {
      canvas.toBlob(
        (blob) => {
          if (blob) resolve(blob);
          else reject(new Error('Failed to create blob'));
        },
        mime,
        qualityValue
      );
    });
  }
}

/**
 * Export canvas to data URL
 */
export function exportCanvasToDataURL(
  canvas: HTMLCanvasElement,
  format: FrameFormat,
  quality: number = 95
): string {
  const mime = FORMAT_MIME[format];
  if (!mime) {
    throw new Error(`Format ${format} not supported in browser`);
  }

  const qualityValue = format === 'png' ? undefined : quality / 100;
  return canvas.toDataURL(mime, qualityValue);
}

/**
 * Download a blob as a file
 */
export function downloadBlob(blob: Blob, filename: string): void {
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

/**
 * Create a ZIP file from multiple frame blobs
 *
 * @param frames - Array of exported frames with blobs
 * @param folderName - Optional folder name inside the zip (default: 'frames')
 * @param compressionLevel - 0-9, where 0 is no compression (default: 6)
 * @returns ZIP file as Blob
 */
export async function createZipFromFrames(
  frames: ExportedFrame[],
  folderName: string = 'frames',
  compressionLevel: number = 6
): Promise<Blob> {
  const zip = new JSZip();
  const folder = zip.folder(folderName);

  if (!folder) {
    throw new Error('Failed to create ZIP folder');
  }

  // Add each frame to the ZIP
  for (const frame of frames) {
    if (frame.blob) {
      folder.file(frame.filename, frame.blob, {
        compression: 'DEFLATE',
        compressionOptions: { level: compressionLevel },
      });
    }
  }

  // Generate the ZIP blob
  return await zip.generateAsync({
    type: 'blob',
    compression: 'DEFLATE',
    compressionOptions: { level: compressionLevel },
  });
}

/**
 * Export frame sequence via backend (for EXR, DPX, TIFF)
 */
export async function exportViaBackend(
  frames: Array<{ canvas: HTMLCanvasElement; frameNumber: number }>,
  options: FrameExportOptions,
  backendUrl: string = '/weyl/export'
): Promise<FrameSequenceResult> {
  const result: FrameSequenceResult = {
    success: false,
    frames: [],
    totalSize: 0,
    errors: [],
    warnings: [],
  };

  try {
    // Convert canvases to PNG blobs for upload
    const frameData: Array<{ frame: number; data: string }> = [];

    for (const { canvas, frameNumber } of frames) {
      const dataUrl = canvas.toDataURL('image/png');
      frameData.push({ frame: frameNumber, data: dataUrl });
    }

    // Send to backend for conversion
    const response = await fetch(backendUrl, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        frames: frameData,
        format: options.format,
        bitDepth: options.bitDepth || 16,
        colorSpace: options.colorSpace || 'sRGB',
        filenamePattern: options.filenamePattern,
        outputDir: options.outputDir,
      }),
    });

    if (!response.ok) {
      throw new Error(`Backend export failed: ${response.statusText}`);
    }

    const data = await response.json();

    if (data.success) {
      result.success = true;
      result.frames = data.frames;
      result.totalSize = data.totalSize;
    } else {
      result.errors = data.errors || ['Unknown backend error'];
    }
  } catch (error) {
    result.errors.push(`Backend export error: ${error}`);
  }

  return result;
}

/**
 * Main frame sequence export function
 */
export async function exportFrameSequence(
  renderFrame: (frame: number) => Promise<HTMLCanvasElement>,
  options: FrameExportOptions,
  onProgress?: (current: number, total: number) => void
): Promise<FrameSequenceResult> {
  const result: FrameSequenceResult = {
    success: false,
    frames: [],
    totalSize: 0,
    errors: [],
    warnings: [],
  };

  const { format, quality, filenamePattern, startFrame, endFrame } = options;
  const totalFrames = endFrame - startFrame + 1;
  const isBrowser = isBrowserFormat(format);

  try {
    if (isBrowser) {
      // Export directly in browser
      for (let frame = startFrame; frame <= endFrame; frame++) {
        try {
          const canvas = await renderFrame(frame);
          const blob = await exportCanvasToBlob(canvas, format, quality);
          const filename = generateFilename(filenamePattern, frame, format);

          result.frames.push({
            frameNumber: frame,
            filename,
            blob,
            size: blob.size,
          });

          result.totalSize += blob.size;
          onProgress?.(frame - startFrame + 1, totalFrames);
        } catch (error) {
          result.errors.push(`Frame ${frame}: ${error}`);
        }
      }

      result.success = result.frames.length > 0;
    } else {
      // Collect frames for backend processing
      const frames: Array<{ canvas: HTMLCanvasElement; frameNumber: number }> = [];

      for (let frame = startFrame; frame <= endFrame; frame++) {
        try {
          const canvas = await renderFrame(frame);
          frames.push({ canvas, frameNumber: frame });
          onProgress?.(frame - startFrame + 1, totalFrames);
        } catch (error) {
          result.errors.push(`Frame ${frame}: ${error}`);
        }
      }

      if (frames.length > 0) {
        result.warnings.push(
          `${format.toUpperCase()} export requires backend processing`
        );

        // Try backend export
        const backendResult = await exportViaBackend(frames, options);
        Object.assign(result, backendResult);
      }
    }
  } catch (error) {
    result.errors.push(`Export failed: ${error}`);
  }

  return result;
}

/**
 * Get format info for UI display
 */
export function getFormatInfo(format: FrameFormat): {
  name: string;
  description: string;
  extension: string;
  requiresBackend: boolean;
  supportsAlpha: boolean;
  bitDepths: number[];
  lossy: boolean;
} {
  const info: Record<FrameFormat, ReturnType<typeof getFormatInfo>> = {
    png: {
      name: 'PNG',
      description: 'Lossless compression, 8-bit RGBA',
      extension: 'png',
      requiresBackend: false,
      supportsAlpha: true,
      bitDepths: [8],
      lossy: false,
    },
    jpeg: {
      name: 'JPEG',
      description: 'Lossy compression, 8-bit RGB',
      extension: 'jpg',
      requiresBackend: false,
      supportsAlpha: false,
      bitDepths: [8],
      lossy: true,
    },
    webp: {
      name: 'WebP',
      description: 'Modern format, lossy or lossless',
      extension: 'webp',
      requiresBackend: false,
      supportsAlpha: true,
      bitDepths: [8],
      lossy: true,
    },
    tiff: {
      name: 'TIFF',
      description: 'Professional format, 8/16-bit',
      extension: 'tiff',
      requiresBackend: true,
      supportsAlpha: true,
      bitDepths: [8, 16],
      lossy: false,
    },
    exr: {
      name: 'OpenEXR',
      description: 'HDR format, 16/32-bit float',
      extension: 'exr',
      requiresBackend: true,
      supportsAlpha: true,
      bitDepths: [16, 32],
      lossy: false,
    },
    dpx: {
      name: 'DPX',
      description: 'Film industry format, 10/16-bit',
      extension: 'dpx',
      requiresBackend: true,
      supportsAlpha: false,
      bitDepths: [10, 16],
      lossy: false,
    },
  };

  return info[format];
}

export default {
  exportFrameSequence,
  exportCanvasToBlob,
  exportCanvasToDataURL,
  downloadBlob,
  createZipFromFrames,
  generateFilename,
  getFormatInfo,
  isBrowserFormat,
};
