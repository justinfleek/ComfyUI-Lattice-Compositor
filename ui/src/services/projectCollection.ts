/**
 * Project Collection Service
 *
 * Collects all project assets (images, videos, audio) and packages them
 * into a ZIP file for download. Includes the project JSON and a manifest.
 */

import JSZip from "jszip";
import type { AssetReference, LatticeProject } from "@/types/project";

// Extended asset type with additional collection properties
type Asset = AssetReference & {
  name?: string; // Alias for filename
  url?: string; // URL source
  mimeType?: string; // MIME type for categorization
};

// ============================================================================
// Types
// ============================================================================

export interface CollectionProgress {
  phase: "scanning" | "collecting" | "compressing" | "complete" | "error";
  current: number;
  total: number;
  currentFile?: string;
  percent: number;
  message: string;
}

export type ProgressCallback = (progress: CollectionProgress) => void;

export interface CollectionOptions {
  includeProject: boolean; // Include project.json
  includeAssets: boolean; // Include asset files
  includeRenderedFrames: boolean; // Include rendered output (if cached)
  flatStructure: boolean; // Flat vs nested folder structure
  maxSizeMB?: number; // Maximum ZIP size limit
}

export interface CollectionManifest {
  projectName: string;
  exportDate: string;
  latticeVersion: string;
  assetCount: number;
  totalSizeBytes: number;
  structure: "flat" | "nested";
  files: Array<{
    path: string;
    originalName: string;
    type: "project" | "image" | "video" | "audio" | "font" | "other";
    sizeBytes: number;
  }>;
}

// ============================================================================
// Service Class
// ============================================================================

class ProjectCollectionService {
  private abortController: AbortController | null = null;

  /**
   * Collect project and assets into a downloadable ZIP
   */
  async collectProject(
    project: LatticeProject,
    assets: Map<string, Asset>,
    options: CollectionOptions = {
      includeProject: true,
      includeAssets: true,
      includeRenderedFrames: false,
      flatStructure: false,
    },
    onProgress?: ProgressCallback,
  ): Promise<Blob> {
    this.abortController = new AbortController();
    const signal = this.abortController.signal;

    const zip = new JSZip();
    const manifest: CollectionManifest = {
      projectName: project.meta?.name || "Untitled Project",
      exportDate: new Date().toISOString(),
      latticeVersion: "1.0.0",
      assetCount: 0,
      totalSizeBytes: 0,
      structure: options.flatStructure ? "flat" : "nested",
      files: [],
    };

    try {
      // Phase 1: Scanning
      onProgress?.({
        phase: "scanning",
        current: 0,
        total: assets.size + 1,
        percent: 0,
        message: "Scanning project assets...",
      });

      // Check for abort
      if (signal.aborted) throw new Error("Collection aborted");

      // Phase 2: Collecting
      let collected = 0;
      const totalItems =
        (options.includeProject ? 1 : 0) +
        (options.includeAssets ? assets.size : 0);

      // Add project JSON
      if (options.includeProject) {
        const projectJson = JSON.stringify(project, null, 2);
        const projectPath = options.flatStructure
          ? "project.json"
          : "project/project.json";

        zip.file(projectPath, projectJson);

        const sizeBytes = new Blob([projectJson]).size;
        manifest.files.push({
          path: projectPath,
          originalName: "project.json",
          type: "project",
          sizeBytes,
        });
        manifest.totalSizeBytes += sizeBytes;
        collected++;

        onProgress?.({
          phase: "collecting",
          current: collected,
          total: totalItems,
          currentFile: "project.json",
          percent: Math.round((collected / totalItems) * 50),
          message: `Collecting: project.json`,
        });
      }

      // Add assets
      if (options.includeAssets) {
        for (const [assetId, asset] of assets) {
          if (signal.aborted) throw new Error("Collection aborted");

          const assetData = await this.fetchAssetData(asset);
          if (!assetData) continue;

          const assetType = this.getAssetType(asset);
          const folder = options.flatStructure ? "" : `assets/${assetType}/`;
          const filename = this.sanitizeFilename(
            asset.name || asset.filename || `asset_${assetId}`,
          );
          const extension = this.getExtension(asset);
          const assetPath = `${folder}${filename}${extension}`;

          zip.file(assetPath, assetData);

          const sizeBytes =
            (assetData instanceof Blob
              ? assetData.size
              : (assetData as ArrayBuffer).byteLength) || 0;
          manifest.files.push({
            path: assetPath,
            originalName: asset.name || asset.filename || assetId,
            type: assetType,
            sizeBytes,
          });
          manifest.totalSizeBytes += sizeBytes;
          manifest.assetCount++;
          collected++;

          onProgress?.({
            phase: "collecting",
            current: collected,
            total: totalItems,
            currentFile: filename,
            percent: Math.round((collected / totalItems) * 50),
            message: `Collecting: ${filename}`,
          });
        }
      }

      // Add manifest
      const manifestJson = JSON.stringify(manifest, null, 2);
      zip.file("manifest.json", manifestJson);

      // Check size limit
      if (
        options.maxSizeMB &&
        manifest.totalSizeBytes > options.maxSizeMB * 1024 * 1024
      ) {
        throw new Error(
          `Project size (${Math.round(manifest.totalSizeBytes / 1024 / 1024)}MB) exceeds limit (${options.maxSizeMB}MB)`,
        );
      }

      // Phase 3: Compressing
      onProgress?.({
        phase: "compressing",
        current: 0,
        total: 100,
        percent: 50,
        message: "Compressing ZIP file...",
      });

      const zipBlob = await zip.generateAsync(
        {
          type: "blob",
          compression: "DEFLATE",
          compressionOptions: { level: 6 },
        },
        (metadata) => {
          onProgress?.({
            phase: "compressing",
            current: Math.round(metadata.percent),
            total: 100,
            percent: 50 + Math.round(metadata.percent / 2),
            message: `Compressing: ${Math.round(metadata.percent)}%`,
          });
        },
      );

      // Phase 4: Complete
      onProgress?.({
        phase: "complete",
        current: totalItems,
        total: totalItems,
        percent: 100,
        message: `Collection complete! ${manifest.assetCount} assets, ${this.formatSize(zipBlob.size)}`,
      });

      return zipBlob;
    } catch (error) {
      const errorMessage =
        error instanceof Error ? error.message : "Unknown error";
      onProgress?.({
        phase: "error",
        current: 0,
        total: 0,
        percent: 0,
        message: `Collection failed: ${errorMessage}`,
      });
      throw error;
    }
  }

  /**
   * Abort an in-progress collection
   */
  abort(): void {
    if (this.abortController) {
      this.abortController.abort();
      this.abortController = null;
    }
  }

  /**
   * Download the ZIP blob as a file
   */
  downloadZip(blob: Blob, filename: string = "project-collection.zip"): void {
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = filename.endsWith(".zip") ? filename : `${filename}.zip`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);
  }

  // --------------------------------------------------------------------------
  // Private Helpers
  // --------------------------------------------------------------------------

  private async fetchAssetData(
    asset: Asset,
  ): Promise<Blob | ArrayBuffer | null> {
    try {
      // If asset has data URL
      if (
        asset.data &&
        typeof asset.data === "string" &&
        asset.data.startsWith("data:")
      ) {
        const response = await fetch(asset.data);
        return await response.blob();
      }

      // If asset has blob URL
      if (asset.url?.startsWith("blob:")) {
        const response = await fetch(asset.url);
        return await response.blob();
      }

      // If asset has regular URL
      if (asset.url) {
        const response = await fetch(asset.url);
        return await response.blob();
      }

      // If asset has raw data, check if it's a Blob
      // Asset.data can be various types, so we check instanceof at runtime
      if (asset.data instanceof Blob) {
        return asset.data;
      }

      if (rawData instanceof ArrayBuffer) {
        return rawData;
      }

      return null;
    } catch (error) {
      console.warn(
        `[ProjectCollection] Failed to fetch asset: ${asset.name || asset.filename}`,
        error,
      );
      return null;
    }
  }

  private getAssetType(
    asset: Asset,
  ): "image" | "video" | "audio" | "font" | "other" {
    const mimeType = asset.mimeType || "";
    if (mimeType.startsWith("image/")) return "image";
    if (mimeType.startsWith("video/")) return "video";
    if (mimeType.startsWith("audio/")) return "audio";
    if (mimeType.includes("font")) return "font";

    // Check by name/extension
    const name = (asset.name || asset.filename || "").toLowerCase();
    if (/\.(png|jpg|jpeg|gif|webp|svg|bmp|tiff?)$/i.test(name)) return "image";
    if (/\.(mp4|webm|mov|avi|mkv)$/i.test(name)) return "video";
    if (/\.(mp3|wav|ogg|aac|flac|m4a)$/i.test(name)) return "audio";
    if (/\.(ttf|otf|woff2?|eot)$/i.test(name)) return "font";

    return "other";
  }

  private getExtension(asset: Asset): string {
    const name = asset.name || asset.filename || "";
    const match = name.match(/\.[^.]+$/);
    if (match) return match[0];

    // Infer from MIME type
    const mimeType = asset.mimeType || "";
    const mimeExtensions: Record<string, string> = {
      "image/png": ".png",
      "image/jpeg": ".jpg",
      "image/gif": ".gif",
      "image/webp": ".webp",
      "image/svg+xml": ".svg",
      "video/mp4": ".mp4",
      "video/webm": ".webm",
      "audio/mpeg": ".mp3",
      "audio/wav": ".wav",
      "audio/ogg": ".ogg",
    };

    return mimeExtensions[mimeType] || "";
  }

  private sanitizeFilename(name: string): string {
    // Remove extension (will be added back)
    const withoutExt = name.replace(/\.[^.]+$/, "");
    // Replace invalid characters
    return withoutExt
      .replace(/[<>:"/\\|?*]/g, "_")
      .replace(/\s+/g, "_")
      .substring(0, 100); // Limit length
  }

  private formatSize(bytes: number): string {
    if (bytes < 1024) return `${bytes} B`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
    if (bytes < 1024 * 1024 * 1024)
      return `${(bytes / 1024 / 1024).toFixed(1)} MB`;
    return `${(bytes / 1024 / 1024 / 1024).toFixed(1)} GB`;
  }
}

// ============================================================================
// Singleton Export
// ============================================================================

export const projectCollectionService = new ProjectCollectionService();
