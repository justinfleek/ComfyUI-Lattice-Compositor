/**
 * Project Collection Service
 *
 * Collects all project assets (images, videos, audio) and packages them
 * into a ZIP file for download. Includes the project JSON and a manifest.
 */

import JSZip from "jszip";
import type { AssetReference, LatticeProject } from "@/types/project";

// Extended asset type with additional collection properties
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional types
// Pattern match: data can be string | Blob | ArrayBuffer (never undefined/null)
type Asset = Omit<AssetReference, "data"> & {
  name?: string; // Alias for filename
  url?: string; // URL source
  mimeType?: string; // MIME type for categorization
  data?: string | Blob | ArrayBuffer; // Extended data type for collection
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Types
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
// Service Class
// ═══════════════════════════════════════════════════════════════════════════

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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      projectName: (typeof project.meta === "object" && project.meta !== null && "name" in project.meta && typeof project.meta.name === "string")
        ? project.meta.name
        : "Untitled Project",
      exportDate: new Date().toISOString(),
      latticeVersion: "1.0.0",
      assetCount: 0,
      totalSizeBytes: 0,
      structure: options.flatStructure ? "flat" : "nested",
      files: [],
    };

    try {
      // Phase 1: Scanning
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if (typeof onProgress === "function") {
        onProgress({
          phase: "scanning",
          current: 0,
          total: assets.size + 1,
          percent: 0,
          message: "Scanning project assets...",
        });
      }

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

        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        if (typeof onProgress === "function") {
          onProgress({
            phase: "collecting",
            current: collected,
            total: totalItems,
            currentFile: "project.json",
            percent: Math.round((collected / totalItems) * 50),
            message: `Collecting: project.json`,
          });
        }
      }

      // Add assets
      if (options.includeAssets) {
        for (const [assetId, asset] of assets) {
          if (signal.aborted) throw new Error("Collection aborted");

          const assetData = await this.fetchAssetData(asset);
          if (!assetData) continue;

          const assetType = this.getAssetType(asset);
          const folder = options.flatStructure ? "" : `assets/${assetType}/`;
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
          const nameValue = (typeof asset.name === "string" && asset.name.length > 0) ? asset.name : ((typeof asset.filename === "string" && asset.filename.length > 0) ? asset.filename : `asset_${assetId}`);
          const filename = this.sanitizeFilename(nameValue);
          const extension = this.getExtension(asset);
          const assetPath = `${folder}${filename}${extension}`;

          zip.file(assetPath, assetData);

          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          // Type proof: byte length ∈ number | undefined → number (≥ 0, byte count)
          const blobSize = assetData instanceof Blob && typeof assetData.size === "number"
            ? assetData.size
            : 0;
          const bufferSize = !(assetData instanceof Blob) && assetData instanceof ArrayBuffer && typeof assetData.byteLength === "number"
            ? assetData.byteLength
            : 0;
          const sizeBytes = blobSize > 0
            ? (Number.isFinite(blobSize) && blobSize >= 0 ? blobSize : 0)
            : (Number.isFinite(bufferSize) && bufferSize >= 0 ? bufferSize : 0);
          manifest.files.push({
            path: assetPath,
            originalName: (typeof asset.name === "string" && asset.name.length > 0) ? asset.name : ((typeof asset.filename === "string" && asset.filename.length > 0) ? asset.filename : assetId),
            type: assetType,
            sizeBytes,
          });
          manifest.totalSizeBytes += sizeBytes;
          manifest.assetCount++;
          collected++;

          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          if (typeof onProgress === "function") {
            onProgress({
              phase: "collecting",
              current: collected,
              total: totalItems,
              currentFile: filename,
              percent: Math.round((collected / totalItems) * 50),
              message: `Collecting: ${filename}`,
            });
          }
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
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if (typeof onProgress === "function") {
        onProgress({
          phase: "compressing",
          current: 0,
          total: 100,
          percent: 50,
          message: "Compressing ZIP file...",
        });
      }

      const zipBlob = await zip.generateAsync(
        {
          type: "blob",
          compression: "DEFLATE",
          compressionOptions: { level: 6 },
        },
        (metadata) => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          if (typeof onProgress === "function") {
            onProgress({
              phase: "compressing",
              current: Math.round(metadata.percent),
              total: 100,
              percent: 50 + Math.round(metadata.percent / 2),
              message: `Compressing: ${Math.round(metadata.percent)}%`,
            });
          }
        },
      );

      // Phase 4: Complete
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if (typeof onProgress === "function") {
        onProgress({
          phase: "complete",
          current: totalItems,
          total: totalItems,
          percent: 100,
          message: `Collection complete! ${manifest.assetCount} assets, ${this.formatSize(zipBlob.size)}`,
        });
      }

      return zipBlob;
    } catch (error) {
      const errorMessage =
        error instanceof Error ? error.message : "Unknown error";
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      if (typeof onProgress === "function") {
        onProgress({
          phase: "error",
          current: 0,
          total: 0,
          percent: 0,
          message: `Collection failed: ${errorMessage}`,
        });
      }
      throw error;
    }
  }

  /**
   * Abort an in-progress collection
   */
  abort(): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
    if (this.abortController !== null && typeof this.abortController === "object" && "abort" in this.abortController && typeof this.abortController.abort === "function") {
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

  // ───────────────────────────────────────────────────────────────────────────
  // Private Helpers
  // ───────────────────────────────────────────────────────────────────────────

  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
  // Pattern match: Return Blob | ArrayBuffer (never null)
  private async fetchAssetData(
    asset: Asset,
  ): Promise<Blob | ArrayBuffer> {
    try {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      // If asset has data URL
      if (
        typeof asset.data === "string" &&
        asset.data.length > 0 &&
        asset.data.startsWith("data:")
      ) {
        const response = await fetch(asset.data);
        return await response.blob();
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      // If asset has blob URL
      if (typeof asset.url === "string" && asset.url.startsWith("blob:")) {
        const response = await fetch(asset.url);
        return await response.blob();
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy truthy checks
      // If asset has regular URL
      if (typeof asset.url === "string" && asset.url.length > 0 && !asset.url.startsWith("blob:") && !asset.url.startsWith("data:")) {
        const response = await fetch(asset.url);
        return await response.blob();
      }

      // If asset has raw data, check if it's a Blob
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      // Asset.data can be various types, so we check instanceof at runtime
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined/null checks
      // Pattern match: Check if asset.data is a Blob (never check undefined/null)
      // Type guard: asset.data can be string | Blob | ArrayBuffer | undefined
      const assetDataValue = asset.data;
      if (typeof assetDataValue === "object" && assetDataValue !== null) {
        // Check for Blob (has size property)
        if ("size" in assetDataValue && typeof assetDataValue.size === "number" && assetDataValue instanceof Blob) {
          return assetDataValue;
        }
        // Check for ArrayBuffer (has byteLength property)
        if ("byteLength" in assetDataValue && typeof assetDataValue.byteLength === "number" && assetDataValue instanceof ArrayBuffer) {
          return assetDataValue;
        }
      }

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      // Return empty ArrayBuffer instead of null
      return new ArrayBuffer(0);
    } catch (error) {
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
      const assetName = (typeof asset.name === "string" && asset.name.length > 0) ? asset.name : ((typeof asset.filename === "string" && asset.filename.length > 0) ? asset.filename : "unknown");
      console.warn(
        `[ProjectCollection] Failed to fetch asset: ${assetName}`,
        error,
      );
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy null returns
      return new ArrayBuffer(0);
    }
  }

  private getAssetType(
    asset: Asset,
  ): "image" | "video" | "audio" | "font" | "other" {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
    const mimeType = (typeof asset.mimeType === "string" && asset.mimeType.length > 0) ? asset.mimeType : "";
    if (mimeType.startsWith("image/")) return "image";
    if (mimeType.startsWith("video/")) return "video";
    if (mimeType.startsWith("audio/")) return "audio";
    if (mimeType.includes("font")) return "font";

    // Check by name/extension
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
    const nameValue = (typeof asset.name === "string" && asset.name.length > 0) ? asset.name : ((typeof asset.filename === "string" && asset.filename.length > 0) ? asset.filename : "");
    const name = nameValue.toLowerCase();
    if (/\.(png|jpg|jpeg|gif|webp|svg|bmp|tiff?)$/i.test(name)) return "image";
    if (/\.(mp4|webm|mov|avi|mkv)$/i.test(name)) return "video";
    if (/\.(mp3|wav|ogg|aac|flac|m4a)$/i.test(name)) return "audio";
    if (/\.(ttf|otf|woff2?|eot)$/i.test(name)) return "font";

    return "other";
  }

  private getExtension(asset: Asset): string {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
    const nameValue = (typeof asset.name === "string" && asset.name.length > 0) ? asset.name : ((typeof asset.filename === "string" && asset.filename.length > 0) ? asset.filename : "");
    const name = nameValue;
    const match = name.match(/\.[^.]+$/);
    if (match && match.length > 0 && typeof match[0] === "string") return match[0];

    // Infer from MIME type
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
    const mimeType = (typeof asset.mimeType === "string" && asset.mimeType.length > 0) ? asset.mimeType : "";
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

    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy logical OR
    const extension = (typeof mimeType === "string" && mimeType.length > 0 && mimeType in mimeExtensions && typeof mimeExtensions[mimeType] === "string") ? mimeExtensions[mimeType] : "";
    return extension;
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

// ═══════════════════════════════════════════════════════════════════════════
// Singleton Export
// ═══════════════════════════════════════════════════════════════════════════

export const projectCollectionService = new ProjectCollectionService();
