/**
 * Project Actions - Asset Management
 *
 * Find used assets, remove unused assets, and collect files for export.
 */

import { toRaw } from "vue";
import { validateURL } from "@/services/security/urlValidator";
import { storeLogger } from "@/utils/logger";
import { pushHistory } from "./history";
import type { ProjectStore } from "./types";

// ============================================================================
// ASSET USAGE DETECTION
// ============================================================================

/**
 * Find all asset IDs that are actually used by layers in all compositions
 */
export function findUsedAssetIds(store: ProjectStore): Set<string> {
  const usedIds = new Set<string>();

  // Iterate through all compositions
  for (const comp of Object.values(store.project.compositions)) {
    for (const layer of comp.layers) {
      // Check layer data for asset references
      if (layer.data && typeof layer.data === "object") {
        const data = layer.data as unknown as Record<string, unknown>;

        // Common asset ID field
        if (data.assetId && typeof data.assetId === "string") {
          usedIds.add(data.assetId);
        }

        // Source asset ID (for derived assets)
        if (data.sourceAssetId && typeof data.sourceAssetId === "string") {
          usedIds.add(data.sourceAssetId);
        }

        // Model layer with material references
        if (data.materials && Array.isArray(data.materials)) {
          for (const mat of data.materials as Array<Record<string, unknown>>) {
            if (mat.textureId && typeof mat.textureId === "string")
              usedIds.add(mat.textureId);
            if (mat.normalMapId && typeof mat.normalMapId === "string")
              usedIds.add(mat.normalMapId);
            if (mat.roughnessMapId && typeof mat.roughnessMapId === "string")
              usedIds.add(mat.roughnessMapId);
          }
        }

        // Particle sprite sheet
        if (
          data.spriteSheetAssetId &&
          typeof data.spriteSheetAssetId === "string"
        ) {
          usedIds.add(data.spriteSheetAssetId);
        }

        // Environment map
        if (
          data.environmentMapId &&
          typeof data.environmentMapId === "string"
        ) {
          usedIds.add(data.environmentMapId);
        }
      }
    }
  }

  return usedIds;
}

// ============================================================================
// ASSET CLEANUP
// ============================================================================

/**
 * Remove unused assets from the project (Reduce Project)
 * Returns the number of assets removed
 */
export function removeUnusedAssets(store: ProjectStore): {
  removed: number;
  assetNames: string[];
} {
  const usedIds = findUsedAssetIds(store);
  const assets = store.project.assets;
  const removedNames: string[] = [];
  let removedCount = 0;

  // Find and remove unused assets
  for (const assetId of Object.keys(assets)) {
    if (!usedIds.has(assetId)) {
      const asset = assets[assetId];
      removedNames.push(asset.filename || assetId);
      delete assets[assetId];
      removedCount++;
    }
  }

  if (removedCount > 0) {
    store.project.meta.modified = new Date().toISOString();
    pushHistory(store);
    storeLogger.info(`Removed ${removedCount} unused assets:`, removedNames);
  }

  return { removed: removedCount, assetNames: removedNames };
}

/**
 * Get statistics about asset usage
 */
export function getAssetUsageStats(store: ProjectStore): {
  total: number;
  used: number;
  unused: number;
  unusedNames: string[];
} {
  const usedIds = findUsedAssetIds(store);
  const assets = store.project.assets;
  const unusedNames: string[] = [];

  for (const assetId of Object.keys(assets)) {
    if (!usedIds.has(assetId)) {
      unusedNames.push(assets[assetId].filename || assetId);
    }
  }

  return {
    total: Object.keys(assets).length,
    used: usedIds.size,
    unused: unusedNames.length,
    unusedNames,
  };
}

// ============================================================================
// FILE COLLECTION (ZIP EXPORT)
// ============================================================================

/**
 * Helper to get file extension for an asset
 */
function getExtensionForAsset(asset: { filename?: string; type?: string }): string {
  if (asset.filename) {
    const ext = asset.filename.split(".").pop();
    if (ext) return ext;
  }

  switch (asset.type) {
    case "image":
      return "png";
    case "video":
      return "mp4";
    case "audio":
      return "mp3";
    case "model":
      return "glb";
    case "pointcloud":
      return "ply";
    default:
      return "bin";
  }
}

/**
 * Collect Files - Package project and all used assets into a ZIP
 */
export async function collectFiles(
  store: ProjectStore,
  options: {
    includeUnused?: boolean;
    projectName?: string;
  } = {},
): Promise<Blob> {
  const { includeUnused = false, projectName } = options;

  // Dynamically import JSZip
  const JSZip = (await import("jszip")).default;
  const zip = new JSZip();

  // Create project folder
  const folderName =
    projectName || store.project.meta.name || "lattice-project";
  const folder = zip.folder(folderName);
  if (!folder) throw new Error("Failed to create ZIP folder");

  // Get assets to include
  const usedIds = includeUnused ? undefined : findUsedAssetIds(store);
  const assets = store.project.assets;
  const assetsFolder = folder.folder("assets");

  // Collect asset files
  const assetManifest: Record<string, string> = {}; // assetId -> relative path

  for (const [assetId, asset] of Object.entries(assets)) {
    // Skip unused assets if not including them
    if (usedIds && !usedIds.has(assetId)) continue;

    const filename =
      asset.filename || `${assetId}.${getExtensionForAsset(asset)}`;
    assetManifest[assetId] = `assets/${filename}`;

    // Add asset data to ZIP
    if (asset.data) {
      // Asset has inline data (base64 or data URL)
      if (asset.data.startsWith("data:")) {
        // Data URL - extract base64 part
        const base64Data = asset.data.split(",")[1];
        if (base64Data) {
          assetsFolder?.file(filename, base64Data, { base64: true });
        }
      } else if (
        asset.data.startsWith("blob:") ||
        asset.data.startsWith("http")
      ) {
        // URL - fetch the data with security validation
        const urlValidation = validateURL(asset.data, "fetch");
        if (!urlValidation.valid) {
          storeLogger.warn(
            `[SECURITY] Skipped asset ${assetId}: ${urlValidation.error}`,
          );
          continue;
        }
        try {
          const response = await fetch(urlValidation.sanitized || asset.data);
          const blob = await response.blob();
          assetsFolder?.file(filename, blob);
        } catch (e) {
          storeLogger.warn(`Failed to fetch asset ${assetId}:`, e);
        }
      } else {
        // Assume it's base64
        assetsFolder?.file(filename, asset.data, { base64: true });
      }
    }
  }

  // Create a copy of the project with updated asset paths
  const exportProject = structuredClone(toRaw(store.project));
  (exportProject.meta as unknown as Record<string, unknown>).exportedAt =
    new Date().toISOString();

  // Add asset manifest to project
  (exportProject as unknown as Record<string, unknown>)._assetManifest = assetManifest;

  // Save project JSON
  folder.file("project.lattice.json", JSON.stringify(exportProject, null, 2));

  // Generate ZIP
  const zipBlob = await zip.generateAsync({
    type: "blob",
    compression: "DEFLATE",
    compressionOptions: { level: 6 },
  });

  storeLogger.info(
    `Collected files: ${Object.keys(assetManifest).length} assets, project JSON`,
  );
  return zipBlob;
}

/**
 * Trigger Collect Files download
 */
export async function downloadCollectedFiles(
  store: ProjectStore,
  options: { includeUnused?: boolean } = {},
): Promise<void> {
  const projectName = store.project.meta.name || "lattice-project";
  const zipBlob = await collectFiles(store, { ...options, projectName });

  // Trigger download
  const url = URL.createObjectURL(zipBlob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `${projectName}.zip`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);

  storeLogger.info(`Downloaded collected files: ${projectName}.zip`);
}
