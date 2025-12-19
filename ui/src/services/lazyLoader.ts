/**
 * Lazy Loader Service
 *
 * Provides on-demand loading for heavy modules to reduce initial bundle size.
 * Modules are loaded once and cached for subsequent access.
 */

// Cache for loaded modules
const moduleCache = new Map<string, unknown>();

// Loading promises to prevent duplicate requests
const loadingPromises = new Map<string, Promise<unknown>>();

/**
 * Generic lazy loader with caching
 */
async function lazyLoad<T>(
  key: string,
  loader: () => Promise<T>
): Promise<T> {
  // Return cached module
  if (moduleCache.has(key)) {
    return moduleCache.get(key) as T;
  }

  // Return existing loading promise
  if (loadingPromises.has(key)) {
    return loadingPromises.get(key) as Promise<T>;
  }

  // Start loading
  const promise = loader()
    .then((module) => {
      moduleCache.set(key, module);
      loadingPromises.delete(key);
      return module;
    })
    .catch((error) => {
      // Remove from loading promises so retry is possible
      loadingPromises.delete(key);
      throw error;
    });

  loadingPromises.set(key, promise);
  return promise;
}

// ============================================================================
// HEAVY MODULE LOADERS
// ============================================================================

/**
 * Lazily load the WebGPU renderer
 */
export async function loadWebGPURenderer() {
  return lazyLoad('webgpuRenderer', async () => {
    const module = await import('./webgpuRenderer');
    return module;
  });
}

/**
 * Lazily load the matte exporter
 */
export async function loadMatteExporter() {
  return lazyLoad('matteExporter', async () => {
    const module = await import('./matteExporter');
    return module;
  });
}

/**
 * Lazily load JSZip for export
 */
export async function loadJSZip() {
  return lazyLoad('jszip', async () => {
    const JSZip = (await import('jszip')).default;
    return JSZip;
  });
}

/**
 * Lazily load MP4 muxer
 */
export async function loadMP4Muxer() {
  return lazyLoad('mp4-muxer', async () => {
    const module = await import('mp4-muxer');
    return module;
  });
}

/**
 * Lazily load WebM muxer
 */
export async function loadWebMMuxer() {
  return lazyLoad('webm-muxer', async () => {
    const module = await import('webm-muxer');
    return module;
  });
}

/**
 * Lazily load the particle system
 */
export async function loadParticleSystem() {
  return lazyLoad('particleSystem', async () => {
    const module = await import('./particleSystem');
    return module;
  });
}

/**
 * Lazily load 3D math utilities
 */
export async function loadMath3D() {
  return lazyLoad('math3d', async () => {
    const module = await import('./math3d');
    return module;
  });
}

/**
 * Lazily load camera trajectory service
 */
export async function loadCameraTrajectory() {
  return lazyLoad('cameraTrajectory', async () => {
    const module = await import('./cameraTrajectory');
    return module;
  });
}

/**
 * Lazily load depthflow service
 */
export async function loadDepthflow() {
  return lazyLoad('depthflow', async () => {
    const module = await import('./depthflow');
    return module;
  });
}

// ============================================================================
// PRELOADING
// ============================================================================

/**
 * Preload modules that will likely be needed soon
 * Call this during idle time or after initial render
 */
export function preloadCommonModules(): void {
  // Use requestIdleCallback for non-critical preloading
  const preload = () => {
    // Preload in order of likely usage
    loadParticleSystem().catch(() => {});
    loadMatteExporter().catch(() => {});
  };

  if ('requestIdleCallback' in window) {
    requestIdleCallback(preload, { timeout: 5000 });
  } else {
    setTimeout(preload, 1000);
  }
}

/**
 * Preload export-related modules (call when user opens export dialog)
 */
export function preloadExportModules(): void {
  loadJSZip().catch(() => {});
  loadMP4Muxer().catch(() => {});
  loadWebMMuxer().catch(() => {});
}

// ============================================================================
// CACHE MANAGEMENT
// ============================================================================

/**
 * Clear a specific cached module
 */
export function clearModuleCache(key: string): void {
  moduleCache.delete(key);
}

/**
 * Clear all cached modules
 */
export function clearAllModuleCache(): void {
  moduleCache.clear();
}

/**
 * Get cache statistics
 */
export function getModuleCacheStats(): {
  cachedModules: string[];
  loadingModules: string[];
} {
  return {
    cachedModules: Array.from(moduleCache.keys()),
    loadingModules: Array.from(loadingPromises.keys()),
  };
}
