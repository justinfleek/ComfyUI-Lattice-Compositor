/**
 * GPU Tier Detection Service
 *
 * Detects GPU capabilities and returns appropriate rendering tier.
 */

import { engineLogger } from '@/utils/logger';

export interface GPUTier {
  tier: 'cpu' | 'webgl' | 'webgpu' | 'blackwell';
  vram: number;
  features: string[];
}

/**
 * Estimate VRAM from WebGPU adapter (approximation)
 */
async function estimateVRAM(adapter: GPUAdapter): Promise<number> {
  try {
    const device = await adapter.requestDevice();
    // WebGPU doesn't directly expose VRAM, but we can check limits
    const maxBufferSize = device.limits.maxBufferSize;
    device.destroy();
    // Rough estimate: max buffer size is usually ~25% of VRAM
    return Math.round((maxBufferSize * 4) / (1024 * 1024 * 1024)); // GB
  } catch {
    return 0;
  }
}

/**
 * Detect GPU tier based on available APIs
 */
export async function detectGPUTier(): Promise<GPUTier> {
  // Check WebGPU (best for canvas rendering)
  if ('gpu' in navigator) {
    try {
      const gpu = navigator.gpu;
      const adapter = await gpu.requestAdapter({
        powerPreference: 'high-performance'
      });

      if (adapter) {
        // Get adapter info - method varies by browser version
        let deviceName = '';
        if ('info' in adapter) {
          // Newer API
          const info = (adapter as any).info;
          deviceName = info?.device || info?.description || '';
        }

        // Detect Blackwell (RTX 50 series)
        if (
          deviceName.includes('RTX 50') ||
          deviceName.toLowerCase().includes('blackwell') ||
          deviceName.includes('B100') ||
          deviceName.includes('B200')
        ) {
          return {
            tier: 'blackwell',
            vram: await estimateVRAM(adapter),
            features: ['fp4_tensor', 'webgpu', 'cuda_12']
          };
        }

        return {
          tier: 'webgpu',
          vram: await estimateVRAM(adapter),
          features: ['webgpu']
        };
      }
    } catch (error) {
      engineLogger.warn('WebGPU detection failed:', error);
    }
  }

  // Fallback to WebGL
  const canvas = document.createElement('canvas');
  const gl = canvas.getContext('webgl2');
  if (gl) {
    const debugInfo = gl.getExtension('WEBGL_debug_renderer_info');
    const renderer = debugInfo
      ? gl.getParameter(debugInfo.UNMASKED_RENDERER_WEBGL)
      : 'Unknown';

    engineLogger.debug('WebGL renderer:', renderer);

    return {
      tier: 'webgl',
      vram: 0, // Can't detect in WebGL
      features: ['webgl2']
    };
  }

  // CPU fallback
  return {
    tier: 'cpu',
    vram: 0,
    features: []
  };
}

export default detectGPUTier;
