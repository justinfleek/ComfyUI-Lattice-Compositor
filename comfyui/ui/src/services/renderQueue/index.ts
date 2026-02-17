/**
 * Render Queue Module
 *
 * Browser-based background render queue with IndexedDB persistence
 */

export {
  getRenderQueueManager,
  initializeRenderQueue,
  type RenderedFrame,
  type RenderJob,
  type RenderJobConfig,
  type RenderJobProgress,
  type RenderJobStatus,
  type RenderQueueConfig,
  RenderQueueManager,
  type RenderQueueStats,
} from "./RenderQueueManager";
