/**
 * Render Queue Module
 *
 * Browser-based background render queue with IndexedDB persistence
 */

export {
  RenderQueueManager,
  getRenderQueueManager,
  initializeRenderQueue,
  type RenderJobStatus,
  type RenderJobConfig,
  type RenderJobProgress,
  type RenderJob,
  type RenderedFrame,
  type RenderQueueStats,
  type RenderQueueConfig,
} from './RenderQueueManager';
