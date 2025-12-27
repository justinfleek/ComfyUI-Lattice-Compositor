<template>
  <div class="render-queue-panel">
    <!-- Header -->
    <div class="panel-header">
      <h3>Render Queue</h3>
      <div class="header-actions">
        <button
          class="icon-btn"
          :class="{ active: isRunning && !isPaused }"
          title="Start Queue"
          @click="startQueue"
        >
          <i class="pi pi-play" />
        </button>
        <button
          class="icon-btn"
          :class="{ active: isPaused }"
          title="Pause Queue"
          @click="pauseQueue"
        >
          <i class="pi pi-pause" />
        </button>
        <button
          class="icon-btn"
          title="Stop Queue"
          @click="stopQueue"
        >
          <i class="pi pi-stop" />
        </button>
      </div>
    </div>

    <!-- Stats Bar -->
    <div class="stats-bar">
      <span class="stat">
        <span class="stat-value">{{ stats.pendingJobs }}</span> pending
      </span>
      <span class="stat">
        <span class="stat-value">{{ stats.activeJobs }}</span> rendering
      </span>
      <span class="stat">
        <span class="stat-value">{{ stats.completedJobs }}</span> done
      </span>
    </div>

    <!-- Add Job Button -->
    <div class="add-job-section">
      <button class="add-job-btn" @click="showAddJobDialog = true">
        <i class="pi pi-plus" /> Add Current Composition
      </button>
    </div>

    <!-- Job List -->
    <div class="job-list">
      <div
        v-for="job in jobs"
        :key="job.id"
        class="job-item"
        :class="{ active: job.progress.status === 'rendering' }"
      >
        <div class="job-header">
          <span class="job-name">{{ job.name }}</span>
          <span class="job-status" :class="job.progress.status">
            {{ job.progress.status }}
          </span>
        </div>

        <div class="job-details">
          <span>{{ job.width }}x{{ job.height }} @ {{ job.fps }}fps</span>
          <span>{{ job.progress.totalFrames }} frames</span>
        </div>

        <!-- Progress Bar -->
        <div class="progress-container">
          <div
            class="progress-bar"
            :style="{ width: `${job.progress.percentage}%` }"
            :class="job.progress.status"
          />
          <span class="progress-text">
            {{ job.progress.percentage.toFixed(1) }}%
            <template v-if="job.progress.status === 'rendering'">
              ({{ formatTime(job.progress.estimatedTimeRemaining) }} remaining)
            </template>
          </span>
        </div>

        <!-- Job Actions -->
        <div class="job-actions">
          <button
            v-if="job.progress.status === 'rendering'"
            class="job-btn"
            title="Pause"
            @click="pauseJob(job.id)"
          >
            <i class="pi pi-pause" />
          </button>
          <button
            v-else-if="job.progress.status === 'paused'"
            class="job-btn"
            title="Resume"
            @click="resumeJob(job.id)"
          >
            <i class="pi pi-play" />
          </button>
          <button
            v-if="job.progress.status === 'completed'"
            class="job-btn primary"
            title="Download"
            @click="downloadJob(job.id)"
          >
            <i class="pi pi-download" />
          </button>
          <button
            class="job-btn danger"
            title="Remove"
            @click="removeJob(job.id)"
          >
            <i class="pi pi-trash" />
          </button>
        </div>
      </div>

      <!-- Empty State -->
      <div v-if="jobs.length === 0" class="empty-state">
        <i class="pi pi-video" />
        <p>No render jobs in queue</p>
        <p class="hint">Click "Add Current Composition" to start rendering</p>
      </div>
    </div>

    <!-- Add Job Dialog -->
    <div v-if="showAddJobDialog" class="dialog-overlay" @click.self="showAddJobDialog = false">
      <div class="dialog">
        <div class="dialog-header">
          <h4>Add Render Job</h4>
          <button class="close-btn" @click="showAddJobDialog = false">
            <i class="pi pi-times" />
          </button>
        </div>
        <div class="dialog-content">
          <div class="form-row">
            <label>Name</label>
            <input v-model="newJob.name" type="text" placeholder="Render Job" />
          </div>
          <div class="form-row">
            <label>Frame Range</label>
            <div class="range-inputs">
              <input v-model.number="newJob.startFrame" type="number" min="0" />
              <span>to</span>
              <input v-model.number="newJob.endFrame" type="number" min="0" />
            </div>
          </div>
          <div class="form-row">
            <label>Output Size</label>
            <div class="size-inputs">
              <input v-model.number="newJob.width" type="number" min="8" step="8" />
              <span>x</span>
              <input v-model.number="newJob.height" type="number" min="8" step="8" />
            </div>
          </div>
          <div class="form-row">
            <label>Format</label>
            <select v-model="newJob.format">
              <option value="png-sequence">PNG Sequence</option>
              <option value="webm">WebM Video</option>
              <option value="mp4">MP4 Video</option>
            </select>
          </div>
          <div class="form-row">
            <label>Quality</label>
            <input v-model.number="newJob.quality" type="range" min="50" max="100" />
            <span class="value-display">{{ newJob.quality }}%</span>
          </div>
        </div>
        <div class="dialog-footer">
          <button class="btn secondary" @click="showAddJobDialog = false">Cancel</button>
          <button class="btn primary" @click="addJob">Add to Queue</button>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, reactive, computed, onMounted, onUnmounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import {
  RenderQueueManager,
  type RenderJob,
  type RenderQueueStats,
  type RenderedFrame,
} from '@/services/renderQueue';

const store = useCompositorStore();

// Queue manager instance
let queueManager: RenderQueueManager | null = null;

// State
const jobs = ref<RenderJob[]>([]);
const stats = reactive<RenderQueueStats>({
  totalJobs: 0,
  activeJobs: 0,
  pendingJobs: 0,
  completedJobs: 0,
  failedJobs: 0,
  totalFramesRendered: 0,
  averageFps: 0,
});
const isRunning = ref(false);
const isPaused = ref(false);
const showAddJobDialog = ref(false);

// New job form
const newJob = reactive({
  name: 'Render Job',
  startFrame: 0,
  endFrame: 80,
  width: 512,
  height: 512,
  fps: 16,
  format: 'png-sequence' as const,
  quality: 95,
});

// Initialize from composition
function initFromComposition() {
  const comp = store.getActiveComp();
  if (comp) {
    newJob.name = comp.name || 'Render Job';
    newJob.startFrame = 0;
    newJob.endFrame = comp.settings.frameCount - 1;
    newJob.width = comp.settings.width;
    newJob.height = comp.settings.height;
    newJob.fps = comp.settings.fps;
  }
}

// Mount/unmount
onMounted(async () => {
  try {
    // Import and create queue manager
    const { RenderQueueManager } = await import('@/services/renderQueue');
    queueManager = new RenderQueueManager({
      maxConcurrentJobs: 1,
      workerPoolSize: 4,
      batchSize: 10,
      autoSaveInterval: 5000,
      dbName: 'lattice-render-queue',
    });

    await queueManager.initialize();

    // Subscribe to progress updates
    queueManager.onProgress((jobId, progress) => {
      refreshJobs();
    });

    queueManager.onJobComplete((jobId) => {
      refreshJobs();
    });

    queueManager.onQueueEmpty(() => {
      isRunning.value = false;
    });

    refreshJobs();
    initFromComposition();
  } catch (err) {
    console.error('Failed to initialize render queue:', err);
  }
});

onUnmounted(() => {
  queueManager?.stop();
});

// Refresh job list
function refreshJobs() {
  if (!queueManager) return;
  jobs.value = queueManager.getAllJobs();
  updateStats();
}

// Update stats
function updateStats() {
  const allJobs = jobs.value;
  stats.totalJobs = allJobs.length;
  stats.activeJobs = allJobs.filter(j => j.progress.status === 'rendering').length;
  stats.pendingJobs = allJobs.filter(j => j.progress.status === 'pending').length;
  stats.completedJobs = allJobs.filter(j => j.progress.status === 'completed').length;
  stats.failedJobs = allJobs.filter(j => j.progress.status === 'failed').length;
}

// Queue controls
function startQueue() {
  queueManager?.start();
  isRunning.value = true;
  isPaused.value = false;
}

function pauseQueue() {
  queueManager?.pause();
  isPaused.value = true;
}

function stopQueue() {
  queueManager?.stop();
  isRunning.value = false;
  isPaused.value = false;
  refreshJobs();
}

// Job actions
async function addJob() {
  if (!queueManager) return;

  const comp = store.getActiveComp();
  if (!comp) {
    console.error('No active composition');
    return;
  }

  await queueManager.addJob({
    name: newJob.name,
    compositionId: comp.id,
    startFrame: newJob.startFrame,
    endFrame: newJob.endFrame,
    width: newJob.width,
    height: newJob.height,
    fps: newJob.fps,
    format: newJob.format,
    quality: newJob.quality,
    priority: jobs.value.length,
  });

  showAddJobDialog.value = false;
  refreshJobs();
}

function pauseJob(jobId: string) {
  queueManager?.pause();
  isPaused.value = true;
}

function resumeJob(jobId: string) {
  queueManager?.resume();
  isPaused.value = false;
}

async function removeJob(jobId: string) {
  await queueManager?.removeJob(jobId);
  refreshJobs();
}

async function downloadJob(jobId: string) {
  if (!queueManager) {
    console.error('Queue manager not initialized');
    return;
  }

  try {
    // Get job info and frames
    const job = await queueManager.getJob(jobId);
    if (!job) {
      console.error('Job not found:', jobId);
      return;
    }

    const frames = await queueManager.getFrames(jobId);
    if (!frames || frames.length === 0) {
      console.error('No frames found for job:', jobId);
      return;
    }

    // Sort frames by frame number
    frames.sort((a: RenderedFrame, b: RenderedFrame) => a.frameNumber - b.frameNumber);

    // Dynamically import JSZip
    const JSZip = (await import('jszip')).default;
    const zip = new JSZip();

    // Add frames to ZIP (RenderJob extends RenderJobConfig, so properties are directly on job)
    const format = job.format || 'png-sequence';
    const extension = format.includes('png') ? 'png' : format.includes('jpg') ? 'jpg' : 'webp';

    for (const frame of frames) {
      const paddedNumber = frame.frameNumber.toString().padStart(5, '0');
      const filename = `frame_${paddedNumber}.${extension}`;
      zip.file(filename, frame.data);
    }

    // Generate ZIP blob
    const zipBlob = await zip.generateAsync({ type: 'blob' });

    // Create download link
    const url = URL.createObjectURL(zipBlob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `${job.name || 'render'}_frames.zip`;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    URL.revokeObjectURL(url);

    console.log(`Downloaded ${frames.length} frames for job:`, jobId);
  } catch (error) {
    console.error('Failed to download job:', error);
  }
}

// Format time helper
function formatTime(seconds: number): string {
  if (!seconds || seconds === Infinity) return '--:--';
  const mins = Math.floor(seconds / 60);
  const secs = Math.floor(seconds % 60);
  return `${mins}:${secs.toString().padStart(2, '0')}`;
}
</script>

<style scoped>
.render-queue-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  background: var(--lattice-surface-1, #121212);
}

.panel-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 12px;
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.panel-header h3 {
  margin: 0;
  font-size: 14px;
  font-weight: 600;
  color: var(--lattice-text-primary, #e0e0e0);
}

.header-actions {
  display: flex;
  gap: 4px;
}

.icon-btn {
  width: 28px;
  height: 28px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  color: var(--lattice-text-secondary, #a0a0a0);
  cursor: pointer;
  transition: all 0.15s;
}

.icon-btn:hover {
  background: var(--lattice-surface-3, #222);
  color: var(--lattice-text-primary, #e0e0e0);
}

.icon-btn.active {
  background: var(--lattice-accent, #8B5CF6);
  border-color: var(--lattice-accent, #8B5CF6);
  color: white;
}

.stats-bar {
  display: flex;
  gap: 16px;
  padding: 8px 12px;
  background: var(--lattice-surface-0, #0a0a0a);
  font-size: 11px;
}

.stat {
  color: var(--lattice-text-muted, #666);
}

.stat-value {
  color: var(--lattice-text-primary, #e0e0e0);
  font-weight: 600;
}

.add-job-section {
  padding: 12px;
}

.add-job-btn {
  width: 100%;
  padding: 10px;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  background: var(--lattice-accent, #8B5CF6);
  border: none;
  border-radius: 6px;
  color: white;
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: background 0.15s;
}

.add-job-btn:hover {
  background: var(--lattice-accent-hover, #A78BFA);
}

.job-list {
  flex: 1;
  overflow-y: auto;
  padding: 0 12px 12px;
}

.job-item {
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-subtle, #222);
  border-radius: 8px;
  padding: 12px;
  margin-bottom: 8px;
}

.job-item.active {
  border-color: var(--lattice-accent, #8B5CF6);
}

.job-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 8px;
}

.job-name {
  font-weight: 500;
  color: var(--lattice-text-primary, #e0e0e0);
}

.job-status {
  font-size: 11px;
  padding: 2px 8px;
  border-radius: 10px;
  text-transform: uppercase;
}

.job-status.pending { background: var(--lattice-surface-3, #222); color: var(--lattice-text-muted, #666); }
.job-status.rendering { background: var(--lattice-accent, #8B5CF6); color: white; }
.job-status.paused { background: #F59E0B; color: white; }
.job-status.completed { background: #10B981; color: white; }
.job-status.failed { background: #EF4444; color: white; }
.job-status.cancelled { background: var(--lattice-surface-3, #222); color: var(--lattice-text-muted, #666); }

.job-details {
  display: flex;
  gap: 16px;
  font-size: 11px;
  color: var(--lattice-text-muted, #666);
  margin-bottom: 8px;
}

.progress-container {
  position: relative;
  height: 20px;
  background: var(--lattice-surface-0, #0a0a0a);
  border-radius: 4px;
  overflow: hidden;
  margin-bottom: 8px;
}

.progress-bar {
  height: 100%;
  background: var(--lattice-accent, #8B5CF6);
  transition: width 0.3s;
}

.progress-bar.completed { background: #10B981; }
.progress-bar.failed { background: #EF4444; }
.progress-bar.paused { background: #F59E0B; }

.progress-text {
  position: absolute;
  top: 50%;
  left: 50%;
  transform: translate(-50%, -50%);
  font-size: 11px;
  color: white;
  text-shadow: 0 1px 2px rgba(0, 0, 0, 0.5);
}

.job-actions {
  display: flex;
  gap: 8px;
}

.job-btn {
  padding: 6px 12px;
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 4px;
  color: var(--lattice-text-secondary, #a0a0a0);
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.job-btn:hover {
  background: var(--lattice-surface-4, #2a2a2a);
  color: var(--lattice-text-primary, #e0e0e0);
}

.job-btn.primary {
  background: var(--lattice-accent, #8B5CF6);
  border-color: var(--lattice-accent, #8B5CF6);
  color: white;
}

.job-btn.danger:hover {
  background: #EF4444;
  border-color: #EF4444;
  color: white;
}

.empty-state {
  text-align: center;
  padding: 40px 20px;
  color: var(--lattice-text-muted, #666);
}

.empty-state i {
  font-size: 48px;
  margin-bottom: 16px;
  opacity: 0.3;
}

.empty-state p {
  margin: 0 0 8px;
}

.empty-state .hint {
  font-size: 12px;
  opacity: 0.7;
}

/* Dialog */
.dialog-overlay {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
}

.dialog {
  width: 400px;
  background: var(--lattice-surface-1, #121212);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 12px;
  overflow: hidden;
}

.dialog-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px;
  border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.dialog-header h4 {
  margin: 0;
  font-size: 16px;
  color: var(--lattice-text-primary, #e0e0e0);
}

.close-btn {
  background: none;
  border: none;
  color: var(--lattice-text-muted, #666);
  cursor: pointer;
  padding: 4px;
}

.dialog-content {
  padding: 16px;
}

.form-row {
  margin-bottom: 16px;
}

.form-row label {
  display: block;
  margin-bottom: 8px;
  font-size: 12px;
  color: var(--lattice-text-secondary, #a0a0a0);
}

.form-row input[type="text"],
.form-row input[type="number"],
.form-row select {
  width: 100%;
  padding: 8px 12px;
  background: var(--lattice-surface-2, #1a1a1a);
  border: 1px solid var(--lattice-border-default, #333);
  border-radius: 6px;
  color: var(--lattice-text-primary, #e0e0e0);
  font-size: 13px;
}

.range-inputs,
.size-inputs {
  display: flex;
  align-items: center;
  gap: 8px;
}

.range-inputs input,
.size-inputs input {
  width: 80px;
}

.range-inputs span,
.size-inputs span {
  color: var(--lattice-text-muted, #666);
}

.form-row input[type="range"] {
  flex: 1;
}

.value-display {
  min-width: 40px;
  text-align: right;
  color: var(--lattice-text-secondary, #a0a0a0);
  font-size: 12px;
}

.dialog-footer {
  display: flex;
  justify-content: flex-end;
  gap: 12px;
  padding: 16px;
  border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);
}

.btn {
  padding: 8px 20px;
  border-radius: 6px;
  font-size: 13px;
  font-weight: 500;
  cursor: pointer;
  transition: all 0.15s;
}

.btn.secondary {
  background: var(--lattice-surface-3, #222);
  border: 1px solid var(--lattice-border-default, #333);
  color: var(--lattice-text-primary, #e0e0e0);
}

.btn.primary {
  background: var(--lattice-accent, #8B5CF6);
  border: 1px solid var(--lattice-accent, #8B5CF6);
  color: white;
}

.btn.primary:hover {
  background: var(--lattice-accent-hover, #A78BFA);
}
</style>
