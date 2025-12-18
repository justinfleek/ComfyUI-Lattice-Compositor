<template>
  <div class="asset-uploader">
    <div
      class="drop-zone"
      :class="{ 'drag-over': isDragging, 'has-asset': hasAsset }"
      @click="openFilePicker"
      @dragover.prevent="onDragOver"
      @dragleave.prevent="onDragLeave"
      @drop.prevent="onDrop"
    >
      <!-- Asset preview -->
      <div v-if="hasAsset" class="asset-preview">
        <div class="preview-content">
          <img v-if="previewImage" :src="previewImage" class="preview-image" />
          <div v-else class="preview-icon">
            <i :class="['pi', assetTypeIcon]"></i>
          </div>
        </div>
        <div class="asset-info">
          <span class="asset-name">{{ assetName }}</span>
          <span class="asset-meta">{{ assetMeta }}</span>
        </div>
        <button class="remove-btn" @click.stop="removeAsset" title="Remove">
          <i class="pi pi-times"></i>
        </button>
      </div>

      <!-- Upload placeholder -->
      <div v-else class="upload-placeholder">
        <i :class="['pi', placeholderIcon]"></i>
        <span class="upload-label">{{ label }}</span>
        <span class="upload-hint">{{ hint }}</span>
        <span class="upload-formats">{{ acceptedFormatsDisplay }}</span>
      </div>
    </div>

    <!-- Hidden file input -->
    <input
      ref="fileInput"
      type="file"
      :accept="acceptedFormats"
      :multiple="multiple"
      @change="onFileSelected"
      style="display: none"
    />

    <!-- Upload progress -->
    <div v-if="isLoading" class="upload-progress">
      <div class="progress-bar">
        <div class="progress-fill" :style="{ width: `${progress}%` }"></div>
      </div>
      <span class="progress-text">{{ progressText }}</span>
    </div>

    <!-- Error message -->
    <div v-if="errorMessage" class="error-message">
      <i class="pi pi-exclamation-triangle"></i>
      {{ errorMessage }}
    </div>
  </div>
</template>

<script setup lang="ts">
import { ref, computed } from 'vue';
import type { AssetType } from '@/types/project';

const props = withDefaults(defineProps<{
  assetType?: AssetType;
  label?: string;
  multiple?: boolean;
  maxSizeMB?: number;
  // Alternative props
  accept?: string;
  buttonText?: string;
}>(), {
  assetType: 'image',
  multiple: false,
  maxSizeMB: 100,
});

const emit = defineEmits<{
  'upload': [file: File, dataUrl?: string];
  'upload-multiple': [files: File[]];
  'remove': [];
  'error': [message: string];
}>();

// State
const fileInput = ref<HTMLInputElement | null>(null);
const isDragging = ref(false);
const isLoading = ref(false);
const progress = ref(0);
const progressText = ref('');
const errorMessage = ref('');
const assetName = ref('');
const assetMeta = ref('');
const previewImage = ref<string | null>(null);
const hasAsset = ref(false);

// Asset type configurations
const assetConfigs: Record<AssetType, {
  formats: string[];
  icon: string;
  hint: string;
}> = {
  model: {
    formats: ['.gltf', '.glb', '.obj', '.fbx', '.dae', '.usdz'],
    icon: 'pi-box',
    hint: 'Drop 3D model file',
  },
  pointcloud: {
    formats: ['.ply', '.pcd', '.xyz', '.pts', '.las'],
    icon: 'pi-th-large',
    hint: 'Drop point cloud file',
  },
  texture: {
    formats: ['.png', '.jpg', '.jpeg', '.webp', '.exr', '.hdr'],
    icon: 'pi-image',
    hint: 'Drop texture image',
  },
  material: {
    formats: ['.json', '.mtl'],
    icon: 'pi-palette',
    hint: 'Drop material file',
  },
  hdri: {
    formats: ['.hdr', '.exr', '.jpg', '.png'],
    icon: 'pi-globe',
    hint: 'Drop HDRI environment',
  },
  svg: {
    formats: ['.svg'],
    icon: 'pi-star',
    hint: 'Drop SVG file',
  },
  spritesheet: {
    formats: ['.png', '.jpg', '.webp', '.json'],
    icon: 'pi-th-large',
    hint: 'Drop sprite sheet',
  },
  lut: {
    formats: ['.cube', '.3dl', '.png'],
    icon: 'pi-sliders-h',
    hint: 'Drop LUT file',
  },
  depth_map: {
    formats: ['.png', '.jpg', '.exr'],
    icon: 'pi-map',
    hint: 'Drop depth map',
  },
  image: {
    formats: ['.png', '.jpg', '.jpeg', '.webp', '.gif'],
    icon: 'pi-image',
    hint: 'Drop image file',
  },
  video: {
    formats: ['.mp4', '.webm', '.mov'],
    icon: 'pi-video',
    hint: 'Drop video file',
  },
  audio: {
    formats: ['.mp3', '.wav', '.ogg', '.m4a'],
    icon: 'pi-volume-up',
    hint: 'Drop audio file',
  },
};

// Computed
const config = computed(() => assetConfigs[props.assetType] || assetConfigs.image);

const acceptedFormats = computed(() => {
  // Use accept prop if provided
  if (props.accept) {
    return props.accept;
  }
  const formats = config.value.formats;
  return formats.map(f => {
    if (f === '.jpg') return 'image/jpeg';
    if (f === '.png') return 'image/png';
    if (f === '.webp') return 'image/webp';
    if (f === '.gif') return 'image/gif';
    if (f === '.svg') return 'image/svg+xml';
    if (f === '.mp4') return 'video/mp4';
    if (f === '.webm') return 'video/webm';
    if (f === '.mp3') return 'audio/mpeg';
    if (f === '.wav') return 'audio/wav';
    if (f === '.ogg') return 'audio/ogg';
    return f;
  }).join(',');
});

const acceptedFormatsDisplay = computed(() => {
  return config.value.formats.join(', ');
});

const placeholderIcon = computed(() => config.value.icon);
const hint = computed(() => config.value.hint);

const label = computed(() => props.buttonText || props.label || `Upload ${props.assetType}`);

const assetTypeIcon = computed(() => {
  return config.value.icon;
});

// Methods
function openFilePicker() {
  if (hasAsset.value) return;
  fileInput.value?.click();
}

function onDragOver() {
  isDragging.value = true;
}

function onDragLeave() {
  isDragging.value = false;
}

function onDrop(e: DragEvent) {
  isDragging.value = false;
  const files = e.dataTransfer?.files;
  if (files && files.length > 0) {
    if (props.multiple) {
      handleMultipleFiles(Array.from(files));
    } else {
      handleFile(files[0]);
    }
  }
}

function onFileSelected(e: Event) {
  const input = e.target as HTMLInputElement;
  if (input.files && input.files.length > 0) {
    if (props.multiple) {
      handleMultipleFiles(Array.from(input.files));
    } else {
      handleFile(input.files[0]);
    }
  }
}

async function handleFile(file: File) {
  errorMessage.value = '';

  // Validate file size
  const sizeMB = file.size / (1024 * 1024);
  if (sizeMB > props.maxSizeMB) {
    errorMessage.value = `File too large (max ${props.maxSizeMB}MB)`;
    emit('error', errorMessage.value);
    return;
  }

  // Validate file extension
  const ext = '.' + file.name.split('.').pop()?.toLowerCase();
  // If using custom accept, check against that; otherwise use config formats
  const validFormats = props.accept
    ? props.accept.split(',').map(f => f.trim().toLowerCase())
    : config.value.formats;
  const isValidExt = validFormats.some(f => f === ext || f.includes('*') || f.includes('/'));
  if (!isValidExt && !props.accept) {
    errorMessage.value = `Invalid format. Accepted: ${acceptedFormatsDisplay.value}`;
    emit('error', errorMessage.value);
    return;
  }

  // Security: Validate MIME type matches extension for common file types
  const mimeTypeMap: Record<string, string[]> = {
    '.png': ['image/png'],
    '.jpg': ['image/jpeg'],
    '.jpeg': ['image/jpeg'],
    '.gif': ['image/gif'],
    '.webp': ['image/webp'],
    '.svg': ['image/svg+xml'],
    '.mp4': ['video/mp4'],
    '.webm': ['video/webm'],
    '.mov': ['video/quicktime'],
    '.mp3': ['audio/mpeg'],
    '.wav': ['audio/wav', 'audio/wave', 'audio/x-wav'],
    '.json': ['application/json'],
    '.ttf': ['font/ttf', 'application/x-font-ttf'],
    '.otf': ['font/otf', 'application/x-font-otf'],
    '.woff': ['font/woff', 'application/font-woff'],
    '.woff2': ['font/woff2', 'application/font-woff2'],
  };
  const expectedMimes = mimeTypeMap[ext];
  if (expectedMimes && file.type && !expectedMimes.includes(file.type) && !file.type.includes('octet-stream')) {
    errorMessage.value = `File type mismatch: expected ${expectedMimes.join(' or ')}, got ${file.type}`;
    emit('error', errorMessage.value);
    return;
  }

  isLoading.value = true;
  progress.value = 0;
  progressText.value = 'Loading...';

  try {
    // Generate preview for images
    let dataUrl: string | undefined;
    if (file.type.startsWith('image/')) {
      dataUrl = await readFileAsDataUrl(file);
      previewImage.value = dataUrl;
    } else {
      previewImage.value = null;
    }

    // Set asset info
    assetName.value = file.name;
    assetMeta.value = formatFileSize(file.size);
    hasAsset.value = true;

    emit('upload', file, dataUrl);
  } catch (err) {
    errorMessage.value = 'Failed to load file';
    emit('error', errorMessage.value);
  } finally {
    isLoading.value = false;
  }
}

function handleMultipleFiles(files: File[]) {
  // Validate all files
  const validFiles = files.filter(file => {
    const ext = '.' + file.name.split('.').pop()?.toLowerCase();
    const sizeMB = file.size / (1024 * 1024);
    return config.value.formats.includes(ext) && sizeMB <= props.maxSizeMB;
  });

  if (validFiles.length === 0) {
    errorMessage.value = 'No valid files found';
    emit('error', errorMessage.value);
    return;
  }

  emit('upload-multiple', validFiles);

  // Show first file info
  assetName.value = `${validFiles.length} files`;
  assetMeta.value = formatFileSize(validFiles.reduce((sum, f) => sum + f.size, 0));
  hasAsset.value = true;
}

function readFileAsDataUrl(file: File): Promise<string> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result as string);
    reader.onerror = reject;
    reader.onprogress = (e) => {
      if (e.lengthComputable) {
        progress.value = Math.round((e.loaded / e.total) * 100);
        progressText.value = `${progress.value}%`;
      }
    };
    reader.readAsDataURL(file);
  });
}

function formatFileSize(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KB`;
  return `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
}

function removeAsset() {
  hasAsset.value = false;
  assetName.value = '';
  assetMeta.value = '';
  previewImage.value = null;
  if (fileInput.value) {
    fileInput.value.value = '';
  }
  emit('remove');
}
</script>

<style scoped>
.asset-uploader {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.drop-zone {
  position: relative;
  border: 2px dashed #333;
  border-radius: 6px;
  cursor: pointer;
  transition: all 0.2s ease;
  overflow: hidden;
  min-height: 100px;
}

.drop-zone:hover {
  border-color: #555;
  background: #252525;
}

.drop-zone.drag-over {
  border-color: #4a90d9;
  background: rgba(74, 144, 217, 0.1);
}

.drop-zone.has-asset {
  border-style: solid;
  border-color: #333;
  cursor: default;
}

.upload-placeholder {
  display: flex;
  flex-direction: column;
  align-items: center;
  justify-content: center;
  padding: 24px 16px;
  gap: 6px;
}

.upload-placeholder i {
  font-size: 32px;
  color: #444;
}

.upload-label {
  font-size: 12px;
  color: #888;
  font-weight: 500;
}

.upload-hint {
  font-size: 13px;
  color: #555;
}

.upload-formats {
  font-size: 12px;
  color: #444;
  margin-top: 4px;
}

.asset-preview {
  display: flex;
  align-items: center;
  padding: 12px;
  gap: 12px;
}

.preview-content {
  width: 60px;
  height: 60px;
  display: flex;
  align-items: center;
  justify-content: center;
  background: #111;
  border-radius: 4px;
  overflow: hidden;
}

.preview-image {
  width: 100%;
  height: 100%;
  object-fit: cover;
}

.preview-icon i {
  font-size: 28px;
  color: #555;
}

.asset-info {
  flex: 1;
  display: flex;
  flex-direction: column;
  gap: 4px;
  overflow: hidden;
}

.asset-name {
  font-size: 12px;
  color: #ccc;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
}

.asset-meta {
  font-size: 12px;
  color: #666;
}

.remove-btn {
  width: 28px;
  height: 28px;
  border: none;
  background: #333;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  transition: all 0.2s ease;
}

.remove-btn:hover {
  background: #d44;
  color: white;
}

.upload-progress {
  display: flex;
  align-items: center;
  gap: 8px;
}

.progress-bar {
  flex: 1;
  height: 4px;
  background: #333;
  border-radius: 2px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: #4a90d9;
  transition: width 0.2s ease;
}

.progress-text {
  font-size: 12px;
  color: #888;
  min-width: 40px;
  text-align: right;
}

.error-message {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 12px;
  background: rgba(220, 68, 68, 0.1);
  border: 1px solid rgba(220, 68, 68, 0.3);
  border-radius: 4px;
  font-size: 13px;
  color: #d44;
}
</style>
