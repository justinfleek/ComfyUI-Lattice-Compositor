// FFI bindings for Lattice.Services.RenderQueue.Database
// IndexedDB operations for render queue persistence

const DB_VERSION = 1;
const JOBS_STORE = "renderJobs";
const FRAMES_STORE = "renderedFrames";

// Open database
export const openDatabaseImpl = (dbName) => () =>
  new Promise((resolve, reject) => {
    const request = indexedDB.open(dbName, DB_VERSION);

    request.onerror = () => {
      reject(new Error(`Failed to open database: ${request.error}`));
    };

    request.onsuccess = () => {
      resolve(request.result);
    };

    request.onupgradeneeded = (event) => {
      const db = event.target.result;

      // Jobs store
      if (!db.objectStoreNames.contains(JOBS_STORE)) {
        const jobsStore = db.createObjectStore(JOBS_STORE, { keyPath: "id" });
        jobsStore.createIndex("status", "progress.status", { unique: false });
        jobsStore.createIndex("priority", "priority", { unique: false });
        jobsStore.createIndex("createdAt", "createdAt", { unique: false });
      }

      // Frames store (for incomplete renders)
      if (!db.objectStoreNames.contains(FRAMES_STORE)) {
        const framesStore = db.createObjectStore(FRAMES_STORE, {
          keyPath: ["jobId", "frameNumber"]
        });
        framesStore.createIndex("jobId", "jobId", { unique: false });
      }
    };
  });

// Close database
export const closeDatabaseImpl = (db) => () => {
  if (db) {
    db.close();
  }
};

// Save job to database
export const saveJobImpl = (db) => (job) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([JOBS_STORE], "readwrite");
    const store = transaction.objectStore(JOBS_STORE);

    // Convert PureScript types to JSON-compatible format
    const jobData = {
      ...job,
      format: formatToString(job.format),
      progress: {
        ...job.progress,
        status: statusToString(job.progress.status),
        error: job.progress.error || null
      },
      startedAt: job.startedAt || null,
      completedAt: job.completedAt || null,
      checkpointFrame: job.checkpointFrame || null
    };

    const request = store.put(jobData);

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });

// Get job by ID
export const getJobImpl = (db) => (jobId) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([JOBS_STORE], "readonly");
    const store = transaction.objectStore(JOBS_STORE);
    const request = store.get(jobId);

    request.onsuccess = () => {
      const result = request.result;
      if (!result) {
        resolve(null); // Nothing in PureScript
      } else {
        // Convert back to PureScript types
        resolve({
          ...result,
          format: stringToFormat(result.format),
          progress: {
            ...result.progress,
            status: stringToStatus(result.progress.status),
            error: result.progress.error || null
          },
          startedAt: result.startedAt || null,
          completedAt: result.completedAt || null,
          checkpointFrame: result.checkpointFrame || null
        });
      }
    };
    request.onerror = () => reject(request.error);
  });

// Get all jobs
export const getAllJobsImpl = (db) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([JOBS_STORE], "readonly");
    const store = transaction.objectStore(JOBS_STORE);
    const request = store.getAll();

    request.onsuccess = () => {
      const results = request.result || [];
      // Convert back to PureScript types
      const jobs = results.map(result => ({
        ...result,
        format: stringToFormat(result.format),
        progress: {
          ...result.progress,
          status: stringToStatus(result.progress.status),
          error: result.progress.error || null
        },
        startedAt: result.startedAt || null,
        completedAt: result.completedAt || null,
        checkpointFrame: result.checkpointFrame || null
      }));
      resolve(jobs);
    };
    request.onerror = () => reject(request.error);
  });

// Delete job by ID
export const deleteJobImpl = (db) => (jobId) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([JOBS_STORE, FRAMES_STORE], "readwrite");

    // Delete job
    const jobsStore = transaction.objectStore(JOBS_STORE);
    jobsStore.delete(jobId);

    // Delete associated frames
    const framesStore = transaction.objectStore(FRAMES_STORE);
    const index = framesStore.index("jobId");
    const cursorRequest = index.openCursor(IDBKeyRange.only(jobId));

    cursorRequest.onsuccess = () => {
      const cursor = cursorRequest.result;
      if (cursor) {
        cursor.delete();
        cursor.continue();
      }
    };

    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error);
  });

// Save rendered frame
export const saveFrameImpl = (db) => (jobId) => (frame) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([FRAMES_STORE], "readwrite");
    const store = transaction.objectStore(FRAMES_STORE);
    const request = store.put({ jobId, ...frame });

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });

// Get all frames for a job
export const getFramesImpl = (db) => (jobId) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([FRAMES_STORE], "readonly");
    const store = transaction.objectStore(FRAMES_STORE);
    const index = store.index("jobId");
    const request = index.getAll(IDBKeyRange.only(jobId));

    request.onsuccess = () => {
      const results = request.result || [];
      // Remove jobId from each frame (it's redundant)
      const frames = results.map(({ jobId: _, ...frame }) => frame);
      resolve(frames);
    };
    request.onerror = () => reject(request.error);
  });

// Clear completed frames for a job
export const clearCompletedFramesImpl = (db) => (jobId) => () =>
  new Promise((resolve, reject) => {
    const transaction = db.transaction([FRAMES_STORE], "readwrite");
    const store = transaction.objectStore(FRAMES_STORE);
    const index = store.index("jobId");
    const cursorRequest = index.openCursor(IDBKeyRange.only(jobId));

    cursorRequest.onsuccess = () => {
      const cursor = cursorRequest.result;
      if (cursor) {
        cursor.delete();
        cursor.continue();
      }
    };

    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error);
  });

// Helper: status to string
function statusToString(status) {
  const statusMap = {
    "StatusPending": "pending",
    "StatusRendering": "rendering",
    "StatusPaused": "paused",
    "StatusCompleted": "completed",
    "StatusFailed": "failed",
    "StatusCancelled": "cancelled"
  };
  // Handle both ADT tags and plain strings
  if (typeof status === "string") {
    return statusMap[status] || status;
  }
  if (status && status.constructor && status.constructor.name) {
    return statusMap[status.constructor.name] || "pending";
  }
  return "pending";
}

// Helper: string to status (returns ADT tag name for PureScript)
function stringToStatus(str) {
  const statusMap = {
    "pending": "StatusPending",
    "rendering": "StatusRendering",
    "paused": "StatusPaused",
    "completed": "StatusCompleted",
    "failed": "StatusFailed",
    "cancelled": "StatusCancelled"
  };
  return statusMap[str] || "StatusPending";
}

// Helper: format to string
function formatToString(format) {
  const formatMap = {
    "FormatPngSequence": "png-sequence",
    "FormatWebM": "webm",
    "FormatMp4": "mp4"
  };
  if (typeof format === "string") {
    return formatMap[format] || format;
  }
  if (format && format.constructor && format.constructor.name) {
    return formatMap[format.constructor.name] || "png-sequence";
  }
  return "png-sequence";
}

// Helper: string to format
function stringToFormat(str) {
  const formatMap = {
    "png-sequence": "FormatPngSequence",
    "webm": "FormatWebM",
    "mp4": "FormatMp4"
  };
  return formatMap[str] || "FormatPngSequence";
}
