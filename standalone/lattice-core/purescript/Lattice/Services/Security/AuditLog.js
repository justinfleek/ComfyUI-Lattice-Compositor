//                                                                       // ffi
// IndexedDB operations for audit logging

const DB_NAME = "LatticeSecurityAudit";
const DB_VERSION = 1;
const STORE_NAME = "auditLog";

let dbPromise = null;
let currentSessionId = null;

// Session management
export const getSessionId = () => () => {
  if (currentSessionId) return currentSessionId;

  const stored = sessionStorage.getItem("lattice_audit_session_id");
  if (stored) {
    currentSessionId = stored;
    return stored;
  }

  currentSessionId = `session_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
  sessionStorage.setItem("lattice_audit_session_id", currentSessionId);
  return currentSessionId;
};

export const getCurrentISOTimestamp = () => () => {
  return new Date().toISOString();
};

// Open IndexedDB database
function openDatabase() {
  if (dbPromise) return dbPromise;

  dbPromise = new Promise((resolve, reject) => {
    const request = indexedDB.open(DB_NAME, DB_VERSION);

    request.onerror = () => {
      console.error("[SECURITY AUDIT] Failed to open IndexedDB:", request.error);
      reject(request.error);
    };

    request.onsuccess = () => {
      resolve(request.result);
    };

    request.onupgradeneeded = (event) => {
      const db = event.target.result;

      if (!db.objectStoreNames.contains(STORE_NAME)) {
        const store = db.createObjectStore(STORE_NAME, {
          keyPath: "id",
          autoIncrement: true,
        });

        store.createIndex("timestamp", "timestamp", { unique: false });
        store.createIndex("category", "category", { unique: false });
        store.createIndex("severity", "severity", { unique: false });
        store.createIndex("toolName", "toolName", { unique: false });
        store.createIndex("sessionId", "sessionId", { unique: false });
      }
    };
  });

  return dbPromise;
}

// Add entry to IndexedDB
export const addEntryImpl = (storeName) => (entryJson) => async () => {
  const db = await openDatabase();
  const transaction = db.transaction(storeName, "readwrite");
  const store = transaction.objectStore(storeName);

  return new Promise((resolve, reject) => {
    const request = store.add(entryJson);
    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
};

// Query entries from IndexedDB
export const queryEntriesImpl = (storeName) => (queryJson) => async () => {
  const db = await openDatabase();
  const transaction = db.transaction(storeName, "readonly");
  const store = transaction.objectStore(storeName);

  const limit = queryJson.limit || 100;
  const offset = queryJson.offset || 0;

  return new Promise((resolve, reject) => {
    const entries = [];
    const index = store.index("timestamp");
    const cursor = index.openCursor(null, "prev"); // Newest first

    let skipped = 0;

    cursor.onsuccess = () => {
      const result = cursor.result;
      if (!result || entries.length >= limit) {
        resolve(entries);
        return;
      }

      if (skipped < offset) {
        skipped++;
        result.continue();
        return;
      }

      entries.push(result.value);
      result.continue();
    };

    cursor.onerror = () => reject(cursor.error);
  });
};

// Count entries in IndexedDB
export const countEntriesImpl = (storeName) => async () => {
  const db = await openDatabase();
  const transaction = db.transaction(storeName, "readonly");
  const store = transaction.objectStore(storeName);

  return new Promise((resolve, reject) => {
    const request = store.count();
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
};

// Clear IndexedDB store
export const clearStoreImpl = (storeName) => async () => {
  const db = await openDatabase();
  const transaction = db.transaction(storeName, "readwrite");
  const store = transaction.objectStore(storeName);

  return new Promise((resolve, reject) => {
    const request = store.clear();
    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
};

// Delete old entries from IndexedDB
export const deleteOldEntriesImpl = (storeName) => (indexName) => (count) => async () => {
  const db = await openDatabase();
  const transaction = db.transaction(storeName, "readwrite");
  const store = transaction.objectStore(storeName);

  return new Promise((resolve, reject) => {
    let deleted = 0;
    const index = store.index("timestamp");
    const cursor = index.openCursor(); // Oldest first

    cursor.onsuccess = () => {
      const result = cursor.result;
      if (!result || deleted >= count) {
        resolve(deleted);
        return;
      }

      store.delete(result.primaryKey);
      deleted++;
      result.continue();
    };

    cursor.onerror = () => reject(cursor.error);
  });
};

// Download blob as file
export const downloadBlobImpl = (content) => (filename) => () => {
  const blob = new Blob([content], { type: "application/json" });
  const url = URL.createObjectURL(blob);

  const a = document.createElement("a");
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
};
