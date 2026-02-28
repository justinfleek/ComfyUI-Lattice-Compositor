// IndexedDB FFI for Hydrogen

export const openImpl = (name) => (version) => (stores) => (onError) => (onSuccess) => () => {
  const request = indexedDB.open(name, version);
  
  request.onerror = () => {
    onError(new Error(request.error?.message || "Failed to open database"))();
  };
  
  request.onsuccess = () => {
    onSuccess(request.result)();
  };
  
  request.onupgradeneeded = (event) => {
    const db = event.target.result;
    
    stores.forEach(({ name, config, indexes }) => {
      if (!db.objectStoreNames.contains(name)) {
        const storeOptions = {};
        if (config.keyPath) storeOptions.keyPath = config.keyPath;
        if (config.autoIncrement) storeOptions.autoIncrement = true;
        
        const store = db.createObjectStore(name, storeOptions);
        
        indexes.forEach(idx => {
          store.createIndex(idx.name, idx.keyPath, {
            unique: idx.unique,
            multiEntry: idx.multiEntry
          });
        });
      }
    });
  };
};

export const closeImpl = (db) => () => {
  db.close();
};

export const deleteDatabaseImpl = (name) => (onError) => (onSuccess) => () => {
  const request = indexedDB.deleteDatabase(name);
  request.onerror = () => onError(new Error("Failed to delete database"))();
  request.onsuccess = () => onSuccess();
};

export const putImpl = (db) => (storeName) => (value) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readwrite");
    const store = tx.objectStore(storeName);
    const request = store.put(value);
    
    request.onerror = () => onError(new Error(request.error?.message || "Put failed"))();
    request.onsuccess = () => onSuccess();
  } catch (e) {
    onError(e)();
  }
};

export const getImpl = (db) => (storeName) => (key) => (onError) => (onSuccess) => (onNotFound) => () => {
  try {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.get(key);
    
    request.onerror = () => onError(new Error(request.error?.message || "Get failed"))();
    request.onsuccess = () => {
      if (request.result === undefined) {
        onNotFound();
      } else {
        onSuccess(request.result)();
      }
    };
  } catch (e) {
    onError(e)();
  }
};

export const getAllImpl = (db) => (storeName) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.getAll();
    
    request.onerror = () => onError(new Error(request.error?.message || "GetAll failed"))();
    request.onsuccess = () => onSuccess(request.result || [])();
  } catch (e) {
    onError(e)();
  }
};

export const getAllByIndexImpl = (db) => (storeName) => (indexName) => (value) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const index = store.index(indexName);
    const request = index.getAll(value);
    
    request.onerror = () => onError(new Error(request.error?.message || "GetAll by index failed"))();
    request.onsuccess = () => onSuccess(request.result || [])();
  } catch (e) {
    onError(e)();
  }
};

export const deleteImpl = (db) => (storeName) => (key) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readwrite");
    const store = tx.objectStore(storeName);
    const request = store.delete(key);
    
    request.onerror = () => onError(new Error(request.error?.message || "Delete failed"))();
    request.onsuccess = () => onSuccess();
  } catch (e) {
    onError(e)();
  }
};

export const clearImpl = (db) => (storeName) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readwrite");
    const store = tx.objectStore(storeName);
    const request = store.clear();
    
    request.onerror = () => onError(new Error(request.error?.message || "Clear failed"))();
    request.onsuccess = () => onSuccess();
  } catch (e) {
    onError(e)();
  }
};

export const countImpl = (db) => (storeName) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.count();
    
    request.onerror = () => onError(new Error(request.error?.message || "Count failed"))();
    request.onsuccess = () => onSuccess(request.result)();
  } catch (e) {
    onError(e)();
  }
};

export const keysImpl = (db) => (storeName) => (onError) => (onSuccess) => () => {
  try {
    const tx = db.transaction(storeName, "readonly");
    const store = tx.objectStore(storeName);
    const request = store.getAllKeys();
    
    request.onerror = () => onError(new Error(request.error?.message || "Keys failed"))();
    request.onsuccess = () => onSuccess(request.result.map(String) || [])();
  } catch (e) {
    onError(e)();
  }
};
