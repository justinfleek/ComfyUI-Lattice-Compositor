/**
 * Persistence Service
 *
 * Handles all persistent storage for the Lattice Compositor:
 * - Project autosave (IndexedDB)
 * - User settings (localStorage)
 * - Recent projects list (localStorage)
 * - Asset cache (IndexedDB)
 * - AI conversation history (IndexedDB)
 */

import type { LatticeProject } from "@/types/project";

// ============================================================================
// CONSTANTS
// ============================================================================

const DB_NAME = "lattice-compositor";
const DB_VERSION = 1;

const STORES = {
  PROJECTS: "projects",
  ASSETS: "assets",
  AI_HISTORY: "ai_history",
  SETTINGS: "settings",
} as const;

const LOCAL_STORAGE_KEYS = {
  RECENT_PROJECTS: "lattice:recentProjects",
  USER_SETTINGS: "lattice:settings",
  LAST_PROJECT_ID: "lattice:lastProjectId",
  AI_MODEL_PREFERENCE: "lattice:aiModel",
  THEME: "lattice:theme",
  AUTOSAVE_ENABLED: "lattice:autosaveEnabled",
} as const;

// ============================================================================
// TYPES
// ============================================================================

export interface StoredProject {
  id: string;
  name: string;
  data: LatticeProject;
  thumbnail?: string; // Base64 PNG
  createdAt: number;
  modifiedAt: number;
  version: number;
}

export interface RecentProject {
  id: string;
  name: string;
  thumbnail?: string;
  modifiedAt: number;
}

export interface UserSettings {
  theme: "dark" | "light" | "system";
  autosaveEnabled: boolean;
  autosaveIntervalMs: number;
  aiModel: "gpt-4o" | "claude-sonnet";
  showWelcome: boolean;
  canvasBackground: string;
  timelineHeight: number;
  panelLayout: "default" | "compact" | "expanded";
  recentProjectsMax: number;
  keyboardShortcutsEnabled: boolean;
}

export interface StoredAsset {
  id: string;
  projectId: string;
  name: string;
  type: "image" | "video" | "audio" | "font" | "model" | "svg";
  mimeType: string;
  data: Blob;
  thumbnail?: string;
  createdAt: number;
  size: number;
}

export interface AIConversation {
  id: string;
  projectId: string;
  messages: Array<{
    role: "user" | "assistant" | "system" | "tool";
    content: string;
    timestamp: number;
    toolCalls?: unknown[];
  }>;
  model: string;
  createdAt: number;
  modifiedAt: number;
}

// ============================================================================
// DEFAULT VALUES
// ============================================================================

const DEFAULT_SETTINGS: UserSettings = {
  theme: "dark",
  autosaveEnabled: true,
  autosaveIntervalMs: 30000, // 30 seconds
  aiModel: "gpt-4o",
  showWelcome: true,
  canvasBackground: "#1a1a1a",
  timelineHeight: 250,
  panelLayout: "default",
  recentProjectsMax: 10,
  keyboardShortcutsEnabled: true,
};

// ============================================================================
// INDEXEDDB INITIALIZATION
// ============================================================================

let dbInstance: IDBDatabase | null = null;
let dbInitPromise: Promise<IDBDatabase> | null = null;

function initDatabase(): Promise<IDBDatabase> {
  if (dbInstance) {
    return Promise.resolve(dbInstance);
  }

  if (dbInitPromise) {
    return dbInitPromise;
  }

  dbInitPromise = new Promise((resolve, reject) => {
    const request = indexedDB.open(DB_NAME, DB_VERSION);

    request.onerror = () => {
      console.error("Failed to open IndexedDB:", request.error);
      reject(request.error);
    };

    request.onsuccess = () => {
      dbInstance = request.result;
      resolve(dbInstance);
    };

    request.onupgradeneeded = (event) => {
      const db = (event.target as IDBOpenDBRequest).result;

      // Projects store
      if (!db.objectStoreNames.contains(STORES.PROJECTS)) {
        const projectStore = db.createObjectStore(STORES.PROJECTS, {
          keyPath: "id",
        });
        projectStore.createIndex("name", "name", { unique: false });
        projectStore.createIndex("modifiedAt", "modifiedAt", { unique: false });
      }

      // Assets store
      if (!db.objectStoreNames.contains(STORES.ASSETS)) {
        const assetStore = db.createObjectStore(STORES.ASSETS, {
          keyPath: "id",
        });
        assetStore.createIndex("projectId", "projectId", { unique: false });
        assetStore.createIndex("type", "type", { unique: false });
      }

      // AI History store
      if (!db.objectStoreNames.contains(STORES.AI_HISTORY)) {
        const aiStore = db.createObjectStore(STORES.AI_HISTORY, {
          keyPath: "id",
        });
        aiStore.createIndex("projectId", "projectId", { unique: false });
        aiStore.createIndex("modifiedAt", "modifiedAt", { unique: false });
      }

      // Settings store (for complex settings that don't fit localStorage)
      if (!db.objectStoreNames.contains(STORES.SETTINGS)) {
        db.createObjectStore(STORES.SETTINGS, { keyPath: "key" });
      }
    };
  });

  return dbInitPromise;
}

async function getDB(): Promise<IDBDatabase> {
  return initDatabase();
}

// ============================================================================
// PROJECT PERSISTENCE
// ============================================================================

/**
 * Generate a unique project ID based on main composition ID or random UUID
 */
function getProjectId(project: LatticeProject): string {
  // Use mainCompositionId as the project identifier, or generate one
  if (project.mainCompositionId) {
    return project.mainCompositionId;
  }
  // Fallback: generate a UUID-like ID
  return `proj_${Date.now()}_${Math.random().toString(36).substring(2, 9)}`;
}

export async function saveProject(
  project: LatticeProject,
  projectId?: string,
  thumbnail?: string,
): Promise<string> {
  const db = await getDB();

  const id = projectId || getProjectId(project);
  const name = project.meta?.name || "Untitled Project";

  const stored: StoredProject = {
    id,
    name,
    data: project,
    thumbnail,
    createdAt: Date.now(),
    modifiedAt: Date.now(),
    version: 1,
  };

  // Check if project exists to preserve createdAt
  const existing = await getProject(id);
  if (existing) {
    stored.createdAt = existing.createdAt;
    stored.version = existing.version + 1;
  }

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.PROJECTS, "readwrite");
    const store = transaction.objectStore(STORES.PROJECTS);
    const request = store.put(stored);

    request.onsuccess = () => {
      // Update recent projects list
      addToRecentProjects({
        id,
        name,
        thumbnail,
        modifiedAt: stored.modifiedAt,
      });
      setLastProjectId(id);
      resolve(id);
    };

    request.onerror = () => reject(request.error);
  });
}

export async function getProject(id: string): Promise<StoredProject | null> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.PROJECTS, "readonly");
    const store = transaction.objectStore(STORES.PROJECTS);
    const request = store.get(id);

    request.onsuccess = () => resolve(request.result || null);
    request.onerror = () => reject(request.error);
  });
}

export async function deleteProject(id: string): Promise<void> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.PROJECTS, "readwrite");
    const store = transaction.objectStore(STORES.PROJECTS);
    const request = store.delete(id);

    request.onsuccess = () => {
      removeFromRecentProjects(id);
      resolve();
    };
    request.onerror = () => reject(request.error);
  });
}

export async function listProjects(): Promise<StoredProject[]> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.PROJECTS, "readonly");
    const store = transaction.objectStore(STORES.PROJECTS);
    const index = store.index("modifiedAt");
    const request = index.openCursor(null, "prev"); // Most recent first

    const projects: StoredProject[] = [];

    request.onsuccess = () => {
      const cursor = request.result;
      if (cursor) {
        projects.push(cursor.value);
        cursor.continue();
      } else {
        resolve(projects);
      }
    };

    request.onerror = () => reject(request.error);
  });
}

// ============================================================================
// ASSET PERSISTENCE
// ============================================================================

export async function saveAsset(
  asset: Omit<StoredAsset, "createdAt" | "size">,
): Promise<void> {
  const db = await getDB();

  const stored: StoredAsset = {
    ...asset,
    createdAt: Date.now(),
    size: asset.data.size,
  };

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.ASSETS, "readwrite");
    const store = transaction.objectStore(STORES.ASSETS);
    const request = store.put(stored);

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
}

export async function getAsset(id: string): Promise<StoredAsset | null> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.ASSETS, "readonly");
    const store = transaction.objectStore(STORES.ASSETS);
    const request = store.get(id);

    request.onsuccess = () => resolve(request.result || null);
    request.onerror = () => reject(request.error);
  });
}

export async function getProjectAssets(
  projectId: string,
): Promise<StoredAsset[]> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.ASSETS, "readonly");
    const store = transaction.objectStore(STORES.ASSETS);
    const index = store.index("projectId");
    const request = index.getAll(projectId);

    request.onsuccess = () => resolve(request.result || []);
    request.onerror = () => reject(request.error);
  });
}

export async function deleteAsset(id: string): Promise<void> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.ASSETS, "readwrite");
    const store = transaction.objectStore(STORES.ASSETS);
    const request = store.delete(id);

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
}

export async function deleteProjectAssets(projectId: string): Promise<void> {
  const assets = await getProjectAssets(projectId);
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.ASSETS, "readwrite");
    const store = transaction.objectStore(STORES.ASSETS);

    let completed = 0;
    if (assets.length === 0) {
      resolve();
      return;
    }

    for (const asset of assets) {
      const request = store.delete(asset.id);
      request.onsuccess = () => {
        completed++;
        if (completed === assets.length) resolve();
      };
      request.onerror = () => reject(request.error);
    }
  });
}

// ============================================================================
// AI CONVERSATION PERSISTENCE
// ============================================================================

export async function saveAIConversation(
  conversation: AIConversation,
): Promise<void> {
  const db = await getDB();

  conversation.modifiedAt = Date.now();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.AI_HISTORY, "readwrite");
    const store = transaction.objectStore(STORES.AI_HISTORY);
    const request = store.put(conversation);

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
}

export async function getAIConversation(
  id: string,
): Promise<AIConversation | null> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.AI_HISTORY, "readonly");
    const store = transaction.objectStore(STORES.AI_HISTORY);
    const request = store.get(id);

    request.onsuccess = () => resolve(request.result || null);
    request.onerror = () => reject(request.error);
  });
}

export async function getProjectAIConversations(
  projectId: string,
): Promise<AIConversation[]> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.AI_HISTORY, "readonly");
    const store = transaction.objectStore(STORES.AI_HISTORY);
    const index = store.index("projectId");
    const request = index.getAll(projectId);

    request.onsuccess = () => resolve(request.result || []);
    request.onerror = () => reject(request.error);
  });
}

export async function deleteAIConversation(id: string): Promise<void> {
  const db = await getDB();

  return new Promise((resolve, reject) => {
    const transaction = db.transaction(STORES.AI_HISTORY, "readwrite");
    const store = transaction.objectStore(STORES.AI_HISTORY);
    const request = store.delete(id);

    request.onsuccess = () => resolve();
    request.onerror = () => reject(request.error);
  });
}

// ============================================================================
// LOCAL STORAGE - SETTINGS
// ============================================================================

export function getSettings(): UserSettings {
  try {
    const stored = localStorage.getItem(LOCAL_STORAGE_KEYS.USER_SETTINGS);
    if (stored) {
      return { ...DEFAULT_SETTINGS, ...JSON.parse(stored) };
    }
  } catch (e) {
    console.warn("Failed to load settings:", e);
  }
  return { ...DEFAULT_SETTINGS };
}

export function saveSettings(settings: Partial<UserSettings>): void {
  try {
    const current = getSettings();
    const merged = { ...current, ...settings };
    localStorage.setItem(
      LOCAL_STORAGE_KEYS.USER_SETTINGS,
      JSON.stringify(merged),
    );
  } catch (e) {
    console.warn("Failed to save settings:", e);
  }
}

export function getSetting<K extends keyof UserSettings>(
  key: K,
): UserSettings[K] {
  return getSettings()[key];
}

export function setSetting<K extends keyof UserSettings>(
  key: K,
  value: UserSettings[K],
): void {
  saveSettings({ [key]: value });
}

// ============================================================================
// LOCAL STORAGE - RECENT PROJECTS
// ============================================================================

export function getRecentProjects(): RecentProject[] {
  try {
    const stored = localStorage.getItem(LOCAL_STORAGE_KEYS.RECENT_PROJECTS);
    if (stored) {
      return JSON.parse(stored);
    }
  } catch (e) {
    console.warn("Failed to load recent projects:", e);
  }
  return [];
}

function saveRecentProjects(projects: RecentProject[]): void {
  try {
    localStorage.setItem(
      LOCAL_STORAGE_KEYS.RECENT_PROJECTS,
      JSON.stringify(projects),
    );
  } catch (e) {
    console.warn("Failed to save recent projects:", e);
  }
}

export function addToRecentProjects(project: RecentProject): void {
  const settings = getSettings();
  let recent = getRecentProjects();

  // Remove existing entry for this project
  recent = recent.filter((p) => p.id !== project.id);

  // Add to front
  recent.unshift(project);

  // Trim to max size
  recent = recent.slice(0, settings.recentProjectsMax);

  saveRecentProjects(recent);
}

export function removeFromRecentProjects(projectId: string): void {
  const recent = getRecentProjects().filter((p) => p.id !== projectId);
  saveRecentProjects(recent);
}

export function clearRecentProjects(): void {
  saveRecentProjects([]);
}

// ============================================================================
// LOCAL STORAGE - LAST PROJECT
// ============================================================================

export function getLastProjectId(): string | null {
  try {
    return localStorage.getItem(LOCAL_STORAGE_KEYS.LAST_PROJECT_ID);
  } catch {
    return null;
  }
}

export function setLastProjectId(id: string): void {
  try {
    localStorage.setItem(LOCAL_STORAGE_KEYS.LAST_PROJECT_ID, id);
  } catch (e) {
    console.warn("Failed to save last project ID:", e);
  }
}

// ============================================================================
// STORAGE QUOTA & CLEANUP
// ============================================================================

export async function getStorageEstimate(): Promise<{
  usage: number;
  quota: number;
} | null> {
  if ("storage" in navigator && "estimate" in navigator.storage) {
    try {
      const estimate = await navigator.storage.estimate();
      return {
        usage: estimate.usage || 0,
        quota: estimate.quota || 0,
      };
    } catch {
      return null;
    }
  }
  return null;
}

export async function clearAllData(): Promise<void> {
  // Clear IndexedDB
  const db = await getDB();
  const storeNames = [
    STORES.PROJECTS,
    STORES.ASSETS,
    STORES.AI_HISTORY,
    STORES.SETTINGS,
  ];

  for (const storeName of storeNames) {
    await new Promise<void>((resolve, reject) => {
      const transaction = db.transaction(storeName, "readwrite");
      const store = transaction.objectStore(storeName);
      const request = store.clear();
      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }

  // Clear localStorage
  Object.values(LOCAL_STORAGE_KEYS).forEach((key) => {
    localStorage.removeItem(key);
  });
}

export async function exportAllData(): Promise<Blob> {
  const projects = await listProjects();
  const settings = getSettings();
  const recentProjects = getRecentProjects();

  // Note: Assets are not included due to size - export separately if needed
  const exportData = {
    version: 1,
    exportedAt: Date.now(),
    projects,
    settings,
    recentProjects,
  };

  return new Blob([JSON.stringify(exportData, null, 2)], {
    type: "application/json",
  });
}

export async function importData(
  data: Blob,
): Promise<{ projectsImported: number }> {
  const text = await data.text();
  const parsed = JSON.parse(text);

  let projectsImported = 0;

  if (parsed.projects && Array.isArray(parsed.projects)) {
    for (const project of parsed.projects) {
      if (project.data && project.id) {
        await saveProject(project.data, project.thumbnail);
        projectsImported++;
      }
    }
  }

  if (parsed.settings) {
    saveSettings(parsed.settings);
  }

  return { projectsImported };
}

// ============================================================================
// INITIALIZATION
// ============================================================================

export async function initPersistence(): Promise<void> {
  try {
    await initDatabase();
    console.log("Persistence service initialized");
  } catch (e) {
    console.error("Failed to initialize persistence:", e);
  }
}

// Auto-initialize on import
initPersistence().catch(console.error);
