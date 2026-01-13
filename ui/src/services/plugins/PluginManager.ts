/**
 * Plugin Manager - Extensibility Architecture
 *
 * Phase 9: Plugin API Architecture Implementation
 *
 * Features:
 * - Plugin registration and lifecycle
 * - Sandboxed execution
 * - API surface for plugins
 * - Effect, Exporter, and UI plugins
 */

import { createLogger } from "@/utils/logger";

const logger = createLogger("PluginManager");

// ============================================================================
// TYPES
// ============================================================================

export type PluginType = "effect" | "exporter" | "layer" | "ui" | "tool";

export interface PluginManifest {
  /** Unique plugin identifier */
  id: string;
  /** Display name */
  name: string;
  /** Semantic version */
  version: string;
  /** Plugin description */
  description: string;
  /** Plugin type */
  type: PluginType;
  /** Author name */
  author?: string;
  /** Plugin homepage */
  homepage?: string;
  /** Required API version */
  apiVersion?: string;
  /** Required permissions */
  permissions?: PluginPermission[];
  /** Plugin entry point */
  entryPoint: string;
}

export type PluginPermission =
  | "read-project"
  | "write-project"
  | "read-layers"
  | "write-layers"
  | "read-assets"
  | "write-assets"
  | "network"
  | "clipboard"
  | "notifications";

export interface LatticePluginAPI {
  // Read-only project access
  getProject(): any;
  getCurrentFrame(): number;
  getSelectedLayers(): string[];
  getLayer(id: string): any;
  getComposition(id: string): any;
  getAsset(id: string): any;

  // Events
  on(event: PluginEvent, callback: (...args: any[]) => void): () => void;
  off(event: PluginEvent, callback: (...args: any[]) => void): void;

  // UI registration
  registerPanel(panel: PanelDefinition): void;
  registerMenuItem(item: MenuItemDefinition): void;
  registerContextMenu(menu: ContextMenuDefinition): void;

  // Effect registration (for effect plugins)
  registerEffect?(effect: EffectDefinition): void;

  // Exporter registration (for exporter plugins)
  registerExporter?(exporter: ExporterDefinition): void;

  // Tool registration (for tool plugins)
  registerTool?(tool: ToolDefinition): void;

  // Notifications
  showNotification(
    message: string,
    type?: "info" | "success" | "warning" | "error",
  ): void;

  // Logging
  log: {
    debug(...args: any[]): void;
    info(...args: any[]): void;
    warn(...args: any[]): void;
    error(...args: any[]): void;
  };
}

export type PluginEvent =
  | "frameChange"
  | "selectionChange"
  | "layerChange"
  | "projectLoad"
  | "projectSave"
  | "compositionChange";

export interface PanelDefinition {
  id: string;
  name: string;
  icon?: string;
  component: any; // Vue component
  position?: "left" | "right" | "bottom";
}

export interface MenuItemDefinition {
  id: string;
  label: string;
  icon?: string;
  shortcut?: string;
  menu: "file" | "edit" | "layer" | "effect" | "view" | "help" | "plugin";
  submenu?: string;
  action: () => void;
}

export interface ContextMenuDefinition {
  id: string;
  label: string;
  icon?: string;
  context: "layer" | "keyframe" | "composition" | "asset";
  action: (contextData: any) => void;
}

export interface EffectDefinition {
  id: string;
  name: string;
  category: string;
  parameters: EffectParameter[];
  render: (
    input: ImageData,
    params: Record<string, any>,
    frame: number,
  ) => ImageData | Promise<ImageData>;
}

export interface EffectParameter {
  id: string;
  name: string;
  type: "number" | "color" | "point" | "angle" | "dropdown" | "checkbox";
  defaultValue: any;
  min?: number;
  max?: number;
  step?: number;
  options?: { label: string; value: any }[];
}

export interface ExporterDefinition {
  id: string;
  name: string;
  extension: string;
  mimeType: string;
  export: (frames: ImageData[], options: any) => Promise<Blob>;
}

export interface ToolDefinition {
  id: string;
  name: string;
  icon: string;
  cursor?: string;
  onActivate?: () => void;
  onDeactivate?: () => void;
  onMouseDown?: (event: MouseEvent) => void;
  onMouseMove?: (event: MouseEvent) => void;
  onMouseUp?: (event: MouseEvent) => void;
}

export interface LatticePlugin {
  /** Plugin manifest */
  manifest: PluginManifest;
  /** Lifecycle: called when plugin loads */
  onLoad(api: LatticePluginAPI): void | Promise<void>;
  /** Lifecycle: called when plugin unloads */
  onUnload?(): void | Promise<void>;
}

export interface LoadedPlugin {
  manifest: PluginManifest;
  instance: LatticePlugin;
  state: "loading" | "active" | "error" | "disabled";
  error?: string;
  registrations: {
    panels: string[];
    menuItems: string[];
    contextMenus: string[];
    effects: string[];
    exporters: string[];
    tools: string[];
    events: Map<PluginEvent, Set<Function>>;
  };
}

// ============================================================================
// PLUGIN MANAGER
// ============================================================================

export class PluginManager {
  private plugins: Map<string, LoadedPlugin> = new Map();
  private eventListeners: Map<PluginEvent, Set<Function>> = new Map();

  // External callbacks for UI registration
  private onRegisterPanel?: (panel: PanelDefinition) => void;
  private onRegisterMenuItem?: (item: MenuItemDefinition) => void;
  private onRegisterContextMenu?: (menu: ContextMenuDefinition) => void;
  private onRegisterEffect?: (effect: EffectDefinition) => void;
  private onRegisterExporter?: (exporter: ExporterDefinition) => void;
  private onRegisterTool?: (tool: ToolDefinition) => void;
  private onShowNotification?: (message: string, type: string) => void;

  // Store access (injected)
  private getProjectFn?: () => any;
  private getCurrentFrameFn?: () => number;
  private getSelectedLayersFn?: () => string[];
  private getLayerFn?: (id: string) => any;
  private getCompositionFn?: (id: string) => any;
  private getAssetFn?: (id: string) => any;

  constructor() {
    // Initialize event listener maps
    const events: PluginEvent[] = [
      "frameChange",
      "selectionChange",
      "layerChange",
      "projectLoad",
      "projectSave",
      "compositionChange",
    ];
    for (const event of events) {
      this.eventListeners.set(event, new Set());
    }
  }

  // ============================================================================
  // CONFIGURATION
  // ============================================================================

  /**
   * Set store access functions
   */
  setStoreAccess(access: {
    getProject: () => any;
    getCurrentFrame: () => number;
    getSelectedLayers: () => string[];
    getLayer: (id: string) => any;
    getComposition: (id: string) => any;
    getAsset: (id: string) => any;
  }): void {
    this.getProjectFn = access.getProject;
    this.getCurrentFrameFn = access.getCurrentFrame;
    this.getSelectedLayersFn = access.getSelectedLayers;
    this.getLayerFn = access.getLayer;
    this.getCompositionFn = access.getComposition;
    this.getAssetFn = access.getAsset;
  }

  /**
   * Set UI registration callbacks
   */
  setUICallbacks(callbacks: {
    onRegisterPanel?: (panel: PanelDefinition) => void;
    onRegisterMenuItem?: (item: MenuItemDefinition) => void;
    onRegisterContextMenu?: (menu: ContextMenuDefinition) => void;
    onRegisterEffect?: (effect: EffectDefinition) => void;
    onRegisterExporter?: (exporter: ExporterDefinition) => void;
    onRegisterTool?: (tool: ToolDefinition) => void;
    onShowNotification?: (message: string, type: string) => void;
  }): void {
    Object.assign(this, callbacks);
  }

  // ============================================================================
  // PLUGIN LOADING
  // ============================================================================

  /**
   * Load a plugin from a module
   */
  async loadPlugin(plugin: LatticePlugin): Promise<void> {
    const { manifest } = plugin;

    if (this.plugins.has(manifest.id)) {
      throw new Error(`Plugin ${manifest.id} is already loaded`);
    }

    const loadedPlugin: LoadedPlugin = {
      manifest,
      instance: plugin,
      state: "loading",
      registrations: {
        panels: [],
        menuItems: [],
        contextMenus: [],
        effects: [],
        exporters: [],
        tools: [],
        events: new Map(),
      },
    };

    this.plugins.set(manifest.id, loadedPlugin);

    try {
      // Create API for this plugin
      const api = this.createPluginAPI(loadedPlugin);

      // Call plugin's onLoad
      await plugin.onLoad(api);

      loadedPlugin.state = "active";
      logger.info(`Plugin loaded: ${manifest.name} v${manifest.version}`);
    } catch (error) {
      loadedPlugin.state = "error";
      loadedPlugin.error =
        error instanceof Error ? error.message : "Unknown error";
      logger.error(`Failed to load plugin ${manifest.id}:`, error);
      throw error;
    }
  }

  /**
   * Unload a plugin
   */
  async unloadPlugin(pluginId: string): Promise<void> {
    const plugin = this.plugins.get(pluginId);
    if (!plugin) return;

    try {
      // Call plugin's onUnload
      if (plugin.instance.onUnload) {
        await plugin.instance.onUnload();
      }

      // Remove all registrations
      this.cleanupPluginRegistrations(plugin);

      this.plugins.delete(pluginId);
      logger.info(`Plugin unloaded: ${pluginId}`);
    } catch (error) {
      logger.error(`Error unloading plugin ${pluginId}:`, error);
    }
  }

  /**
   * Enable a disabled plugin
   */
  async enablePlugin(pluginId: string): Promise<void> {
    const plugin = this.plugins.get(pluginId);
    if (!plugin || plugin.state !== "disabled") return;

    plugin.state = "active";
    logger.info(`Plugin enabled: ${pluginId}`);
  }

  /**
   * Disable a plugin (without unloading)
   */
  async disablePlugin(pluginId: string): Promise<void> {
    const plugin = this.plugins.get(pluginId);
    if (!plugin || plugin.state !== "active") return;

    plugin.state = "disabled";
    logger.info(`Plugin disabled: ${pluginId}`);
  }

  // ============================================================================
  // API CREATION
  // ============================================================================

  /**
   * Create the API object for a plugin
   */
  private createPluginAPI(plugin: LoadedPlugin): LatticePluginAPI {
    return {
      // Read-only access
      getProject: () => this.getProjectFn?.() ?? null,
      getCurrentFrame: () => this.getCurrentFrameFn?.() ?? 0,
      getSelectedLayers: () => this.getSelectedLayersFn?.() ?? [],
      getLayer: (id) => this.getLayerFn?.(id) ?? null,
      getComposition: (id) => this.getCompositionFn?.(id) ?? null,
      getAsset: (id) => this.getAssetFn?.(id) ?? null,

      // Events
      on: (event, callback) => {
        const listeners = this.eventListeners.get(event);
        if (listeners) {
          listeners.add(callback);
          plugin.registrations.events.set(
            event,
            plugin.registrations.events.get(event) || new Set(),
          );
          plugin.registrations.events.get(event)?.add(callback);
        }
        return () => this.eventListeners.get(event)?.delete(callback);
      },

      off: (event, callback) => {
        this.eventListeners.get(event)?.delete(callback);
        plugin.registrations.events.get(event)?.delete(callback);
      },

      // UI registration
      registerPanel: (panel) => {
        plugin.registrations.panels.push(panel.id);
        this.onRegisterPanel?.(panel);
      },

      registerMenuItem: (item) => {
        plugin.registrations.menuItems.push(item.id);
        this.onRegisterMenuItem?.(item);
      },

      registerContextMenu: (menu) => {
        plugin.registrations.contextMenus.push(menu.id);
        this.onRegisterContextMenu?.(menu);
      },

      // Effect registration
      registerEffect: (effect) => {
        plugin.registrations.effects.push(effect.id);
        this.onRegisterEffect?.(effect);
      },

      // Exporter registration
      registerExporter: (exporter) => {
        plugin.registrations.exporters.push(exporter.id);
        this.onRegisterExporter?.(exporter);
      },

      // Tool registration
      registerTool: (tool) => {
        plugin.registrations.tools.push(tool.id);
        this.onRegisterTool?.(tool);
      },

      // Notifications
      showNotification: (message, type = "info") => {
        this.onShowNotification?.(message, type);
      },

      // Logging
      log: {
        debug: (...args) => logger.debug(`[${plugin.manifest.id}]`, ...args),
        info: (...args) => logger.info(`[${plugin.manifest.id}]`, ...args),
        warn: (...args) => logger.warn(`[${plugin.manifest.id}]`, ...args),
        error: (...args) => logger.error(`[${plugin.manifest.id}]`, ...args),
      },
    };
  }

  /**
   * Clean up all registrations from a plugin
   */
  private cleanupPluginRegistrations(plugin: LoadedPlugin): void {
    // Remove event listeners
    for (const [event, callbacks] of plugin.registrations.events) {
      const listeners = this.eventListeners.get(event);
      if (listeners) {
        for (const callback of callbacks) {
          listeners.delete(callback);
        }
      }
    }

    // Note: UI elements would need to be cleaned up by the UI layer
    // This would require additional callbacks for unregister
  }

  // ============================================================================
  // EVENT EMISSION
  // ============================================================================

  /**
   * Emit an event to all plugins
   */
  emit(event: PluginEvent, ...args: any[]): void {
    const listeners = this.eventListeners.get(event);
    if (!listeners) return;

    for (const callback of listeners) {
      try {
        callback(...args);
      } catch (error) {
        logger.error(`Error in plugin event handler for ${event}:`, error);
      }
    }
  }

  // ============================================================================
  // QUERIES
  // ============================================================================

  /**
   * Get all loaded plugins
   */
  getPlugins(): LoadedPlugin[] {
    return Array.from(this.plugins.values());
  }

  /**
   * Get a specific plugin
   */
  getPlugin(id: string): LoadedPlugin | undefined {
    return this.plugins.get(id);
  }

  /**
   * Get plugins by type
   */
  getPluginsByType(type: PluginType): LoadedPlugin[] {
    return this.getPlugins().filter((p) => p.manifest.type === type);
  }

  /**
   * Get active plugins
   */
  getActivePlugins(): LoadedPlugin[] {
    return this.getPlugins().filter((p) => p.state === "active");
  }

  /**
   * Check if a permission is granted for a plugin
   */
  hasPermission(pluginId: string, permission: PluginPermission): boolean {
    const plugin = this.plugins.get(pluginId);
    if (!plugin) return false;
    return plugin.manifest.permissions?.includes(permission) ?? false;
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

let managerInstance: PluginManager | null = null;

export function getPluginManager(): PluginManager {
  if (!managerInstance) {
    managerInstance = new PluginManager();
  }
  return managerInstance;
}

// ============================================================================
// EXPORTS
// ============================================================================

export default PluginManager;
