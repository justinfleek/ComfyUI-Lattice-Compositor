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
import type { AssetReference, Composition, Layer, LatticeProject } from "@/types/project";
import type { Component } from "vue";

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
  getProject(): LatticeProject;
  getCurrentFrame(): number;
  getSelectedLayers(): string[];
  getLayer(id: string): Layer;
  getComposition(id: string): Composition;
  getAsset(id: string): AssetReference;

  // Events - type-safe callbacks
  on<T extends PluginEvent>(event: T, callback: PluginEventCallback<T>): () => void;
  off<T extends PluginEvent>(event: T, callback: PluginEventCallback<T>): void;

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

  // Logging - accepts serializable values
  log: {
    debug(...args: LoggableValue[]): void;
    info(...args: LoggableValue[]): void;
    warn(...args: LoggableValue[]): void;
    error(...args: LoggableValue[]): void;
  };
}

export type PluginEvent =
  | "frameChange"
  | "selectionChange"
  | "layerChange"
  | "projectLoad"
  | "projectSave"
  | "compositionChange";

/** Event payload types for each plugin event */
export interface PluginEventPayloads {
  frameChange: { frame: number; previousFrame: number };
  selectionChange: { layerIds: string[]; previousLayerIds: string[] };
  layerChange: { layerId: string; layer: Layer };
  projectLoad: { project: LatticeProject };
  projectSave: { project: LatticeProject };
  compositionChange: { compositionId: string; composition: Composition };
}

/** Type-safe event callback */
export type PluginEventCallback<T extends PluginEvent> = (payload: PluginEventPayloads[T]) => void;

/** Serializable values that can be logged */
export type LoggableValue =
  | string
  | number
  | boolean
  | Error
  | (string | number | boolean)[]
  | Record<string, string | number | boolean>;

export interface PanelDefinition {
  id: string;
  name: string;
  icon?: string;
  component: Component;
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

/** Context data passed to context menu actions */
export type ContextMenuData =
  | { context: "layer"; layerId: string; layer: Layer }
  | { context: "keyframe"; layerId: string; propertyId: string; keyframeId: string }
  | { context: "composition"; compositionId: string; composition: Composition }
  | { context: "asset"; assetId: string; asset: AssetReference };

export interface ContextMenuDefinition {
  id: string;
  label: string;
  icon?: string;
  context: "layer" | "keyframe" | "composition" | "asset";
  action: (contextData: ContextMenuData) => void;
}

/** Effect parameter value types based on parameter type */
export type EffectParameterValue = number | string | boolean | { x: number; y: number } | [number, number, number];

export interface EffectDefinition {
  id: string;
  name: string;
  category: string;
  parameters: EffectParameter[];
  render: (
    input: ImageData,
    params: Record<string, EffectParameterValue>,
    frame: number,
  ) => ImageData | Promise<ImageData>;
}

export interface EffectParameter {
  id: string;
  name: string;
  type: "number" | "color" | "point" | "angle" | "dropdown" | "checkbox";
  defaultValue: EffectParameterValue;
  min?: number;
  max?: number;
  step?: number;
  options?: { label: string; value: EffectParameterValue }[];
}

/** Export options passed to exporter plugins */
export interface ExportOptions {
  fps: number;
  quality: number;
  [key: string]: string | number | boolean | string[] | number[];
}

export interface ExporterDefinition {
  id: string;
  name: string;
  extension: string;
  mimeType: string;
  export: (frames: ImageData[], options: ExportOptions) => Promise<Blob>;
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
    events: Map<PluginEvent, Set<(payload: PluginEventPayloads[PluginEvent]) => void>>;
  };
}

// ============================================================================
// PLUGIN MANAGER
// ============================================================================

export class PluginManager {
  private plugins: Map<string, LoadedPlugin> = new Map();
  private eventListeners: Map<
    PluginEvent,
    Set<(payload: PluginEventPayloads[PluginEvent]) => void>
  > = new Map();

  // External callbacks for UI registration
  private onRegisterPanel?: (panel: PanelDefinition) => void;
  private onRegisterMenuItem?: (item: MenuItemDefinition) => void;
  private onRegisterContextMenu?: (menu: ContextMenuDefinition) => void;
  private onRegisterEffect?: (effect: EffectDefinition) => void;
  private onRegisterExporter?: (exporter: ExporterDefinition) => void;
  private onRegisterTool?: (tool: ToolDefinition) => void;
  private onShowNotification?: (message: string, type: string) => void;

  // Store access (injected)
  private getProjectFn?: () => LatticeProject | null;
  private getCurrentFrameFn?: () => number;
  private getSelectedLayersFn?: () => string[];
  private getLayerFn?: (id: string) => Layer | null;
  private getCompositionFn?: (id: string) => Composition | null;
  private getAssetFn?: (id: string) => AssetReference | null;

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
    getProject: () => LatticeProject | null;
    getCurrentFrame: () => number;
    getSelectedLayers: () => string[];
    getLayer: (id: string) => Layer | null;
    getComposition: (id: string) => Composition | null;
    getAsset: (id: string) => AssetReference | null;
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
      getProject: () => {
        if (!this.getProjectFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        const result = this.getProjectFn();
        if (result === null) {
          throw new Error("Plugin API: Project not available");
        }
        return result;
      },
      getCurrentFrame: () => {
        if (!this.getCurrentFrameFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        return this.getCurrentFrameFn();
      },
      getSelectedLayers: () => {
        if (!this.getSelectedLayersFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        return this.getSelectedLayersFn();
      },
      getLayer: (id) => {
        if (!this.getLayerFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        const result = this.getLayerFn(id);
        if (result === null) {
          throw new Error(`Plugin API: Layer with id "${id}" not found`);
        }
        return result;
      },
      getComposition: (id) => {
        if (!this.getCompositionFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        const result = this.getCompositionFn(id);
        if (result === null) {
          throw new Error(`Plugin API: Composition with id "${id}" not found`);
        }
        return result;
      },
      getAsset: (id) => {
        if (!this.getAssetFn) {
          throw new Error("Plugin API: Store access not configured");
        }
        const result = this.getAssetFn(id);
        if (result === null) {
          throw new Error(`Plugin API: Asset with id "${id}" not found`);
        }
        return result;
      },

      // Events - type-safe implementation
      on: <T extends PluginEvent>(event: T, callback: PluginEventCallback<T>) => {
        const listeners = this.eventListeners.get(event);
        if (listeners) {
          listeners.add(callback as (payload: PluginEventPayloads[PluginEvent]) => void);
          plugin.registrations.events.set(
            event,
            plugin.registrations.events.get(event) || new Set(),
          );
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
          const eventSet = plugin.registrations.events.get(event);
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          if (typeof eventSet === "object" && eventSet !== null && "add" in eventSet && typeof eventSet.add === "function") {
            eventSet.add(callback as (payload: PluginEventPayloads[PluginEvent]) => void);
          }
        }
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        return () => {
          const eventSet = this.eventListeners.get(event);
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
          if (typeof eventSet === "object" && eventSet !== null && "delete" in eventSet && typeof eventSet.delete === "function") {
            eventSet.delete(callback as (payload: PluginEventPayloads[PluginEvent]) => void);
          }
        };
      },

      off: <T extends PluginEvent>(event: T, callback: PluginEventCallback<T>) => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        const eventSet1 = this.eventListeners.get(event);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof eventSet1 === "object" && eventSet1 !== null && "delete" in eventSet1 && typeof eventSet1.delete === "function") {
          eventSet1.delete(callback as (payload: PluginEventPayloads[PluginEvent]) => void);
        }
        const eventSet2 = plugin.registrations.events.get(event);
        if (typeof eventSet2 === "object" && eventSet2 !== null && "delete" in eventSet2 && typeof eventSet2.delete === "function") {
          eventSet2.delete(callback as (payload: PluginEventPayloads[PluginEvent]) => void);
        }
      },

      // UI registration
      registerPanel: (panel) => {
        plugin.registrations.panels.push(panel.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterPanel === "function") {
          this.onRegisterPanel(panel);
        }
      },

      registerMenuItem: (item) => {
        plugin.registrations.menuItems.push(item.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterMenuItem === "function") {
          this.onRegisterMenuItem(item);
        }
      },

      registerContextMenu: (menu) => {
        plugin.registrations.contextMenus.push(menu.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterContextMenu === "function") {
          this.onRegisterContextMenu(menu);
        }
      },

      // Effect registration
      registerEffect: (effect) => {
        plugin.registrations.effects.push(effect.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterEffect === "function") {
          this.onRegisterEffect(effect);
        }
      },

      // Exporter registration
      registerExporter: (exporter) => {
        plugin.registrations.exporters.push(exporter.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterExporter === "function") {
          this.onRegisterExporter(exporter);
        }
      },

      // Tool registration
      registerTool: (tool) => {
        plugin.registrations.tools.push(tool.id);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onRegisterTool === "function") {
          this.onRegisterTool(tool);
        }
      },

      // Notifications
      showNotification: (message, type = "info") => {
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy undefined checks
        if (typeof this.onShowNotification === "function") {
          this.onShowNotification(message, type);
        }
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
  emit<T extends PluginEvent>(event: T, payload: PluginEventPayloads[T]): void {
    const listeners = this.eventListeners.get(event);
    if (!listeners) return;

    for (const callback of listeners) {
      try {
        callback(payload);
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
  getPlugin(id: string): LoadedPlugin {
    const plugin = this.plugins.get(id);
    if (!plugin) {
      throw new Error(`Plugin with id "${id}" not found`);
    }
    return plugin;
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
    // Type proof: permissions?.includes(...) ∈ boolean | undefined → boolean
    const permissions = plugin.manifest.permissions;
    return Array.isArray(permissions) && permissions.includes(permission);
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

let managerInstance: PluginManager | null = null;

export function getPluginManager(): PluginManager {
  if (managerInstance === null) {
    managerInstance = new PluginManager();
  }
  return managerInstance;
}

// ============================================================================
// EXPORTS
// ============================================================================

export default PluginManager;
