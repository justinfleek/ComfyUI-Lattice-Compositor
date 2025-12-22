/**
 * Plugin System Module
 *
 * Plugin API architecture for extensibility
 */

export {
  PluginManager,
  getPluginManager,
  type PluginType,
  type PluginManifest,
  type PluginPermission,
  type WeylPluginAPI,
  type PluginEvent,
  type PanelDefinition,
  type MenuItemDefinition,
  type ContextMenuDefinition,
  type EffectDefinition,
  type EffectParameter,
  type ExporterDefinition,
  type ToolDefinition,
  type WeylPlugin,
  type LoadedPlugin,
} from './PluginManager';
