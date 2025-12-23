/**
 * Export Template Management Service
 *
 * Allows users to save, load, and manage custom export configurations.
 * Templates are stored in localStorage for persistence.
 */

import type { ExportConfig, ExportTarget } from '@/types/export';

// ============================================================================
// Types
// ============================================================================

export interface ExportTemplate {
  id: string;
  name: string;
  description?: string;
  createdAt: number;
  modifiedAt: number;
  config: Partial<ExportConfig>;
}

export interface ExportTemplateStore {
  templates: ExportTemplate[];
  lastUsedTemplateId?: string;
}

// ============================================================================
// Storage Key
// ============================================================================

const STORAGE_KEY = 'weyl-export-templates';

// ============================================================================
// Default Templates
// ============================================================================

const DEFAULT_TEMPLATES: ExportTemplate[] = [
  {
    id: 'default-wan-5s',
    name: 'Wan 2.2 (5 seconds)',
    description: 'Standard Wan 2.2 export at 832x480, 81 frames',
    createdAt: Date.now(),
    modifiedAt: Date.now(),
    config: {
      target: 'wan22-i2v' as ExportTarget,
      width: 832,
      height: 480,
      frameCount: 81,
      fps: 16,
      exportReferenceFrame: true,
      exportLastFrame: false,
    },
  },
  {
    id: 'default-hd-sequence',
    name: 'HD Image Sequence',
    description: 'PNG sequence at 1280x720 for compositing',
    createdAt: Date.now(),
    modifiedAt: Date.now(),
    config: {
      target: 'custom-workflow' as ExportTarget,
      width: 1280,
      height: 720,
      frameCount: 81,
      fps: 24,
      exportReferenceFrame: true,
    },
  },
  {
    id: 'default-controlnet',
    name: 'ControlNet Depth',
    description: 'Single frame depth map for ControlNet',
    createdAt: Date.now(),
    modifiedAt: Date.now(),
    config: {
      target: 'controlnet-depth' as ExportTarget,
      width: 1024,
      height: 1024,
      frameCount: 1,
      exportDepthMap: true,
      exportReferenceFrame: true,
    },
  },
];

// ============================================================================
// Service Class
// ============================================================================

class ExportTemplateService {
  private store: ExportTemplateStore;

  constructor() {
    this.store = this.loadFromStorage();
  }

  // --------------------------------------------------------------------------
  // Storage
  // --------------------------------------------------------------------------

  private loadFromStorage(): ExportTemplateStore {
    try {
      const stored = localStorage.getItem(STORAGE_KEY);
      if (stored) {
        const parsed = JSON.parse(stored) as ExportTemplateStore;
        // Merge with defaults (don't overwrite user's default templates)
        const userTemplates = parsed.templates.filter(t => !t.id.startsWith('default-'));
        const defaultIds = new Set(DEFAULT_TEMPLATES.map(t => t.id));
        const existingDefaults = parsed.templates.filter(t => defaultIds.has(t.id));

        return {
          templates: [
            ...DEFAULT_TEMPLATES.filter(d => !existingDefaults.find(e => e.id === d.id)),
            ...existingDefaults,
            ...userTemplates,
          ],
          lastUsedTemplateId: parsed.lastUsedTemplateId,
        };
      }
    } catch (e) {
      console.warn('[ExportTemplates] Failed to load from storage:', e);
    }

    return {
      templates: [...DEFAULT_TEMPLATES],
    };
  }

  private saveToStorage(): void {
    try {
      localStorage.setItem(STORAGE_KEY, JSON.stringify(this.store));
    } catch (e) {
      console.warn('[ExportTemplates] Failed to save to storage:', e);
    }
  }

  // --------------------------------------------------------------------------
  // CRUD Operations
  // --------------------------------------------------------------------------

  /**
   * Get all templates
   */
  getTemplates(): ExportTemplate[] {
    return [...this.store.templates];
  }

  /**
   * Get a template by ID
   */
  getTemplate(id: string): ExportTemplate | undefined {
    return this.store.templates.find(t => t.id === id);
  }

  /**
   * Get the last used template
   */
  getLastUsedTemplate(): ExportTemplate | undefined {
    if (this.store.lastUsedTemplateId) {
      return this.getTemplate(this.store.lastUsedTemplateId);
    }
    return undefined;
  }

  /**
   * Save a new template
   */
  saveTemplate(
    name: string,
    config: Partial<ExportConfig>,
    description?: string
  ): ExportTemplate {
    const now = Date.now();
    const template: ExportTemplate = {
      id: `user-${now}-${Math.random().toString(36).slice(2, 8)}`,
      name,
      description,
      createdAt: now,
      modifiedAt: now,
      config,
    };

    this.store.templates.push(template);
    this.saveToStorage();

    console.log(`[ExportTemplates] Saved template: ${name}`);
    return template;
  }

  /**
   * Update an existing template
   */
  updateTemplate(
    id: string,
    updates: Partial<Pick<ExportTemplate, 'name' | 'description' | 'config'>>
  ): ExportTemplate | null {
    const index = this.store.templates.findIndex(t => t.id === id);
    if (index === -1) return null;

    // Don't allow modifying default templates directly
    if (id.startsWith('default-')) {
      console.warn('[ExportTemplates] Cannot modify default templates');
      return null;
    }

    this.store.templates[index] = {
      ...this.store.templates[index],
      ...updates,
      modifiedAt: Date.now(),
    };

    this.saveToStorage();
    return this.store.templates[index];
  }

  /**
   * Delete a template
   */
  deleteTemplate(id: string): boolean {
    // Don't allow deleting default templates
    if (id.startsWith('default-')) {
      console.warn('[ExportTemplates] Cannot delete default templates');
      return false;
    }

    const index = this.store.templates.findIndex(t => t.id === id);
    if (index === -1) return false;

    this.store.templates.splice(index, 1);

    // Clear lastUsedTemplateId if it was deleted
    if (this.store.lastUsedTemplateId === id) {
      this.store.lastUsedTemplateId = undefined;
    }

    this.saveToStorage();
    return true;
  }

  /**
   * Mark a template as last used
   */
  setLastUsed(id: string): void {
    if (this.getTemplate(id)) {
      this.store.lastUsedTemplateId = id;
      this.saveToStorage();
    }
  }

  /**
   * Duplicate a template (useful for customizing defaults)
   */
  duplicateTemplate(id: string, newName?: string): ExportTemplate | null {
    const original = this.getTemplate(id);
    if (!original) return null;

    return this.saveTemplate(
      newName || `${original.name} (Copy)`,
      { ...original.config },
      original.description
    );
  }

  /**
   * Export templates to JSON (for backup/sharing)
   */
  exportToJson(): string {
    const userTemplates = this.store.templates.filter(t => !t.id.startsWith('default-'));
    return JSON.stringify(userTemplates, null, 2);
  }

  /**
   * Import templates from JSON
   */
  importFromJson(json: string): number {
    try {
      const templates = JSON.parse(json) as ExportTemplate[];
      let imported = 0;

      for (const template of templates) {
        // Skip if template with same ID already exists
        if (this.getTemplate(template.id)) continue;

        // Regenerate ID to avoid conflicts
        const newTemplate: ExportTemplate = {
          ...template,
          id: `imported-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`,
          createdAt: Date.now(),
          modifiedAt: Date.now(),
        };

        this.store.templates.push(newTemplate);
        imported++;
      }

      if (imported > 0) {
        this.saveToStorage();
        console.log(`[ExportTemplates] Imported ${imported} templates`);
      }

      return imported;
    } catch (e) {
      console.error('[ExportTemplates] Failed to import:', e);
      return 0;
    }
  }

  /**
   * Reset to default templates only
   */
  resetToDefaults(): void {
    this.store = {
      templates: [...DEFAULT_TEMPLATES],
    };
    this.saveToStorage();
    console.log('[ExportTemplates] Reset to defaults');
  }
}

// ============================================================================
// Singleton Export
// ============================================================================

export const exportTemplateService = new ExportTemplateService();
