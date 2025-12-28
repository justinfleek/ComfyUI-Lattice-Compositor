/**
 * Project Storage Service
 *
 * Handles saving and loading compositor projects via the backend API.
 * Projects are stored as JSON files in the ComfyUI projects directory.
 */

import type { LatticeProject } from '@/types/project';
import { createLogger } from '@/utils/logger';
import { validateProjectStructure, ValidationError } from '@/utils/security';

const logger = createLogger('ProjectStorage');

// Base URL for compositor API endpoints
const API_BASE = '/lattice/compositor';

/**
 * Validate project ID format for security
 * Accepts UUIDs, timestamps, or alphanumeric IDs
 */
function isValidProjectId(projectId: string): boolean {
  // Allow UUIDs (with or without hyphens)
  const uuidPattern = /^[0-9a-f]{8}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{4}-?[0-9a-f]{12}$/i;
  // Allow alphanumeric with underscores (typical generated IDs like "project_1702345678901")
  const alphanumericPattern = /^[a-zA-Z0-9_-]{1,128}$/;

  return uuidPattern.test(projectId) || alphanumericPattern.test(projectId);
}

/**
 * Project metadata returned from list endpoint
 */
export interface ProjectInfo {
  id: string;
  name: string;
  created?: string;
  modified?: string;
  path?: string;
  error?: string;
}

/**
 * Save response from the backend
 */
export interface SaveResult {
  status: 'success' | 'error';
  project_id?: string;
  path?: string;
  message?: string;
}

/**
 * Load response from the backend
 */
export interface LoadResult {
  status: 'success' | 'error';
  project?: LatticeProject;
  project_id?: string;
  message?: string;
}

/**
 * List response from the backend
 */
export interface ListResult {
  status: 'success' | 'error';
  projects?: ProjectInfo[];
  message?: string;
}

/**
 * Save a project to the backend
 *
 * @param project - The project to save
 * @param projectId - Optional existing project ID (for overwriting)
 * @returns Save result with the project ID
 */
export async function saveProject(
  project: LatticeProject,
  projectId?: string
): Promise<SaveResult> {
  try {
    logger.info(`Saving project${projectId ? ` (${projectId})` : ''}...`);

    const response = await fetch(`${API_BASE}/save_project`, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
      },
      body: JSON.stringify({
        project,
        project_id: projectId,
      }),
    });

    const result = await response.json();

    if (result.status === 'success') {
      logger.info(`Project saved: ${result.project_id}`);
    } else {
      logger.error(`Failed to save project: ${result.message}`);
    }

    return result;
  } catch (error) {
    logger.error('Error saving project:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error',
    };
  }
}

/**
 * Load a project from the backend
 *
 * @param projectId - The project ID to load
 * @returns Load result with the project data
 */
export async function loadProject(projectId: string): Promise<LoadResult> {
  // Validate project ID format to prevent injection attacks
  if (!isValidProjectId(projectId)) {
    logger.error(`Invalid project ID format: ${projectId}`);
    return {
      status: 'error',
      message: 'Invalid project ID format',
    };
  }

  try {
    logger.info(`Loading project: ${projectId}...`);

    const response = await fetch(`${API_BASE}/load_project/${encodeURIComponent(projectId)}`);
    const result = await response.json();

    if (result.status === 'success') {
      logger.info(`Project loaded: ${projectId}`);
    } else {
      logger.error(`Failed to load project: ${result.message}`);
    }

    return result;
  } catch (error) {
    logger.error('Error loading project:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error',
    };
  }
}

/**
 * List all saved projects
 *
 * @returns List of project metadata
 */
export async function listProjects(): Promise<ListResult> {
  try {
    logger.info('Listing projects...');

    const response = await fetch(`${API_BASE}/list_projects`);
    const result = await response.json();

    if (result.status === 'success') {
      logger.info(`Found ${result.projects?.length || 0} projects`);
    } else {
      logger.error(`Failed to list projects: ${result.message}`);
    }

    return result;
  } catch (error) {
    logger.error('Error listing projects:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error',
    };
  }
}

/**
 * Delete a project from the backend
 *
 * @param projectId - The project ID to delete
 * @returns Delete result
 */
export async function deleteProject(projectId: string): Promise<{ status: string; message?: string }> {
  try {
    logger.info(`Deleting project: ${projectId}...`);

    const response = await fetch(`${API_BASE}/delete_project/${encodeURIComponent(projectId)}`, {
      method: 'DELETE',
    });
    const result = await response.json();

    if (result.status === 'success') {
      logger.info(`Project deleted: ${projectId}`);
    } else {
      logger.error(`Failed to delete project: ${result.message}`);
    }

    return result;
  } catch (error) {
    logger.error('Error deleting project:', error);
    return {
      status: 'error',
      message: error instanceof Error ? error.message : 'Unknown error',
    };
  }
}

/**
 * Check if the backend API is available
 *
 * @returns True if the API is reachable
 */
export async function isApiAvailable(): Promise<boolean> {
  try {
    const response = await fetch(`${API_BASE}/list_projects`, {
      method: 'GET',
    });
    return response.ok;
  } catch {
    return false;
  }
}

/**
 * Export project as downloadable JSON file (client-side fallback)
 *
 * @param project - The project to export
 * @param filename - Optional filename (without extension)
 */
export function exportProjectAsFile(project: LatticeProject, filename?: string): void {
  const name = filename || project.meta?.name || 'lattice-project';
  const safeName = name.replace(/[^a-zA-Z0-9-_]/g, '_');

  const blob = new Blob([JSON.stringify(project, null, 2)], {
    type: 'application/json',
  });

  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = `${safeName}.lattice.json`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);

  logger.info(`Exported project: ${a.download}`);
}

/**
 * Import project from uploaded JSON file (client-side)
 *
 * @param file - The file to import
 * @returns The imported project
 */
export async function importProjectFromFile(file: File): Promise<LatticeProject> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();

    reader.onload = () => {
      try {
        const data = JSON.parse(reader.result as string);

        // Validate project structure before accepting
        validateProjectStructure(data, `Project file '${file.name}'`);

        const project = data as LatticeProject;
        logger.info(`Imported project: ${project.meta?.name || file.name}`);
        resolve(project);
      } catch (error) {
        if (error instanceof ValidationError) {
          reject(new Error(`Invalid project file: ${error.message}`));
        } else {
          reject(new Error('Invalid project file: Failed to parse JSON'));
        }
      }
    };

    reader.onerror = () => {
      reject(new Error('Failed to read file'));
    };

    reader.readAsText(file);
  });
}
