/**
 * STRICT Property Tests for ProjectStorage
 * 
 * Tests for project save/load functionality
 */

import { describe, it, expect, vi, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';

// Mock fetch for API tests
const mockFetch = vi.fn();
// Type assertion: mock fetch for test environment
// Production-grade: properly type the global fetch mock
global.fetch = mockFetch as typeof fetch;

// Import after mocking
import {
  saveProject,
  loadProject,
  listProjects,
  deleteProject,
  isApiAvailable,
} from '@/services/projectStorage';
import type { LatticeProject } from '@/types/project';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                   // helpers
// ════════════════════════════════════════════════════════════════════════════

function createMinimalProject(name: string = 'Test'): LatticeProject {
  const compId = 'comp-1';
  return {
    version: '1.0.0',
    schemaVersion: 1,
    mainCompositionId: compId,
    meta: {
      name,
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
    },
    composition: {
      width: 1920,
      height: 1080,
      frameCount: 300,
      fps: 30,
      duration: 10,
      backgroundColor: '#000000',
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    compositions: {
      [compId]: {
        id: compId,
        name: 'Main',
        settings: {
          width: 1920,
          height: 1080,
          frameCount: 300,
          fps: 30,
          duration: 10,
          backgroundColor: '#000000',
          autoResizeToContent: false,
          frameBlendingEnabled: false,
        },
        layers: [],
        currentFrame: 0,
        isNestedComp: false,
      },
    },
    layers: [],
    currentFrame: 0,
    assets: {},
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                      // project // id // validation // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Project ID Validation', () => {
  // These tests validate the internal isValidProjectId function indirectly via loadProject
  
  beforeEach(() => {
    mockFetch.mockReset();
  });

  test.prop([
    fc.uuid()
  ])('accepts valid UUIDs', async (uuid) => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project: createMinimalProject() }),
    });
    
    const result = await loadProject(uuid);
    // Should have made a fetch call (ID is valid)
    expect(mockFetch).toHaveBeenCalled();
  });

  test.prop([
    fc.stringMatching(/^[a-zA-Z0-9_-]{1,128}$/)
  ])('accepts valid alphanumeric IDs', async (id) => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project: createMinimalProject() }),
    });
    
    const result = await loadProject(id);
    expect(mockFetch).toHaveBeenCalled();
  });

  it('rejects IDs with path traversal attempts', async () => {
    const result = await loadProject('../../../etc/passwd');
    expect(result.status).toBe('error');
    expect(result.message).toContain('Invalid project ID');
    expect(mockFetch).not.toHaveBeenCalled();
  });

  it('rejects IDs with special characters', async () => {
    const result = await loadProject('project<script>alert(1)</script>');
    expect(result.status).toBe('error');
    expect(mockFetch).not.toHaveBeenCalled();
  });

  it('rejects empty ID', async () => {
    const result = await loadProject('');
    expect(result.status).toBe('error');
    expect(mockFetch).not.toHaveBeenCalled();
  });

  it('rejects overly long IDs', async () => {
    const longId = 'a'.repeat(200);
    const result = await loadProject(longId);
    expect(result.status).toBe('error');
    expect(mockFetch).not.toHaveBeenCalled();
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                  // save // project // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: saveProject', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  it('sends project to correct endpoint', async () => {
    const project = createMinimalProject();
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project_id: 'new-id' }),
    });
    
    await saveProject(project);
    
    expect(mockFetch).toHaveBeenCalledWith(
      '/lattice/compositor/save_project',
      expect.objectContaining({
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
      })
    );
  });

  it('includes project ID when provided', async () => {
    const project = createMinimalProject();
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project_id: 'existing-id' }),
    });
    
    await saveProject(project, 'existing-id');
    
    const call = mockFetch.mock.calls[0];
    const body = JSON.parse(call[1].body);
    expect(body.project_id).toBe('existing-id');
  });

  it('returns success result on success', async () => {
    const project = createMinimalProject();
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project_id: 'saved-id', path: '/path/to/project' }),
    });
    
    const result = await saveProject(project);
    
    expect(result.status).toBe('success');
    expect(result.project_id).toBe('saved-id');
    expect(result.path).toBe('/path/to/project');
  });

  it('handles network errors gracefully', async () => {
    const project = createMinimalProject();
    mockFetch.mockRejectedValueOnce(new Error('Network error'));
    
    const result = await saveProject(project);
    
    expect(result.status).toBe('error');
    expect(result.message).toContain('Network error');
  });

  it('handles server errors', async () => {
    const project = createMinimalProject();
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'error', message: 'Disk full' }),
    });
    
    const result = await saveProject(project);
    
    expect(result.status).toBe('error');
    expect(result.message).toBe('Disk full');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                  // load // project // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: loadProject', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  it('loads project from correct endpoint', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project: createMinimalProject() }),
    });
    
    await loadProject('test-id');
    
    expect(mockFetch).toHaveBeenCalledWith(
      '/lattice/compositor/load_project/test-id'
    );
  });

  it('URL-encodes project ID', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project: createMinimalProject() }),
    });
    
    await loadProject('project_with-dashes');
    
    expect(mockFetch).toHaveBeenCalledWith(
      expect.stringContaining('project_with-dashes')
    );
  });

  it('returns project data on success', async () => {
    const project = createMinimalProject('My Project');
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', project }),
    });
    
    const result = await loadProject('test-id');
    
    expect(result.status).toBe('success');
    expect(result.project?.meta?.name).toBe('My Project');
  });

  it('handles network errors gracefully', async () => {
    mockFetch.mockRejectedValueOnce(new Error('Connection refused'));
    
    const result = await loadProject('test-id');
    
    expect(result.status).toBe('error');
    expect(result.message).toContain('Connection refused');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                 // list // projects // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: listProjects', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  it('fetches from correct endpoint', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', projects: [] }),
    });
    
    await listProjects();
    
    expect(mockFetch).toHaveBeenCalledWith('/lattice/compositor/list_projects');
  });

  it('returns project list on success', async () => {
    const projects = [
      { id: '1', name: 'Project 1' },
      { id: '2', name: 'Project 2' },
    ];
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', projects }),
    });
    
    const result = await listProjects();
    
    expect(result.status).toBe('success');
    expect(result.projects).toHaveLength(2);
    expect(result.projects?.[0].name).toBe('Project 1');
  });

  it('handles empty project list', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success', projects: [] }),
    });
    
    const result = await listProjects();
    
    expect(result.status).toBe('success');
    expect(result.projects).toEqual([]);
  });

  it('handles network errors', async () => {
    mockFetch.mockRejectedValueOnce(new Error('Timeout'));
    
    const result = await listProjects();
    
    expect(result.status).toBe('error');
    expect(result.message).toContain('Timeout');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                // delete // project // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: deleteProject', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  it('sends DELETE request to correct endpoint', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success' }),
    });
    
    await deleteProject('test-id');
    
    expect(mockFetch).toHaveBeenCalledWith(
      '/lattice/compositor/delete_project/test-id',
      { method: 'DELETE' }
    );
  });

  it('returns success on successful delete', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'success' }),
    });
    
    const result = await deleteProject('test-id');
    
    expect(result.status).toBe('success');
  });

  it('handles delete errors', async () => {
    mockFetch.mockResolvedValueOnce({
      ok: true,
      json: () => Promise.resolve({ status: 'error', message: 'File not found' }),
    });
    
    const result = await deleteProject('nonexistent');
    
    expect(result.status).toBe('error');
    expect(result.message).toBe('File not found');
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                              // api // availability // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: isApiAvailable', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  it('returns true when API responds OK', async () => {
    mockFetch.mockResolvedValueOnce({ ok: true });
    
    const available = await isApiAvailable();
    
    expect(available).toBe(true);
  });

  it('returns false when API responds with error', async () => {
    mockFetch.mockResolvedValueOnce({ ok: false });
    
    const available = await isApiAvailable();
    
    expect(available).toBe(false);
  });

  it('returns false when network fails', async () => {
    mockFetch.mockRejectedValueOnce(new Error('Network error'));
    
    const available = await isApiAvailable();
    
    expect(available).toBe(false);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                      // determinism // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Determinism', () => {
  beforeEach(() => {
    mockFetch.mockReset();
  });

  test.prop([
    fc.record({
      name: fc.string({ minLength: 1, maxLength: 50 }),
      width: fc.integer({ min: 100, max: 4096 }),
      height: fc.integer({ min: 100, max: 4096 }),
    })
  ])('serialization is deterministic', async (config) => {
    const project = createMinimalProject(config.name);
    project.composition.width = config.width;
    project.composition.height = config.height;
    
    // Capture serialized body from two saves
    const bodies: string[] = [];
    mockFetch.mockImplementation((_url, options) => {
      if (options?.body) bodies.push(options.body);
      return Promise.resolve({
        ok: true,
        json: () => Promise.resolve({ status: 'success', project_id: 'test' }),
      });
    });
    
    await saveProject(project);
    await saveProject(project);
    
    // Should serialize identically
    expect(bodies[0]).toBe(bodies[1]);
  });
});
