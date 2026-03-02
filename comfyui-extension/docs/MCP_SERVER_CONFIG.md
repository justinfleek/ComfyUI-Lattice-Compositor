# MCP Server Configuration for Lattice Compositor

> **Purpose:** MCP server configuration to expose software capabilities and database queries to LLM agents
> **Status:** 🏗️ FOUNDATION DESIGN
> **Last Updated:** 2026-01-23

**CRITICAL:** This MCP server acts as the interface between LLM agents and the Lattice Compositor software. It exposes:
1. Database queries (DuckDB)
2. Software capabilities (features, APIs, operations)
3. Project structure and domain ontology
4. Feature flag status

---

## MCP Server Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    LLM Agent (Claude/GPT)                   │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ (MCP Protocol)
┌─────────────────────────────────────────────────────────────┐
│              MCP Server (Node.js/Python)                    │
│  - Exposes resources (database, capabilities)              │
│  - Exposes tools (queries, operations)                      │
│  - Exposes prompts (context, instructions)                  │
└─────────────────────────────────────────────────────────────┘
                          │
        ┌─────────────────┴─────────────────┐
        ▼                                   ▼
┌──────────────────┐            ┌──────────────────────┐
│   DuckDB         │            │   Software APIs      │
│   Database       │            │   (Haskell/PS/TS)    │
└──────────────────┘            └──────────────────────┘
```

---

## Configuration File

**Location:** `.cursor/mcp.json` or `opencode.json` (MCP section)

```json
{
  "mcp": {
    "lattice-compositor": {
      "type": "local",
      "enabled": true,
      "command": "node",
      "args": ["./scripts/mcp-server.js"],
      "env": {
        "PROJECT_ROOT": "${workspaceFolder}",
        "DB_PATH": "${workspaceFolder}/.lattice/database.duckdb",
        "FEATURE_FLAGS_PATH": "${workspaceFolder}/.lattice/feature-flags.json"
      }
    }
  }
}
```

---

## MCP Server Implementation

**File:** `scripts/mcp-server.js`

```javascript
#!/usr/bin/env node
/**
 * Lattice Compositor MCP Server
 * 
 * Exposes:
 * - Resources: Database schema, feature flags, project structure
 * - Tools: Database queries, software operations
 * - Prompts: Context-aware prompts for LLM agents
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { 
  CallToolRequestSchema,
  ListResourcesRequestSchema,
  ListToolsRequestSchema,
  ReadResourceRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import Database from 'better-sqlite3';
import { readFileSync } from 'fs';
import { join } from 'path';

const DB_PATH = process.env.DB_PATH || join(process.cwd(), '.lattice/database.duckdb');
const FEATURE_FLAGS_PATH = process.env.FEATURE_FLAGS_PATH || join(process.cwd(), '.lattice/feature-flags.json');

// Initialize database connection
const db = new Database(DB_PATH);

// Load feature flags
function loadFeatureFlags() {
  try {
    return JSON.parse(readFileSync(FEATURE_FLAGS_PATH, 'utf-8'));
  } catch {
    return {};
  }
}

// Create MCP server
const server = new Server({
  name: 'lattice-compositor',
  version: '1.0.0',
}, {
  capabilities: {
    resources: {},
    tools: {},
    prompts: {},
  },
});

// List Resources
server.setRequestHandler(ListResourcesRequestSchema, async () => {
  return {
    resources: [
      {
        uri: 'lattice://database/schema',
        name: 'Database Schema',
        description: 'Complete DuckDB schema definition',
        mimeType: 'application/sql',
      },
      {
        uri: 'lattice://database/feature-flags',
        name: 'Feature Flags',
        description: 'Current feature flag configuration',
        mimeType: 'application/json',
      },
      {
        uri: 'lattice://ontology/domain-entities',
        name: 'Domain Ontology',
        description: 'Complete domain entity definitions',
        mimeType: 'application/json',
      },
      {
        uri: 'lattice://capabilities/apis',
        name: 'Software APIs',
        description: 'Available software APIs and operations',
        mimeType: 'application/json',
      },
      {
        uri: 'lattice://project/structure',
        name: 'Project Structure',
        description: 'Current project structure and relationships',
        mimeType: 'application/json',
      },
    ],
  };
});

// Read Resource
server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
  const { uri } = request.params;
  
  switch (uri) {
    case 'lattice://database/schema':
      return {
        contents: [{
          uri,
          mimeType: 'application/sql',
          text: readFileSync(join(process.cwd(), 'docs/DATABASE_SCHEMA.md'), 'utf-8'),
        }],
      };
      
    case 'lattice://database/feature-flags':
      return {
        contents: [{
          uri,
          mimeType: 'application/json',
          text: JSON.stringify(loadFeatureFlags(), null, 2),
        }],
      };
      
    case 'lattice://ontology/domain-entities':
      return {
        contents: [{
          uri,
          mimeType: 'application/json',
          text: readFileSync(join(process.cwd(), 'docs/MASTER_DEPENDENCY_ONTOLOGY.md'), 'utf-8'),
        }],
      };
      
    case 'lattice://capabilities/apis':
      return {
        contents: [{
          uri,
          mimeType: 'application/json',
          text: JSON.stringify({
            stores: [
              'layerStore', 'keyframeStore', 'animationStore', 'expressionStore',
              'audioStore', 'effectStore', 'cameraStore', 'physicsStore',
              'projectStore', 'assetStore',
            ],
            services: [
              'interpolation', 'easing', 'expressions', 'audioFeatures',
              'exportPipeline', 'effectProcessor', 'cameraExport',
            ],
            operations: [
              'createLayer', 'addKeyframe', 'evaluatePropertyAtFrame',
              'exportComposition', 'applyEffect',
            ],
          }, null, 2),
        }],
      };
      
    case 'lattice://project/structure':
      const project = db.prepare('SELECT * FROM projects ORDER BY updated_at DESC LIMIT 1').get();
      if (!project) {
        return {
          contents: [{
            uri,
            mimeType: 'application/json',
            text: JSON.stringify({ error: 'No project found' }, null, 2),
          }],
        };
      }
      
      const compositions = db.prepare('SELECT * FROM compositions WHERE project_id = ?').all(project.id);
      const layers = db.prepare(`
        SELECT l.* FROM layers l
        JOIN compositions c ON l.composition_id = c.id
        WHERE c.project_id = ?
      `).all(project.id);
      
      return {
        contents: [{
          uri,
          mimeType: 'application/json',
          text: JSON.stringify({
            project,
            compositions,
            layers,
          }, null, 2),
        }],
      };
      
    default:
      throw new Error(`Unknown resource: ${uri}`);
  }
});

// List Tools
server.setRequestHandler(ListToolsRequestSchema, async () => {
  return {
    tools: [
      {
        name: 'query_database',
        description: 'Execute a SQL query against the DuckDB database. Use this to query projects, compositions, layers, keyframes, effects, etc.',
        inputSchema: {
          type: 'object',
          properties: {
            query: {
              type: 'string',
              description: 'SQL query to execute',
            },
            limit: {
              type: 'number',
              description: 'Maximum number of rows to return (default: 100)',
              default: 100,
            },
          },
          required: ['query'],
        },
      },
      {
        name: 'get_feature_flags',
        description: 'Get current feature flag status for a project or globally',
        inputSchema: {
          type: 'object',
          properties: {
            project_id: {
              type: 'string',
              description: 'Project ID (optional, for project-specific flags)',
            },
          },
        },
      },
      {
        name: 'get_project_structure',
        description: 'Get complete project structure including compositions, layers, keyframes',
        inputSchema: {
          type: 'object',
          properties: {
            project_id: {
              type: 'string',
              description: 'Project ID (optional, uses latest if not provided)',
            },
          },
        },
      },
      {
        name: 'search_chat_history',
        description: 'Search chat message history for a project',
        inputSchema: {
          type: 'object',
          properties: {
            project_id: {
              type: 'string',
              description: 'Project ID',
            },
            query: {
              type: 'string',
              description: 'Search query (full-text search)',
            },
            limit: {
              type: 'number',
              description: 'Maximum number of results (default: 20)',
              default: 20,
            },
          },
          required: ['project_id', 'query'],
        },
      },
      {
        name: 'get_layer_details',
        description: 'Get detailed information about a layer including keyframes, expressions, effects',
        inputSchema: {
          type: 'object',
          properties: {
            layer_id: {
              type: 'string',
              description: 'Layer ID',
            },
          },
          required: ['layer_id'],
        },
      },
      {
        name: 'get_available_operations',
        description: 'Get list of available software operations (store methods, services)',
        inputSchema: {
          type: 'object',
          properties: {
            category: {
              type: 'string',
              description: 'Filter by category: stores, services, or operations',
              enum: ['stores', 'services', 'operations'],
            },
          },
        },
      },
    ],
  };
});

// Call Tool
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;
  
  try {
    switch (name) {
      case 'query_database': {
        const { query, limit = 100 } = args;
        const stmt = db.prepare(query);
        const results = stmt.all().slice(0, limit);
        return {
          content: [{
            type: 'text',
            text: JSON.stringify(results, null, 2),
          }],
        };
      }
      
      case 'get_feature_flags': {
        const { project_id } = args || {};
        let flags;
        if (project_id) {
          const project = db.prepare('SELECT feature_flags FROM projects WHERE id = ?').get(project_id);
          flags = project ? JSON.parse(project.feature_flags) : {};
        } else {
          flags = loadFeatureFlags();
        }
        return {
          content: [{
            type: 'text',
            text: JSON.stringify(flags, null, 2),
          }],
        };
      }
      
      case 'get_project_structure': {
        const { project_id } = args || {};
        let project;
        if (project_id) {
          project = db.prepare('SELECT * FROM projects WHERE id = ?').get(project_id);
        } else {
          project = db.prepare('SELECT * FROM projects ORDER BY updated_at DESC LIMIT 1').get();
        }
        
        if (!project) {
          return {
            content: [{
              type: 'text',
              text: JSON.stringify({ error: 'No project found' }, null, 2),
            }],
            isError: true,
          };
        }
        
        const compositions = db.prepare('SELECT * FROM compositions WHERE project_id = ?').all(project.id);
        const layers = db.prepare(`
          SELECT l.* FROM layers l
          JOIN compositions c ON l.composition_id = c.id
          WHERE c.project_id = ?
        `).all(project.id);
        const keyframes = db.prepare(`
          SELECT k.* FROM keyframes k
          JOIN layers l ON k.layer_id = l.id
          JOIN compositions c ON l.composition_id = c.id
          WHERE c.project_id = ?
        `).all(project.id);
        
        return {
          content: [{
            type: 'text',
            text: JSON.stringify({
              project,
              compositions,
              layers,
              keyframes,
            }, null, 2),
          }],
        };
      }
      
      case 'search_chat_history': {
        const { project_id, query, limit = 20 } = args;
        const results = db.prepare(`
          SELECT * FROM chat_messages
          WHERE project_id = ?
            AND content MATCH ?
          ORDER BY timestamp DESC
          LIMIT ?
        `).all(project_id, query, limit);
        return {
          content: [{
            type: 'text',
            text: JSON.stringify(results, null, 2),
          }],
        };
      }
      
      case 'get_layer_details': {
        const { layer_id } = args;
        const layer = db.prepare('SELECT * FROM layers WHERE id = ?').get(layer_id);
        if (!layer) {
          return {
            content: [{
              type: 'text',
              text: JSON.stringify({ error: 'Layer not found' }, null, 2),
            }],
            isError: true,
          };
        }
        
        const keyframes = db.prepare('SELECT * FROM keyframes WHERE layer_id = ?').all(layer_id);
        const expressions = db.prepare('SELECT * FROM expressions WHERE layer_id = ?').all(layer_id);
        const effects = db.prepare('SELECT * FROM effects WHERE layer_id = ?').all(layer_id);
        
        return {
          content: [{
            type: 'text',
            text: JSON.stringify({
              layer,
              keyframes,
              expressions,
              effects,
            }, null, 2),
          }],
        };
      }
      
      case 'get_available_operations': {
        const { category } = args || {};
        const operations = {
          stores: [
            'layerStore', 'keyframeStore', 'animationStore', 'expressionStore',
            'audioStore', 'effectStore', 'cameraStore', 'physicsStore',
            'projectStore', 'assetStore',
          ],
          services: [
            'interpolation', 'easing', 'expressions', 'audioFeatures',
            'exportPipeline', 'effectProcessor', 'cameraExport',
          ],
          operations: [
            'createLayer', 'addKeyframe', 'evaluatePropertyAtFrame',
            'exportComposition', 'applyEffect',
          ],
        };
        
        const result = category ? { [category]: operations[category] } : operations;
        return {
          content: [{
            type: 'text',
            text: JSON.stringify(result, null, 2),
          }],
        };
      }
      
      default:
        throw new Error(`Unknown tool: ${name}`);
    }
  } catch (error) {
    return {
      content: [{
        type: 'text',
        text: JSON.stringify({ error: error.message }, null, 2),
      }],
      isError: true,
    };
  }
});

// Start server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Lattice Compositor MCP Server running');
}

main().catch(console.error);
```

---

## Prompts (Context for LLM Agents)

**File:** `scripts/mcp-prompts.json`

```json
{
  "prompts": [
    {
      "name": "lattice-compositor-context",
      "description": "Context about Lattice Compositor software capabilities",
      "arguments": [
        {
          "name": "project_id",
          "description": "Project ID to get context for",
          "required": false
        }
      ]
    }
  ]
}
```

---

## Usage Examples

### Query Database

```javascript
// From LLM agent
{
  "tool": "query_database",
  "arguments": {
    "query": "SELECT l.name, l.layer_type, COUNT(k.id) as keyframe_count FROM layers l LEFT JOIN keyframes k ON k.layer_id = l.id GROUP BY l.id, l.name, l.layer_type",
    "limit": 50
  }
}
```

### Get Feature Flags

```javascript
{
  "tool": "get_feature_flags",
  "arguments": {
    "project_id": "project-123"
  }
}
```

### Search Chat History

```javascript
{
  "tool": "search_chat_history",
  "arguments": {
    "project_id": "project-123",
    "query": "particle system",
    "limit": 10
  }
}
```

---

## Security Considerations

1. **Read-Only by Default:** MCP server only exposes read operations
2. **Sandboxed:** Database access runs in Bubblewrap sandbox
3. **Query Limits:** All queries have default limits
4. **Input Validation:** All inputs validated before execution
5. **Error Handling:** Errors don't expose internal structure

---

## Related Documents

- `docs/DATABASE_SCHEMA.md` - Database schema
- `docs/LITERATE_PROGRAMMING_MAPPING.md` - Code-to-database mapping
- `docs/MASTER_DEPENDENCY_ONTOLOGY.md` - Domain ontology

---

*MCP Server Version: 1.0*
*Last Updated: 2026-01-23*
