# Straylight Protocol MCP Server

This directory contains the Model Context Protocol (MCP) server for Straylight Protocol enforcement.

## Files

- `straylight-mcp.js` - Main MCP server implementation
- `settings.json` - Claude Code MCP configuration

## Installation

1. Install dependencies:
   ```bash
   npm install
   ```

2. The MCP server will be automatically used by Claude Code when configured in `.claude/settings.json`

## Usage

The MCP server provides 6 tools:

1. **straylight_validate** - Validate code against protocol rules
2. **straylight_template** - Generate starter code templates
3. **straylight_locate** - Determine correct file location
4. **straylight_plan** - Get documentation and examples for a task
5. **straylight_examples** - Find reference implementations
6. **straylight_search** - Search codebase

## Testing

To test the MCP server manually:

```bash
# The server communicates via stdio, so it's designed to be used by MCP clients
# For manual testing, you can check the syntax:
node -c .claude/straylight-mcp.js
```

## Troubleshooting

- **Module not found errors**: Run `npm install` to install `@modelcontextprotocol/sdk`
- **Server won't start**: Check Node.js version (requires 18+)
- **Tools not available**: Verify `.claude/settings.json` is configured correctly
