#!/bin/bash
# Bash script to set up Claude Code MCP server configuration
# Run this script to configure Claude Code to use the Straylight Protocol MCP server

set -euo pipefail

# Get the project root directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
MCP_SERVER_PATH="$PROJECT_ROOT/.claude/straylight-mcp.js"

# Verify MCP server exists
if [ ! -f "$MCP_SERVER_PATH" ]; then
    echo "Error: MCP server not found at: $MCP_SERVER_PATH" >&2
    exit 1
fi

# Convert to absolute path
MCP_SERVER_PATH="$(cd "$(dirname "$MCP_SERVER_PATH")" && pwd)/$(basename "$MCP_SERVER_PATH")"

# Determine Claude config directory based on OS
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS
    CLAUDE_CONFIG_DIR="$HOME/Library/Application Support/Claude"
elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    # Linux
    CLAUDE_CONFIG_DIR="$HOME/.claude"
else
    echo "Error: Unsupported OS: $OSTYPE" >&2
    exit 1
fi

CLAUDE_CONFIG_FILE="$CLAUDE_CONFIG_DIR/claude_desktop_config.json"

# Create config directory if it doesn't exist
mkdir -p "$CLAUDE_CONFIG_DIR"
echo "Created Claude config directory: $CLAUDE_CONFIG_DIR"

# Read existing config or create new one
if [ -f "$CLAUDE_CONFIG_FILE" ]; then
    CONFIG=$(cat "$CLAUDE_CONFIG_FILE")
else
    CONFIG='{"mcpServers":{}}'
fi

# Update config with straylight server
CONFIG=$(echo "$CONFIG" | jq --arg path "$MCP_SERVER_PATH" '
    .mcpServers.straylight = {
        "command": "node",
        "args": [$path]
    }
')

# Write config file
echo "$CONFIG" > "$CLAUDE_CONFIG_FILE"

echo "✅ Claude Code MCP configuration updated!"
echo "   Config file: $CLAUDE_CONFIG_FILE"
echo "   MCP server: $MCP_SERVER_PATH"
echo ""
echo "⚠️  Please restart Claude Code for changes to take effect."
