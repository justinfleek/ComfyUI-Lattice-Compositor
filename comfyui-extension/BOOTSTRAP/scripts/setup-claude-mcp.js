#!/usr/bin/env node
/**
 * Cross-platform script to set up Claude Code MCP server configuration
 */

import { writeFileSync, mkdirSync, existsSync, readFileSync } from 'fs';
import { join, dirname, resolve } from 'path';
import { fileURLToPath } from 'url';
import { homedir } from 'os';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const projectRoot = resolve(__dirname, '..');
const mcpServerPath = resolve(projectRoot, '.claude', 'straylight-mcp.js');

// Verify MCP server exists
if (!existsSync(mcpServerPath)) {
  console.error(`Error: MCP server not found at: ${mcpServerPath}`);
  process.exit(1);
}

// Determine Claude config directory based on OS
const platform = process.platform;
let claudeConfigDir;
let claudeConfigFile;

if (platform === 'win32') {
  claudeConfigDir = join(homedir(), '.claude');
  claudeConfigFile = join(claudeConfigDir, 'claude_desktop_config.json');
} else if (platform === 'darwin') {
  claudeConfigDir = join(homedir(), 'Library', 'Application Support', 'Claude');
  claudeConfigFile = join(claudeConfigDir, 'claude_desktop_config.json');
} else {
  // Linux
  claudeConfigDir = join(homedir(), '.claude');
  claudeConfigFile = join(claudeConfigDir, 'claude_desktop_config.json');
}

// Create config directory if it doesn't exist
if (!existsSync(claudeConfigDir)) {
  mkdirSync(claudeConfigDir, { recursive: true });
  console.log(`Created Claude config directory: ${claudeConfigDir}`);
}

// Read existing config or create new one
let config = { mcpServers: {} };
if (existsSync(claudeConfigFile)) {
  try {
    const existingConfig = readFileSync(claudeConfigFile, 'utf-8');
    config = JSON.parse(existingConfig);
    if (!config.mcpServers) {
      config.mcpServers = {};
    }
  } catch (error) {
    console.warn('Could not parse existing config, creating new one');
    config = { mcpServers: {} };
  }
}

// Add or update straylight server config
config.mcpServers.straylight = {
  command: 'node',
  args: [mcpServerPath],
};

// Write config file
writeFileSync(claudeConfigFile, JSON.stringify(config, null, 2), 'utf-8');

console.log('✅ Claude Code MCP configuration updated!');
console.log(`   Config file: ${claudeConfigFile}`);
console.log(`   MCP server: ${mcpServerPath}`);
console.log('');
console.log('⚠️  Please restart Claude Code for changes to take effect.');
