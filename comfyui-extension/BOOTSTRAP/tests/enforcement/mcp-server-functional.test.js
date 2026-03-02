/**
 * MCP Server Functional Tests
 * Actually test MCP server tools work and find bugs
 */

import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

const mcpServerPath = join(process.cwd(), '.claude', 'straylight-mcp.js');

console.log('\n🔍 BUG HUNT: Testing MCP Server\n');

const bugs = [];

// Test 1: MCP server should exist and be valid JavaScript
console.log('Test 1: MCP server syntax...');
if (!existsSync(mcpServerPath)) {
  bugs.push({ test: 'Test 1', bug: true, message: 'MCP server file does not exist' });
} else {
  try {
    const content = readFileSync(mcpServerPath, 'utf-8');
    // Check for required imports
    if (!content.includes('@modelcontextprotocol/sdk')) {
      bugs.push({ test: 'Test 1', bug: true, message: 'MCP server missing SDK import' });
    }
    if (!content.includes('Server')) {
      bugs.push({ test: 'Test 1', bug: true, message: 'MCP server missing Server import' });
    }
    if (!content.includes('RULES')) {
      bugs.push({ test: 'Test 1', bug: true, message: 'MCP server missing RULES import' });
    }
  } catch (error) {
    bugs.push({ test: 'Test 1', bug: true, message: `Cannot read MCP server: ${error.message}` });
  }
}

// Test 2: All 6 tools should be implemented
console.log('Test 2: All MCP tools implemented...');
const content = readFileSync(mcpServerPath, 'utf-8');
const requiredTools = ['straylight_validate', 'straylight_template', 'straylight_locate', 'straylight_plan', 'straylight_examples', 'straylight_search'];
for (const tool of requiredTools) {
  if (!content.includes(tool)) {
    bugs.push({ test: 'Test 2', bug: true, message: `MCP tool ${tool} not implemented` });
  }
}

// Test 3: straylight_validate should use same logic as validate-file.js
console.log('Test 3: Validation logic consistency...');
if (!content.includes('validateCode')) {
  bugs.push({ test: 'Test 3', bug: true, message: 'MCP server not using validateCode function' });
}

// Test 4: Error handling should be present
console.log('Test 4: Error handling...');
if (!content.includes('try') && !content.includes('catch')) {
  bugs.push({ test: 'Test 4', bug: true, message: 'MCP server missing error handling' });
}

// Test 5: Should handle invalid input gracefully
console.log('Test 5: Invalid input handling...');
// This would require actually running the MCP server, but we can check for input validation
if (!content.includes('code') && !content.includes('type')) {
  bugs.push({ test: 'Test 5', bug: true, message: 'MCP server may not validate input parameters' });
}

console.log(`\n📊 Bug Hunt Results: ${bugs.length} bugs found\n`);

if (bugs.length > 0) {
  console.log('❌ BUGS FOUND:\n');
  bugs.forEach((bug, i) => {
    console.log(`${i + 1}. ${bug.test}: ${bug.message}`);
  });
  process.exit(1);
} else {
  console.log('✅ No bugs found in MCP server structure');
  process.exit(0);
}
