/**
 * Configuration Bug Hunt Tests
 * Find bugs in configuration files and their usage
 */

import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

console.log('\n🔍 BUG HUNT: Testing Configuration Files\n');

const bugs = [];

// Test 1: opencode.json should be valid JSON
console.log('Test 1: opencode.json validity...');
const opencodePath = join(process.cwd(), 'opencode.json');
if (!existsSync(opencodePath)) {
  bugs.push({ test: 'Test 1', bug: true, message: 'opencode.json does not exist' });
} else {
  try {
    const content = JSON.parse(readFileSync(opencodePath, 'utf-8'));
    if (!content.mcpServers || !content.mcpServers.straylight) {
      bugs.push({ test: 'Test 1', bug: true, message: 'opencode.json missing straylight MCP server config' });
    }
    if (!content.instructions || !Array.isArray(content.instructions)) {
      bugs.push({ test: 'Test 1', bug: true, message: 'opencode.json missing or invalid instructions' });
    }
  } catch (error) {
    bugs.push({ test: 'Test 1', bug: true, message: `opencode.json is invalid JSON: ${error.message}` });
  }
}

// Test 2: .claude/settings.json should be valid JSON
console.log('Test 2: .claude/settings.json validity...');
const settingsPath = join(process.cwd(), '.claude', 'settings.json');
if (!existsSync(settingsPath)) {
  bugs.push({ test: 'Test 2', bug: true, message: '.claude/settings.json does not exist' });
} else {
  try {
    const content = JSON.parse(readFileSync(settingsPath, 'utf-8'));
    if (!content.mcpServers || !content.mcpServers.straylight) {
      bugs.push({ test: 'Test 2', bug: true, message: '.claude/settings.json missing straylight MCP server config' });
    }
  } catch (error) {
    bugs.push({ test: 'Test 2', bug: true, message: `.claude/settings.json is invalid JSON: ${error.message}` });
  }
}

// Test 3: AGENTS.md should reference mandatory workflow
console.log('Test 3: AGENTS.md completeness...');
const agentsPath = join(process.cwd(), 'AGENTS.md');
if (!existsSync(agentsPath)) {
  bugs.push({ test: 'Test 3', bug: true, message: 'AGENTS.md does not exist' });
} else {
  const content = readFileSync(agentsPath, 'utf-8');
  const required = ['straylight_plan', 'straylight_locate', 'straylight_template', 'straylight_validate', 'MANDATORY'];
  for (const req of required) {
    if (!content.includes(req)) {
      bugs.push({ test: 'Test 3', bug: true, message: `AGENTS.md missing required content: ${req}` });
    }
  }
}

// Test 4: Cursor rules should be valid markdown
console.log('Test 4: Cursor rules validity...');
const rulesDir = join(process.cwd(), '.cursor', 'rules');
if (!existsSync(rulesDir)) {
  bugs.push({ test: 'Test 4', bug: true, message: '.cursor/rules directory does not exist' });
} else {
  const ruleFiles = ['001_straylight-protocol.mdc', '002_validation-required.mdc', '003_mandatory-workflow.mdc'];
  for (const file of ruleFiles) {
    const filePath = join(rulesDir, file);
    if (!existsSync(filePath)) {
      bugs.push({ test: 'Test 4', bug: true, message: `Missing rule file: ${file}` });
    } else {
      const content = readFileSync(filePath, 'utf-8');
      if (!content.includes('##')) {
        bugs.push({ test: 'Test 4', bug: true, message: `${file} appears to be invalid markdown` });
      }
    }
  }
}

// Test 5: Skills should be consistent across locations
console.log('Test 5: Skills consistency...');
const skillLocations = [
  join(process.cwd(), 'skills'),
  join(process.cwd(), '.cursor', 'skills'),
  join(process.cwd(), '.opencode', 'skills'),
  join(process.cwd(), '.claude', 'skills'),
];

const expectedSkills = ['council', 'deterministic-coder', 'testing-methodology'];
for (const skill of expectedSkills) {
  const foundIn = [];
  for (const location of skillLocations) {
    const skillPath = join(location, skill, 'SKILL.md');
    if (existsSync(skillPath)) {
      foundIn.push(location);
    }
  }
  if (foundIn.length === 0) {
    bugs.push({ test: 'Test 5', bug: true, message: `Skill ${skill} not found in any location` });
  }
}

console.log(`\n📊 Bug Hunt Results: ${bugs.length} bugs found\n`);

if (bugs.length > 0) {
  console.log('❌ BUGS FOUND:\n');
  bugs.forEach((bug, i) => {
    console.log(`${i + 1}. ${bug.test}: ${bug.message}`);
  });
  process.exit(1);
} else {
  console.log('✅ No bugs found in configuration files');
  process.exit(0);
}
