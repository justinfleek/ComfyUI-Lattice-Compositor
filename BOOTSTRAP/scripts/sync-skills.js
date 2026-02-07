#!/usr/bin/env node

/**
 * Skill Synchronization Script
 * 
 * Syncs skills from source location (skills/) to all deployment locations:
 * - .cursor/skills/ (Cursor IDE)
 * - .opencode/skills/ (OpenCode primary)
 * - .claude/skills/ (OpenCode fallback + Claude Code)
 * 
 * Usage:
 *   node scripts/sync-skills.js [--validate-only]
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const SOURCE_DIR = path.join(__dirname, '..', 'skills');
const TARGET_DIRS = [
  path.join(__dirname, '..', '.cursor', 'skills'),
  path.join(__dirname, '..', '.opencode', 'skills'),
  path.join(__dirname, '..', '.claude', 'skills'),
];

const VALIDATE_ONLY = process.argv.includes('--validate-only');

// Required frontmatter fields
const REQUIRED_FIELDS = ['name', 'description'];
const OPTIONAL_FIELDS = ['license', 'compatibility', 'metadata'];

function validateSkill(skillPath) {
  const skillFile = path.join(skillPath, 'SKILL.md');
  
  if (!fs.existsSync(skillFile)) {
    return { valid: false, error: `Missing SKILL.md in ${skillPath}` };
  }
  
  let content = fs.readFileSync(skillFile, 'utf8');
  
  // Normalize line endings (handle both \n and \r\n)
  content = content.replace(/\r\n/g, '\n');
  
  // Check for YAML frontmatter
  if (!content.startsWith('---\n')) {
    return { valid: false, error: `Missing YAML frontmatter in ${skillFile}` };
  }
  
  // Extract frontmatter
  const frontmatterEnd = content.indexOf('\n---\n', 4);
  if (frontmatterEnd === -1) {
    return { valid: false, error: `Invalid YAML frontmatter in ${skillFile}` };
  }
  
  const frontmatter = content.substring(4, frontmatterEnd);
  const lines = frontmatter.split('\n').filter(l => l.trim());
  
  const fields = {};
  for (const line of lines) {
    const match = line.match(/^(\w+):\s*(.+)$/);
    if (match) {
      fields[match[1]] = match[2].trim();
    }
  }
  
  // Validate required fields
  for (const field of REQUIRED_FIELDS) {
    if (!fields[field]) {
      return { valid: false, error: `Missing required field '${field}' in ${skillFile}` };
    }
  }
  
  // Validate name format (lowercase, hyphens, alphanumeric)
  if (fields.name && !/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(fields.name)) {
    return { valid: false, error: `Invalid name format '${fields.name}' in ${skillFile}. Must be lowercase alphanumeric with hyphens.` };
  }
  
  // Validate description length
  if (fields.description && fields.description.length > 1024) {
    return { valid: false, error: `Description too long (${fields.description.length} > 1024) in ${skillFile}` };
  }
  
  return { valid: true, fields };
}

function syncSkill(skillName, sourcePath, targetDir) {
  const sourceSkillPath = path.join(sourcePath, skillName);
  const targetSkillPath = path.join(targetDir, skillName);
  
  // Validate source skill
  const validation = validateSkill(sourceSkillPath);
  if (!validation.valid) {
    console.error(`❌ ${skillName}: ${validation.error}`);
    return false;
  }
  
  // Create target directory
  if (!fs.existsSync(targetDir)) {
    fs.mkdirSync(targetDir, { recursive: true });
  }
  
  // Copy skill directory
  if (fs.existsSync(targetSkillPath)) {
    fs.rmSync(targetSkillPath, { recursive: true, force: true });
  }
  
  fs.cpSync(sourceSkillPath, targetSkillPath, { recursive: true });
  
  console.log(`✅ ${skillName} → ${path.relative(process.cwd(), targetSkillPath)}`);
  return true;
}

function main() {
  console.log('Skill Synchronization\n');
  
  if (!fs.existsSync(SOURCE_DIR)) {
    console.error(`❌ Source directory not found: ${SOURCE_DIR}`);
    process.exit(1);
  }
  
  // Get all skills from source
  const skills = fs.readdirSync(SOURCE_DIR).filter(item => {
    const itemPath = path.join(SOURCE_DIR, item);
    return fs.statSync(itemPath).isDirectory();
  });
  
  if (skills.length === 0) {
    console.error(`❌ No skills found in ${SOURCE_DIR}`);
    process.exit(1);
  }
  
  console.log(`Found ${skills.length} skills in source directory\n`);
  
  let allValid = true;
  
  // Validate all skills first
  for (const skill of skills) {
    const validation = validateSkill(path.join(SOURCE_DIR, skill));
    if (!validation.valid) {
      console.error(`❌ ${skill}: ${validation.error}`);
      allValid = false;
    }
  }
  
  if (!allValid) {
    console.error('\n❌ Validation failed. Fix errors before syncing.');
    process.exit(1);
  }
  
  if (VALIDATE_ONLY) {
    console.log('\n✅ All skills validated successfully');
    return;
  }
  
  // Sync to all target directories
  console.log('\nSyncing skills...\n');
  
  for (const targetDir of TARGET_DIRS) {
    console.log(`→ ${path.basename(path.dirname(targetDir))}/${path.basename(targetDir)}/`);
    
    for (const skill of skills) {
      if (!syncSkill(skill, SOURCE_DIR, targetDir)) {
        allValid = false;
      }
    }
    
    console.log('');
  }
  
  if (allValid) {
    console.log('✅ All skills synced successfully');
  } else {
    console.error('❌ Some skills failed to sync');
    process.exit(1);
  }
}

// Run if executed directly
const isMainModule = import.meta.url === `file://${path.resolve(process.argv[1])}` || 
                     import.meta.url.endsWith('sync-skills.js');

if (isMainModule) {
  main();
}

export { validateSkill, syncSkill };
