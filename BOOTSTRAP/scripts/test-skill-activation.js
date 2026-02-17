#!/usr/bin/env node

/**
 * Skill Activation Test Script
 * 
 * Tests keyword matching for skill activation across platforms.
 * 
 * Usage:
 *   node scripts/test-skill-activation.js [skill-name]
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const SKILLS_DIR = path.join(__dirname, '..', 'skills');
const KEYWORD_MAPPINGS = {
  'straylight-script': ['script', 'bash', 'shell', 'command-line'],
  'deterministic-coder': ['fix', 'bug', 'refactor', 'implement'],
  'expert-researcher': ['research', 'investigate', 'verify'],
  'thorough-reading': ['read', 'analyze', 'review'],
  'verification': ['verify', 'validate', 'check'],
  'testing-methodology': ['test', 'testing'],
  'safe-refactoring': ['refactor', 'refactoring'],
  'type-cleanup': ['type', 'types'],
  'exploratory-architect': ['architecture', 'design', 'plan'],
  'council': ['council:'],
};

function extractKeywords(description) {
  // Simple keyword extraction from description
  const words = description.toLowerCase()
    .replace(/[^\w\s]/g, ' ')
    .split(/\s+/)
    .filter(w => w.length > 3);
  return [...new Set(words)];
}

function testSkill(skillName) {
  const skillPath = path.join(SKILLS_DIR, skillName);
  const skillFile = path.join(skillPath, 'SKILL.md');
  
  if (!fs.existsSync(skillFile)) {
    console.error(`❌ Skill not found: ${skillName}`);
    return false;
  }
  
  const content = fs.readFileSync(skillFile, 'utf8');
  
  // Extract frontmatter
  const frontmatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
  if (!frontmatterMatch) {
    console.error(`❌ ${skillName}: Missing frontmatter`);
    return false;
  }
  
  const frontmatter = frontmatterMatch[1];
  const descriptionMatch = frontmatter.match(/^description:\s*(.+)$/m);
  
  if (!descriptionMatch) {
    console.error(`❌ ${skillName}: Missing description`);
    return false;
  }
  
  const description = descriptionMatch[1];
  const extractedKeywords = extractKeywords(description);
  const expectedKeywords = KEYWORD_MAPPINGS[skillName] || [];
  
  console.log(`\n${skillName}:`);
  console.log(`  Description: ${description.substring(0, 80)}...`);
  console.log(`  Expected keywords: ${expectedKeywords.join(', ')}`);
  console.log(`  Extracted keywords: ${extractedKeywords.slice(0, 10).join(', ')}`);
  
  // Check if expected keywords are present
  const missingKeywords = expectedKeywords.filter(kw => 
    !description.toLowerCase().includes(kw.toLowerCase())
  );
  
  if (missingKeywords.length > 0) {
    console.log(`  ⚠️  Missing keywords: ${missingKeywords.join(', ')}`);
    return false;
  }
  
  console.log(`  ✅ All expected keywords present`);
  return true;
}

function main() {
  const skillArg = process.argv[2];
  
  if (skillArg) {
    // Test single skill
    testSkill(skillArg);
  } else {
    // Test all skills
    console.log('Testing skill activation keywords...\n');
    
    const skills = fs.readdirSync(SKILLS_DIR).filter(item => {
      const itemPath = path.join(SKILLS_DIR, item);
      return fs.statSync(itemPath).isDirectory();
    });
    
    let passed = 0;
    let failed = 0;
    
    for (const skill of skills) {
      if (testSkill(skill)) {
        passed++;
      } else {
        failed++;
      }
    }
    
    console.log(`\n\nResults: ${passed} passed, ${failed} failed`);
    
    if (failed > 0) {
      process.exit(1);
    }
  }
}

main();
