#!/usr/bin/env node

/**
 * Claude Code Skill Activator Hook
 * 
 * Analyzes user messages for skill keywords and explicitly activates matching skills.
 * This provides deterministic skill activation for Claude Code.
 * 
 * Location: .claude/hooks/user-prompt-submit/10-skill-activator.js
 * 
 * This hook runs before each user message is processed.
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__dirname);

// Skill keyword mappings
const SKILL_KEYWORDS = {
  'straylight-script': ['script', 'bash', 'shell', 'command-line', 'cli', 'executable'],
  'deterministic-coder': ['fix', 'bug', 'refactor', 'implement', 'spec', 'routine'],
  'expert-researcher': ['research', 'investigate', 'verify', 'fact-check', 'evidence'],
  'thorough-reading': ['read', 'analyze', 'review', 'trace', 'dependencies'],
  'verification': ['verify', 'validate', 'check', 'test'],
  'testing-methodology': ['test', 'testing', 'test suite', 'test case'],
  'safe-refactoring': ['refactor', 'refactoring', 'restructure'],
  'type-cleanup': ['type', 'types', 'typing', 'type system'],
  'exploratory-architect': ['architecture', 'design', 'plan', 'structure'],
  'council': ['council:'], // Special case - prefix trigger
};

function findMatchingSkills(userMessage) {
  const message = userMessage.toLowerCase();
  const matches = [];
  
  // Check for council prefix first (special case)
  if (message.startsWith('council:')) {
    matches.push('council');
  }
  
  // Check other skills
  for (const [skill, keywords] of Object.entries(SKILL_KEYWORDS)) {
    if (skill === 'council') continue; // Already handled
    
    for (const keyword of keywords) {
      if (message.includes(keyword)) {
        matches.push(skill);
        break; // Only add once per skill
      }
    }
  }
  
  return matches;
}

function main() {
  // Read user message from stdin or environment
  const userMessage = process.env.USER_MESSAGE || 
                     (process.stdin.isTTY ? '' : fs.readFileSync(0, 'utf8').trim());
  
  if (!userMessage) {
    // No message, exit silently
    process.exit(0);
  }
  
  const matchingSkills = findMatchingSkills(userMessage);
  
  if (matchingSkills.length > 0) {
    // Output skill activation hints
    // Claude Code will use these to activate skills
    console.log(`# Skill Activation Hints`);
    console.log(`# Matching skills: ${matchingSkills.join(', ')}`);
    console.log(`# Consider activating: ${matchingSkills.map(s => `skills/${s}`).join(', ')}`);
  }
  
  // Exit successfully (hook doesn't block, just provides hints)
  process.exit(0);
}

main();
