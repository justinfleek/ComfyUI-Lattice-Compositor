/**
 * Configuration Validators
 * Utilities for validating configuration files
 */

import { readFileSync, existsSync } from 'fs';
import { join } from 'path';

/**
 * Validate Cursor rules file (.mdc format)
 */
export function validateCursorRule(filePath) {
  if (!existsSync(filePath)) {
    return { valid: false, error: 'File does not exist' };
  }
  
  const content = readFileSync(filePath, 'utf-8');
  const errors = [];
  
  // Check for required sections
  if (!content.includes('## Description')) {
    errors.push('Missing Description section');
  }
  
  // Check for globs section
  if (!content.includes('## Globs')) {
    errors.push('Missing Globs section');
  }
  
  // Check for rules section
  if (!content.includes('## Rules')) {
    errors.push('Missing Rules section');
  }
  
  // Basic markdown validation
  if (!content.trim().startsWith('#')) {
    errors.push('File should start with markdown header');
  }
  
  return {
    valid: errors.length === 0,
    errors,
  };
}

/**
 * Validate skill file (SKILL.md format)
 */
export function validateSkillFile(filePath) {
  if (!existsSync(filePath)) {
    return { valid: false, error: 'File does not exist' };
  }
  
  const content = readFileSync(filePath, 'utf-8');
  const errors = [];
  
  // Check for frontmatter
  if (!content.startsWith('---')) {
    errors.push('Missing frontmatter (should start with ---)');
  }
  
  // Extract frontmatter
  const frontmatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
  if (!frontmatterMatch) {
    errors.push('Invalid frontmatter format');
    return { valid: false, errors };
  }
  
  const frontmatter = frontmatterMatch[1];
  
  // Check required fields
  if (!frontmatter.includes('name:')) {
    errors.push('Missing name field in frontmatter');
  }
  if (!frontmatter.includes('description:')) {
    errors.push('Missing description field in frontmatter');
  }
  
  // Check content after frontmatter
  const contentAfter = content.substring(frontmatterMatch[0].length).trim();
  if (!contentAfter) {
    errors.push('Missing skill content after frontmatter');
  }
  
  return {
    valid: errors.length === 0,
    errors,
  };
}

/**
 * Validate agent config (AGENTS.md, CLAUDE.md)
 */
export function validateAgentConfig(filePath) {
  if (!existsSync(filePath)) {
    return { valid: false, error: 'File does not exist' };
  }
  
  const content = readFileSync(filePath, 'utf-8');
  const errors = [];
  
  // Check for mandatory workflow mention
  if (!content.includes('MANDATORY') && !content.includes('mandatory')) {
    errors.push('Missing MANDATORY workflow mention');
  }
  
  // Check for validation step mention
  if (!content.includes('validate') && !content.includes('VALIDATE')) {
    errors.push('Missing validation step mention');
  }
  
  // Check for Straylight Protocol mention
  if (!content.includes('Straylight Protocol') && !content.includes('straylight')) {
    errors.push('Missing Straylight Protocol reference');
  }
  
  return {
    valid: errors.length === 0,
    errors,
  };
}

/**
 * Validate opencode.json
 */
export function validateOpencodeConfig(filePath) {
  if (!existsSync(filePath)) {
    return { valid: false, error: 'File does not exist' };
  }
  
  try {
    const content = readFileSync(filePath, 'utf-8');
    const config = JSON.parse(content);
    const errors = [];
    
    // Check required fields
    if (!config.mcpServers) {
      errors.push('Missing mcpServers field');
    }
    
    if (!config.instructions || !Array.isArray(config.instructions)) {
      errors.push('Missing or invalid instructions field');
    }
    
    // Check for straylight MCP server
    if (config.mcpServers && !config.mcpServers.straylight) {
      errors.push('Missing straylight MCP server configuration');
    }
    
    // Check for permission settings
    if (!config.permission) {
      errors.push('Missing permission field');
    }
    
    return {
      valid: errors.length === 0,
      errors,
    };
  } catch (error) {
    return {
      valid: false,
      errors: [`JSON parse error: ${error.message}`],
    };
  }
}

/**
 * Validate MCP settings.json
 */
export function validateMcpConfig(filePath) {
  if (!existsSync(filePath)) {
    return { valid: false, error: 'File does not exist' };
  }
  
  try {
    const content = readFileSync(filePath, 'utf-8');
    const config = JSON.parse(content);
    const errors = [];
    
    // Check for mcpServers field
    if (!config.mcpServers) {
      errors.push('Missing mcpServers field');
    }
    
    // Check for straylight server
    if (config.mcpServers && !config.mcpServers.straylight) {
      errors.push('Missing straylight MCP server configuration');
    }
    
    // Check straylight server config
    if (config.mcpServers?.straylight) {
      const straylight = config.mcpServers.straylight;
      if (!straylight.command) {
        errors.push('Missing command in straylight MCP server config');
      }
      if (!straylight.args || !Array.isArray(straylight.args)) {
        errors.push('Missing or invalid args in straylight MCP server config');
      }
    }
    
    return {
      valid: errors.length === 0,
      errors,
    };
  } catch (error) {
    return {
      valid: false,
      errors: [`JSON parse error: ${error.message}`],
    };
  }
}
