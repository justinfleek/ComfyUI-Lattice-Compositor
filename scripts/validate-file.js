#!/usr/bin/env node
/**
 * File validation script - can be used as middleware or standalone
 * Validates files against Straylight Protocol rules
 */

import { readFileSync } from 'fs';
import { extname, basename, resolve } from 'path';
import { existsSync } from 'fs';
import { RULES, MAX_FILE_LINES } from './rules.js';

/**
 * Extract embedded code blocks from config files
 * Returns array of { type, code, line } objects
 */
function extractEmbeddedCode(content, filePath) {
  const ext = extname(filePath).toLowerCase();
  const embedded = [];
  const lines = content.split('\n');
  
  if (ext === '.yml' || ext === '.yaml') {
    // Check for Nix code in YAML (common in Nix flakes)
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      // Look for patterns like: nix: | or script: |
      if (/^\s*(nix|bash|script|build|install):\s*\|/.test(line)) {
        // Multi-line string block follows
        let code = '';
        let j = i + 1;
        while (j < lines.length && /^\s{2,}/.test(lines[j])) {
          code += lines[j].replace(/^\s{2,}/, '') + '\n';
          j++;
        }
        if (code.trim()) {
          embedded.push({ type: 'nix', code: code.trim(), line: i + 1 });
        }
      }
      // Check for inline Nix expressions
      if (/nix:\s*\{/.test(line) || /bash:\s*"/.test(line)) {
        embedded.push({ type: 'bash', code: line, line: i + 1 });
      }
    }
  } else if (ext === '.toml') {
    // Check for embedded scripts in TOML
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (/^\s*\[.*script.*\]/.test(line) || /^\s*script\s*=/.test(line)) {
        // Script block follows
        let code = '';
        let j = i + 1;
        while (j < lines.length && (/^\s{2,}/.test(lines[j]) || lines[j].trim().startsWith('"'))) {
          code += lines[j] + '\n';
          j++;
        }
        if (code.trim()) {
          embedded.push({ type: 'bash', code: code.trim(), line: i + 1 });
        }
      }
    }
  } else if (ext === '.json') {
    // Check for embedded code in JSON strings
    const jsonMatch = content.match(/"\s*(nix|bash|script)\s*":\s*"([^"]+)"/g);
    if (jsonMatch) {
      for (const match of jsonMatch) {
        const codeMatch = match.match(/"([^"]+)"/);
        if (codeMatch && codeMatch[1]) {
          const lineNum = content.substring(0, content.indexOf(match)).split('\n').length;
          embedded.push({ type: 'bash', code: codeMatch[1], line: lineNum });
        }
      }
    }
  }
  
  return embedded;
}

function validateFileSize(code, filePath) {
  // Skip file size check for legacy/imported codebases
  // These directories contain existing code that will be refactored over time
  const normalizedPath = (filePath || '').replace(/\\/g, '/');
  const legacyPaths = ['/leancomfy/', '/leandocs/', '/newfeatures/'];
  const isLegacy = legacyPaths.some(p => normalizedPath.includes(p));
  if (isLegacy) {
    return { valid: true, errors: [] }; // Skip size check for legacy code
  }

  // Count lines - split by newline, but don't count trailing empty line if file ends with newline
  const lines = code.split('\n');
  // If last line is empty and code ends with newline, don't count it
  const lineCount = code.endsWith('\n') && lines[lines.length - 1] === ''
    ? lines.length - 1
    : lines.length;

  if (lineCount > MAX_FILE_LINES) {
    return {
      valid: false,
      errors: [{
        line: 0,
        rule: "STRAYLIGHT-010",
        message: `File exceeds ${MAX_FILE_LINES} line limit (${lineCount} lines). Split into smaller modules.`,
      }],
    };
  }
  return { valid: true, errors: [] };
}

function validateCode(code, type, filePath = '') {
  // Note: File size check runs first, but code block size check (STRAYLIGHT-010-BLOCK)
  // should still run even if file is >500 lines to catch individual block violations
  const sizeCheck = validateFileSize(code, filePath);
  // Don't return early - continue to check other rules including code block sizes
  
  const errors = [];
  const lines = code.split('\n');

  if (!RULES[type]) {
    return {
      valid: false,
      errors: [{ line: 0, rule: 'UNKNOWN', message: `Unknown type: ${type}` }],
    };
  }

  // Add file size error if file exceeds limit (but continue checking other rules)
  if (!sizeCheck.valid) {
    errors.push(...sizeCheck.errors);
  }

  // Check forbidden patterns
  for (const rule of RULES[type].forbidden || []) {
    if (rule.check) {
      // Rule has custom check function - always run it
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        // Check function returned false = violation found
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
        });
      }
      // Skip pattern check if check function exists
      continue;
    } else if (rule.pattern) {
      // Rule uses pattern matching
      const matches = [...code.matchAll(new RegExp(rule.pattern, 'gm'))];
      for (const match of matches) {
        // Check for exceptions
        if (rule.exception) {
          // Exception can be a regex or function
          if (typeof rule.exception === 'function') {
            if (rule.exception(code, match)) continue;
          } else if (rule.exception.test(code)) {
            continue;
          }
        }

        const beforeMatch = code.substring(0, match.index);
        const lineNum = beforeMatch.split('\n').length;

        errors.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
        });
      }
    }
  }

  // Check warnings
  const warnings = [];
  for (const rule of RULES[type].warnings || []) {
    if (rule.check) {
      // Rule has custom check function - always run it
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        // Check function returned false = violation found
        warnings.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
          severity: "warning",
        });
      }
      // Skip pattern check if check function exists
      continue;
    } else if (rule.pattern) {
      const matches = [...code.matchAll(new RegExp(rule.pattern, 'gm'))];
      for (const match of matches) {
        if (rule.exception && rule.exception.test(code)) {
          continue;
        }
        
        if (rule.context === "module" && !filePath.includes('/modules/')) {
          continue;
        }
        if (rule.context === "nixos" && !filePath.includes('/nixos/')) {
          continue;
        }

        const beforeMatch = code.substring(0, match.index);
        const lineNum = beforeMatch.split('\n').length;

        warnings.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
          severity: "warning",
        });
      }
    }
  }

  // Check required patterns
  for (const rule of RULES[type].required || []) {
    if (rule.check) {
      // Check function may take (code) or (code, filePath)
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
        });
      }
    } else if (rule.pattern && !rule.pattern.test(code)) {
      errors.push({
        line: 0,
        rule: rule.rule,
        message: rule.message,
      });
    }
  }

  return {
    valid: errors.length === 0,
    errors,
    warnings,
  };
}

function determineFileType(filePath) {
  const ext = extname(filePath);
  const name = basename(filePath);
  const fullPath = filePath.toLowerCase();
  
  // Literate programming files (check first - they have compound extensions)
  if (fullPath.endsWith('.lit.hs')) return 'literate';
  if (fullPath.endsWith('.lit.cpp')) return 'literate';
  if (fullPath.endsWith('.lit.purs')) return 'literate';
  if (ext === '.lit' || ext === '.mdx') return 'literate';
  
  // Nix files
  if (ext === '.nix') return 'nix';
  
  // Haskell files
  if (ext === '.hs') return 'haskell';
  
  // PureScript files
  if (ext === '.purs') return 'purescript';
  
  // Lean4 files
  if (ext === '.lean') return 'lean4';
  
  // C++ files (check before forbidden languages to avoid false positives)
  if (ext === '.cpp' || ext === '.hpp' || ext === '.cc' || ext === '.cxx' || ext === '.h' || ext === '.hxx') return 'cpp23';
  
  // CUDA files (C++ extension)
  if (ext === '.cu' || ext === '.cuh') return 'cpp23';
  
  // Dhall files
  if (ext === '.dhall') return 'dhall';
  
  // Bazel/Buck2 files
  if (ext === '.bzl') return 'bazel';
  
  // Rust files
  if (ext === '.rs') return 'rust';
  
  // Python files
  if (ext === '.py') return 'python';
  
  // Config files with embedded code (validate embedded code, not config structure)
  if (ext === '.yml' || ext === '.yaml' || ext === '.toml' || ext === '.json' || ext === '.ini') {
    return 'config'; // Special type for config files
  }
  
  // Bash files
  if (ext === '.sh' || ext === '.bash' || name.endsWith('.sh') || name.endsWith('.bash')) {
    return 'bash';
  }
  
  // Also check for shebang in case extension is missing
  if (existsSync(filePath)) {
    try {
      const content = readFileSync(filePath, 'utf-8');
      if (content.startsWith('#!/bin/bash') || content.startsWith('#!/usr/bin/env bash')) {
        return 'bash';
      }
      if (content.startsWith('#!/usr/bin/env python') || content.startsWith('#!/usr/bin/python')) {
        return 'python';
      }
    } catch {
      // File might not be readable
    }
  }
  
  return null;
}

// Main execution
const filePath = process.argv[2];

if (!filePath) {
  console.error('Usage: node validate-file.js <file-path>');
  process.exit(1);
}

// Skip BOOTSTRAP scripts (legacy setup; STRAYLIGHT-006 would require Haskell port)
const pathNorm = filePath.replace(/\\/g, '/');
if (pathNorm.startsWith('BOOTSTRAP/')) {
  console.log(`Skipping validation for BOOTSTRAP script: ${filePath}`);
  process.exit(0);
}

try {
  const code = readFileSync(filePath, 'utf-8');
  const type = determineFileType(filePath);
  
  if (!type) {
    const ext = extname(filePath).toLowerCase();
    // WASM files are binary - skip validation but note they should be generated from validated source
    if (ext === '.wasm') {
      console.log(`⚠️  ${filePath}: WASM binary file detected. Binary files are not validated directly.`);
      console.log(`   Ensure source files (Rust/C++/etc.) that generate this WASM are validated.`);
      process.exit(0); // Don't fail, but inform
    }
    // Forbidden languages: languages explicitly not allowed in Straylight Protocol
    // Note: .cpp, .c, .h are NOT forbidden - they're supported as cpp23 type
    const forbiddenLanguages = ['.js', '.ts', '.jsx', '.tsx', '.java', '.rb', '.go', '.php'];
    if (forbiddenLanguages.includes(ext)) {
      console.error(`❌ ${filePath}: Forbidden language detected (${ext}). Only Haskell (.hs), PureScript (.purs), Lean4 (.lean), Nix (.nix), Bash (.sh/.bash), C++23 (.cpp/.hpp/.cc/.h/.cu/.cuh), Dhall (.dhall), Bazel (.bzl), Rust (.rs), and Python (.py) are allowed.`);
      process.exit(1);
    }
    console.error(`❌ Unknown file type for: ${filePath}. Only supported file types are: .nix, .hs, .purs, .lean, .sh, .bash, .lit, .mdx, .lit.hs, .lit.cpp, .lit.purs, .cpp, .hpp, .cc, .h, .cu, .cuh, .dhall, .bzl, .rs, .py`);
    process.exit(1);
  }
  
  // Special handling for config files - validate embedded code
  if (type === 'config') {
    const embedded = extractEmbeddedCode(code, filePath);
    if (embedded.length === 0) {
      // No embedded code - config file is just data, skip validation
      console.log(`✅ ${filePath}: Config file with no embedded code - validation skipped`);
      process.exit(0);
    }
    
    // Validate each embedded code block
    const absolutePath = resolve(filePath);
    let allValid = true;
    const allErrors = [];
    
    for (const block of embedded) {
      console.log(`Validating embedded ${block.type} code at line ${block.line}...`);
      const result = validateCode(block.code, block.type, absolutePath);
      if (!result.valid) {
        allValid = false;
        // Adjust line numbers to account for config file context
        for (const error of result.errors) {
          allErrors.push({
            ...error,
            line: block.line + error.line - 1,
            message: `[Embedded ${block.type} code] ${error.message}`,
          });
        }
      }
      if (result.warnings && result.warnings.length > 0) {
        for (const warning of result.warnings) {
          allErrors.push({
            ...warning,
            line: block.line + warning.line - 1,
            message: `[Embedded ${block.type} code] ${warning.message}`,
            severity: 'warning',
          });
        }
      }
    }
    
    if (allValid) {
      console.log(`✅ ${filePath}: All embedded code blocks are valid`);
      process.exit(0);
    } else {
      console.error(`❌ ${filePath} has ${allErrors.length} violation(s) in embedded code:`);
      for (const error of allErrors) {
        const prefix = error.severity === 'warning' ? '⚠️' : '❌';
        console.error(`  Line ${error.line}: [${error.rule}] ${prefix} ${error.message}`);
      }
      process.exit(1);
    }
  }
  
  // Pass absolute path to validateCode for proper path checking
  const absolutePath = resolve(filePath);
  const result = validateCode(code, type, absolutePath);
  
  if (result.valid) {
    if (result.warnings && result.warnings.length > 0) {
      console.log(`✅ ${filePath} is valid with ${result.warnings.length} warning(s):`);
      result.warnings.forEach(w => {
        console.log(`  Line ${w.line}: [${w.rule}] ⚠️ ${w.message}`);
      });
      // Warnings don't cause failure, but test script expects them to
      process.exit(0);
    } else {
      console.log(`✅ ${filePath} is valid`);
    }
    process.exit(0);
  } else {
    console.error(`❌ ${filePath} has ${result.errors.length} violation(s):`);
    for (const error of result.errors) {
      console.error(`  Line ${error.line}: [${error.rule}] ${error.message}`);
    }
    if (result.warnings && result.warnings.length > 0) {
      console.log('\n⚠️  Warnings:');
      result.warnings.forEach(w => {
        console.log(`  Line ${w.line}: [${w.rule}] ${w.message}`);
      });
    }
    process.exit(1);
  }
} catch (error) {
  console.error(`Error reading file: ${error.message}`);
  process.exit(1);
}
