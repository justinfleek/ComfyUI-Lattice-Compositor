#!/usr/bin/env node
/**
 * Comprehensive file scanner for Straylight Protocol validation
 * Systematically validates ALL files in a directory tree against all 48 rules
 */

import { readFileSync, readdirSync, statSync, existsSync } from 'fs';
import { join, resolve, relative, extname, basename, dirname } from 'path';
import { execSync } from 'child_process';
import { fileURLToPath } from 'url';

// Import validate-file.js functions for embedded code extraction
// Note: We'll call validate-file.js as subprocess, but need extractEmbeddedCode logic
function extractEmbeddedCode(content, filePath) {
  const ext = extname(filePath).toLowerCase();
  const embedded = [];
  const lines = content.split('\n');
  
  if (ext === '.yml' || ext === '.yaml') {
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (/^\s*(nix|bash|script|build|install):\s*\|/.test(line)) {
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
    }
  } else if (ext === '.toml') {
    for (let i = 0; i < lines.length; i++) {
      const line = lines[i];
      if (/^\s*\[.*script.*\]/.test(line) || /^\s*script\s*=/.test(line)) {
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
  }
  
  return embedded;
}

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

// Import validation logic - we'll call validate-file.js as a subprocess
const validateScript = resolve(__dirname, 'validate-file.js');

// Supported file extensions
const SUPPORTED_EXTENSIONS = {
  nix: ['.nix'],
  haskell: ['.hs'],
  purescript: ['.purs'],
  lean4: ['.lean'],
  bash: ['.sh', '.bash'],
  cpp23: ['.cpp', '.hpp', '.cc', '.cxx', '.h', '.hxx', '.cu', '.cuh'],
  literate: ['.lit', '.mdx', '.lit.hs', '.lit.cpp', '.lit.purs'],
  dhall: ['.dhall'],
  bazel: ['.bzl'],
  rust: ['.rs'],
  python: ['.py'],
};

// Directories to skip
const SKIP_DIRS = [
  '.git',
  'node_modules',
  '.cache',
  '.buck',
  'dist',
  'build',
  'target',
  '.stack-work',
  '.cabal-sandbox',
  '.ghc',
  'result',
  'result-*',
  '.direnv',
];

// Files to skip
const SKIP_FILES = [
  'flake.lock',
  'package-lock.json',
  'yarn.lock',
  'compile_commands.json',
];

/**
 * Determine file type from path
 */
function determineFileType(filePath) {
  const ext = extname(filePath);
  const name = basename(filePath);
  const fullPath = filePath.toLowerCase();
  
  // Literate programming files (check first - they have compound extensions)
  if (fullPath.endsWith('.lit.hs')) return 'literate';
  if (fullPath.endsWith('.lit.cpp')) return 'literate';
  if (fullPath.endsWith('.lit.purs')) return 'literate';
  if (ext === '.lit' || ext === '.mdx') return 'literate';
  
  // Check all extensions
  for (const [type, exts] of Object.entries(SUPPORTED_EXTENSIONS)) {
    if (exts.includes(ext)) {
      return type;
    }
  }
  
  // Config files with embedded code
  if (ext === '.yml' || ext === '.yaml' || ext === '.toml' || ext === '.json' || ext === '.ini') {
    return 'config';
  }
  
  // Check for bash shebang
  if (ext === '' || ext === '.sh' || ext === '.bash' || name.endsWith('.sh') || name.endsWith('.bash')) {
    try {
      if (existsSync(filePath)) {
        const content = readFileSync(filePath, 'utf-8');
        if (content.startsWith('#!/bin/bash') || content.startsWith('#!/usr/bin/env bash')) {
          return 'bash';
        }
        if (content.startsWith('#!/usr/bin/env python') || content.startsWith('#!/usr/bin/python')) {
          return 'python';
        }
      }
    } catch {
      // File might not be readable
    }
  }
  
  return null;
}

/**
 * Check if directory should be skipped
 */
function shouldSkipDir(dirName) {
  return SKIP_DIRS.some(skip => dirName === skip || dirName.startsWith(skip));
}

/**
 * Check if file should be skipped
 */
function shouldSkipFile(fileName) {
  return SKIP_FILES.includes(fileName);
}

/**
 * Recursively find all files to validate
 */
function findFiles(rootDir, baseDir = rootDir) {
  const files = [];
  
  try {
    const entries = readdirSync(rootDir, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = join(rootDir, entry.name);
      const relPath = relative(baseDir, fullPath);
      
      // Skip directories
      if (entry.isDirectory()) {
        if (shouldSkipDir(entry.name)) {
          continue;
        }
        // Recurse
        files.push(...findFiles(fullPath, baseDir));
        continue;
      }
      
      // Skip files
      if (shouldSkipFile(entry.name)) {
        continue;
      }
      
      // Check if file type is supported
      const fileType = determineFileType(fullPath);
      if (fileType) {
        files.push({
          path: fullPath,
          relPath: relPath,
          type: fileType,
        });
      }
    }
  } catch (error) {
    // Skip directories we can't read
    if (error.code !== 'EACCES' && error.code !== 'ENOENT') {
      console.warn(`Warning: Could not read ${rootDir}: ${error.message}`);
    }
  }
  
  return files;
}

/**
 * Validate a single file
 */
function validateFile(filePath) {
  try {
    const output = execSync(`node "${validateScript}" "${filePath}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
      maxBuffer: 10 * 1024 * 1024, // 10MB buffer
    });
    
    return {
      valid: true,
      warnings: [],
      errors: [],
      output: output.trim(),
    };
  } catch (error) {
    // Parse error output
    const errorOutput = error.stdout || error.stderr || error.message;
    const lines = errorOutput.split('\n');
    
    const errors = [];
    const warnings = [];
    let valid = false;
    
    for (const line of lines) {
      // Parse error lines: "  Line X: [RULE] message"
      const errorMatch = line.match(/Line\s+(\d+):\s+\[([^\]]+)\]\s+(.+)/);
      if (errorMatch) {
        errors.push({
          line: parseInt(errorMatch[1]),
          rule: errorMatch[2],
          message: errorMatch[3],
        });
      }
      
      // Parse warning lines: "  Line X: [RULE] ⚠️ message"
      const warningMatch = line.match(/Line\s+(\d+):\s+\[([^\]]+)\]\s+⚠️\s+(.+)/);
      if (warningMatch) {
        warnings.push({
          line: parseInt(warningMatch[1]),
          rule: warningMatch[2],
          message: warningMatch[3],
        });
      }
      
      // Check if file is valid
      if (line.includes('✅') && line.includes('is valid')) {
        valid = true;
      }
    }
    
    // If exit code was 0, file is valid (even with warnings)
    if (error.status === 0 || error.code === 0) {
      valid = true;
    }
    
    return {
      valid,
      errors,
      warnings,
      output: errorOutput.trim(),
    };
  }
}

/**
 * Main execution
 */
function main() {
  const targetDir = process.argv[2] || '../straylight-protocol';
  const outputFormat = process.argv[3] || 'text'; // 'text', 'json'
  const isJSON = outputFormat === 'json';
  
  const absoluteTargetDir = resolve(targetDir);
  
  if (!existsSync(absoluteTargetDir)) {
    if (!isJSON) console.error(`❌ Error: Directory not found: ${absoluteTargetDir}`);
    process.exit(1);
  }
  
  if (!isJSON) {
    console.log(`🔍 Scanning directory: ${absoluteTargetDir}`);
    console.log(`📋 Finding all files to validate...\n`);
  }
  
  const files = findFiles(absoluteTargetDir);
  
  if (files.length === 0) {
    if (!isJSON) console.error(`❌ No files found to validate`);
    process.exit(1);
  }
  
  if (!isJSON) {
    console.log(`Found ${files.length} files to validate:\n`);
    console.log(`  Nix:        ${files.filter(f => f.type === 'nix').length}`);
    console.log(`  Haskell:    ${files.filter(f => f.type === 'haskell').length}`);
    console.log(`  PureScript: ${files.filter(f => f.type === 'purescript').length}`);
    console.log(`  Lean4:      ${files.filter(f => f.type === 'lean4').length}`);
    console.log(`  Bash:       ${files.filter(f => f.type === 'bash').length}`);
    console.log(`  C++:        ${files.filter(f => f.type === 'cpp23').length}`);
    console.log(`  Literate:   ${files.filter(f => f.type === 'literate').length}`);
    console.log(`  Dhall:      ${files.filter(f => f.type === 'dhall').length}`);
    console.log(`  Bazel:      ${files.filter(f => f.type === 'bazel').length}`);
    console.log(`  Rust:       ${files.filter(f => f.type === 'rust').length}`);
    console.log(`  Python:     ${files.filter(f => f.type === 'python').length}`);
    console.log(`  Config:     ${files.filter(f => f.type === 'config').length}`);
    console.log(`\n🚀 Starting validation...\n`);
  }
  
  const results = {
    total: files.length,
    passed: 0,
    failed: 0,
    warnings: 0,
    files: [],
    ruleViolations: {},
    startTime: Date.now(),
  };
  
  // Validate files in batches for progress reporting
  const BATCH_SIZE = 50;
  for (let i = 0; i < files.length; i += BATCH_SIZE) {
    const batch = files.slice(i, i + BATCH_SIZE);
    const batchNum = Math.floor(i / BATCH_SIZE) + 1;
    const totalBatches = Math.ceil(files.length / BATCH_SIZE);
    
    if (!isJSON) {
      console.log(`Processing batch ${batchNum}/${totalBatches} (${i + 1}-${Math.min(i + BATCH_SIZE, files.length)}/${files.length})...`);
    }
    
    for (const file of batch) {
      const result = validateFile(file.path);
      
      const fileResult = {
        path: file.relPath,
        absolutePath: file.path,
        type: file.type,
        valid: result.valid,
        errors: result.errors,
        warnings: result.warnings,
      };
      
      results.files.push(fileResult);
      
      if (result.valid && result.errors.length === 0) {
        results.passed++;
      } else {
        results.failed++;
      }
      
      if (result.warnings.length > 0) {
        results.warnings += result.warnings.length;
      }
      
      // Count violations by rule
      for (const error of result.errors) {
        if (!results.ruleViolations[error.rule]) {
          results.ruleViolations[error.rule] = { count: 0, files: [] };
        }
        results.ruleViolations[error.rule].count++;
        if (!results.ruleViolations[error.rule].files.includes(file.relPath)) {
          results.ruleViolations[error.rule].files.push(file.relPath);
        }
      }
      
      for (const warning of result.warnings) {
        const ruleKey = `${warning.rule}-WARNING`;
        if (!results.ruleViolations[ruleKey]) {
          results.ruleViolations[ruleKey] = { count: 0, files: [] };
        }
        results.ruleViolations[ruleKey].count++;
        if (!results.ruleViolations[ruleKey].files.includes(file.relPath)) {
          results.ruleViolations[ruleKey].files.push(file.relPath);
        }
      }
    }
  }
  
  results.endTime = Date.now();
  results.duration = results.endTime - results.startTime;
  
  // JSON output (only JSON, no console output)
  if (isJSON) {
    console.log(JSON.stringify(results, null, 2));
    process.exit(results.failed > 0 ? 1 : 0);
    return;
  }
  
  // Generate report (text format)
  console.log(`\n${'='.repeat(80)}`);
  console.log(`VALIDATION COMPLETE`);
  console.log(`${'='.repeat(80)}\n`);
  
  console.log(`📊 Summary:`);
  console.log(`  Total files:     ${results.total}`);
  console.log(`  ✅ Passed:       ${results.passed}`);
  console.log(`  ❌ Failed:       ${results.failed}`);
  console.log(`  ⚠️  Warnings:    ${results.warnings}`);
  console.log(`  ⏱️  Duration:     ${(results.duration / 1000).toFixed(2)}s`);
  console.log(`\n`);
  
  if (Object.keys(results.ruleViolations).length > 0) {
    console.log(`📋 Violations by Rule:`);
    const sortedRules = Object.entries(results.ruleViolations)
      .sort((a, b) => b[1].count - a[1].count);
    
    for (const [rule, data] of sortedRules) {
      console.log(`  ${rule}: ${data.count} violation(s) in ${data.files.length} file(s)`);
      if (data.files.length <= 5) {
        for (const file of data.files) {
          console.log(`    - ${file}`);
        }
      } else {
        for (const file of data.files.slice(0, 5)) {
          console.log(`    - ${file}`);
        }
        console.log(`    ... and ${data.files.length - 5} more`);
      }
    }
    console.log(`\n`);
  }
  
  // List files with violations
  const filesWithViolations = results.files.filter(f => !f.valid || f.errors.length > 0);
  if (filesWithViolations.length > 0) {
    console.log(`❌ Files with Errors (${filesWithViolations.length}):`);
    for (const file of filesWithViolations.slice(0, 20)) {
      console.log(`  ${file.path}`);
      for (const error of file.errors) {
        console.log(`    Line ${error.line}: [${error.rule}] ${error.message}`);
      }
    }
    if (filesWithViolations.length > 20) {
      console.log(`  ... and ${filesWithViolations.length - 20} more files`);
    }
    console.log(`\n`);
  }
  
  // List files with warnings only
  const filesWithWarningsOnly = results.files.filter(f => f.valid && f.errors.length === 0 && f.warnings.length > 0);
  if (filesWithWarningsOnly.length > 0) {
    console.log(`⚠️  Files with Warnings Only (${filesWithWarningsOnly.length}):`);
    for (const file of filesWithWarningsOnly.slice(0, 10)) {
      console.log(`  ${file.path} (${file.warnings.length} warning(s))`);
    }
    if (filesWithWarningsOnly.length > 10) {
      console.log(`  ... and ${filesWithWarningsOnly.length - 10} more files`);
    }
    console.log(`\n`);
  }
  
  // Exit code
  if (results.failed > 0) {
    console.log(`\n❌ Validation failed: ${results.failed} file(s) have errors`);
    process.exit(1);
  } else {
    console.log(`\n✅ All files passed validation!`);
    if (results.warnings > 0) {
      console.log(`⚠️  Note: ${results.warnings} warning(s) found (non-blocking)`);
    }
    process.exit(0);
  }
}

main();
