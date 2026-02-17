#!/usr/bin/env node
/**
 * Stratified validation strategy for large codebases
 * Validates files using stratified sampling to ensure comprehensive coverage
 * while maintaining performance
 */

import { readdirSync, statSync, existsSync } from 'fs';
import { join, resolve, relative, extname, basename } from 'path';
import { execSync } from 'child_process';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

const validateScript = resolve(__dirname, 'validate-file.js');

// Configuration
const FULL_COVERAGE_PATHS = process.argv.includes('--full-coverage-paths')
  ? process.argv[process.argv.indexOf('--full-coverage-paths') + 1].split(',')
  : ['nix/modules/', 'nix/scripts/', 'src/'];
const FULL_COVERAGE_SIZE = parseInt(process.argv.find(arg => arg.startsWith('--full-coverage-size'))?.split('=')[1] || '300');
const SAMPLE_RATE = parseFloat(process.argv.find(arg => arg.startsWith('--sample-rate'))?.split('=')[1] || '0.2');
const PARALLEL = parseInt(process.argv.find(arg => arg.startsWith('--parallel'))?.split('=')[1] || '4');

function determineFileType(filePath) {
  const ext = extname(filePath);
  const name = basename(filePath);
  if (ext === '.lit' || ext === '.mdx' || name.endsWith('.lit.hs') || name.endsWith('.lit.cpp') || name.endsWith('.lit.purs')) return 'literate';
  if (ext === '.nix') return 'nix';
  if (ext === '.hs') return 'haskell';
  if (ext === '.purs') return 'purescript';
  if (ext === '.lean') return 'lean4';
  if (ext === '.sh' || ext === '.bash' || name.endsWith('.sh') || name.endsWith('.bash')) {
    try {
      if (existsSync(filePath)) {
        const content = require('fs').readFileSync(filePath, 'utf-8');
        if (content.startsWith('#!/bin/bash') || content.startsWith('#!/usr/bin/env bash')) return 'bash';
      }
    } catch {}
  }
  if (['.cpp', '.hpp', '.cc', '.cxx', '.h', '.hxx'].includes(ext)) return 'cpp23';
  return null;
}

function shouldSkip(filePath) {
  const skipDirs = ['.git', 'node_modules', '.cache', 'dist', 'build', 'target', 'result'];
  return skipDirs.some(dir => filePath.includes(`/${dir}/`) || filePath.includes(`\\${dir}\\`));
}

function findFiles(dir, fileList = []) {
  const files = readdirSync(dir);
  for (const file of files) {
    const filePath = join(dir, file);
    if (shouldSkip(filePath)) continue;
    const stat = statSync(filePath);
    if (stat.isDirectory()) {
      findFiles(filePath, fileList);
    } else {
      const type = determineFileType(filePath);
      if (type) {
        const content = require('fs').readFileSync(filePath, 'utf-8');
        const lines = content.split('\n').length;
        fileList.push({
          path: filePath,
          type,
          lines,
          size: stat.size,
        });
      }
    }
  }
  return fileList;
}

function stratifyFiles(files) {
  const strata = {
    fullCoverage: [],
    largeFiles: [],
    criticalPaths: [],
    sample: [],
  };
  
  for (const file of files) {
    const normalizedPath = file.path.replace(/\\/g, '/');
    
    // Full coverage: critical paths
    if (FULL_COVERAGE_PATHS.some(path => normalizedPath.includes(path))) {
      strata.fullCoverage.push(file);
      continue;
    }
    
    // Full coverage: large files
    if (file.lines >= FULL_COVERAGE_SIZE) {
      strata.largeFiles.push(file);
      continue;
    }
    
    // Sample: smaller files
    if (Math.random() < SAMPLE_RATE) {
      strata.sample.push(file);
    }
  }
  
  return strata;
}

function validateFile(filePath) {
  try {
    const output = execSync(`node "${validateScript}" "${filePath}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
      maxBuffer: 10 * 1024 * 1024,
    });
    return { valid: true, errors: [], warnings: [], output: output.trim() };
  } catch (error) {
    const errorOutput = error.stdout || error.stderr || error.message;
    const lines = errorOutput.split('\n');
    const errors = [];
    const warnings = [];
    for (const line of lines) {
      const errorMatch = line.match(/Line\s+(\d+):\s+\[([^\]]+)\]\s+(.+)/);
      if (errorMatch) {
        errors.push({ line: parseInt(errorMatch[1]), rule: errorMatch[2], message: errorMatch[3] });
      }
      const warningMatch = line.match(/Line\s+(\d+):\s+\[([^\]]+)\]\s+⚠️\s+(.+)/);
      if (warningMatch) {
        warnings.push({ line: parseInt(warningMatch[1]), rule: warningMatch[2], message: warningMatch[3] });
      }
    }
    return {
      valid: error.status === 0 || error.code === 0,
      errors,
      warnings,
      output: errorOutput.trim(),
    };
  }
}

function main() {
  const targetDir = process.argv[2] || '../straylight-protocol';
  const absoluteTargetDir = resolve(targetDir);
  
  if (!existsSync(absoluteTargetDir)) {
    console.error(`❌ Directory not found: ${absoluteTargetDir}`);
    process.exit(1);
  }
  
  console.log(`🔍 Stratified validation strategy`);
  console.log(`📁 Target: ${absoluteTargetDir}`);
  console.log(`📊 Full coverage paths: ${FULL_COVERAGE_PATHS.join(', ')}`);
  console.log(`📏 Full coverage size: ${FULL_COVERAGE_SIZE}+ lines`);
  console.log(`🎲 Sample rate: ${(SAMPLE_RATE * 100).toFixed(0)}%`);
  console.log(`\n🔎 Discovering files...\n`);
  
  const allFiles = findFiles(absoluteTargetDir);
  const strata = stratifyFiles(allFiles);
  
  console.log(`📋 File distribution:`);
  console.log(`   Total files: ${allFiles.length}`);
  console.log(`   Full coverage (critical paths): ${strata.fullCoverage.length}`);
  console.log(`   Full coverage (large files): ${strata.largeFiles.length}`);
  console.log(`   Sampled: ${strata.sample.length}`);
  console.log(`   Total to validate: ${strata.fullCoverage.length + strata.largeFiles.length + strata.sample.length}`);
  console.log(`\n🚀 Starting validation...\n`);
  
  const filesToValidate = [
    ...strata.fullCoverage,
    ...strata.largeFiles,
    ...strata.sample,
  ];
  
  const results = {
    total: filesToValidate.length,
    passed: 0,
    failed: 0,
    warnings: 0,
    files: [],
    ruleViolations: {},
    startTime: Date.now(),
  };
  
  // Validate in batches
  const BATCH_SIZE = PARALLEL;
  for (let i = 0; i < filesToValidate.length; i += BATCH_SIZE) {
    const batch = filesToValidate.slice(i, i + BATCH_SIZE);
    const batchResults = batch.map(file => {
      const result = validateFile(file.path);
      return { file, result };
    });
    
    for (const { file, result } of batchResults) {
      if (result.valid && result.errors.length === 0) {
        results.passed++;
      } else {
        results.failed++;
      }
      if (result.warnings.length > 0) {
        results.warnings += result.warnings.length;
      }
      
      results.files.push({
        path: relative(absoluteTargetDir, file.path),
        type: file.type,
        lines: file.lines,
        valid: result.valid,
        errors: result.errors,
        warnings: result.warnings,
      });
      
      // Aggregate rule violations
      for (const error of result.errors) {
        if (!results.ruleViolations[error.rule]) {
          results.ruleViolations[error.rule] = 0;
        }
        results.ruleViolations[error.rule]++;
      }
    }
    
    const progress = ((i + batch.length) / filesToValidate.length * 100).toFixed(1);
    process.stdout.write(`\r⏳ Progress: ${progress}% (${i + batch.length}/${filesToValidate.length})`);
  }
  
  results.duration = Date.now() - results.startTime;
  
  console.log(`\n\n✅ Validation complete!\n`);
  console.log(`📊 Results:`);
  console.log(`   ✅ Passed: ${results.passed}`);
  console.log(`   ❌ Failed: ${results.failed}`);
  console.log(`   ⚠️  Warnings: ${results.warnings}`);
  console.log(`   ⏱️  Duration: ${(results.duration / 1000).toFixed(2)}s`);
  console.log(`   📈 Speed: ${(results.total / (results.duration / 1000)).toFixed(1)} files/sec\n`);
  
  if (Object.keys(results.ruleViolations).length > 0) {
    console.log(`📋 Top violations:`);
    const sorted = Object.entries(results.ruleViolations)
      .sort((a, b) => b[1] - a[1])
      .slice(0, 10);
    for (const [rule, count] of sorted) {
      console.log(`   ${rule}: ${count}`);
    }
  }
  
  if (results.failed > 0) {
    process.exit(1);
  }
}

main();
