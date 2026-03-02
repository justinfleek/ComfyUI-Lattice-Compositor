#!/usr/bin/env node
/**
 * File watcher that validates files on save
 * Can be run as a background process to enforce protocol in real-time
 */

import { watch, existsSync } from 'fs';
import { exec } from 'child_process';
import { promisify } from 'util';
import { extname } from 'path';

const execAsync = promisify(exec);

const WATCH_PATTERNS = [
  '**/*.nix',
  '**/*.hs',
  '**/*.purs',
  '**/*.lean',
  '**/*.sh',
  '**/*.bash',
  '**/*.lit',
  '**/*.mdx',
  '**/*.lit.hs',
  '**/*.lit.cpp',
  '**/*.lit.purs',
  '**/*.cpp',
  '**/*.hpp',
  '**/*.cc',
  '**/*.h',
  '**/*.cu',
  '**/*.cuh',
  '**/*.dhall',
  '**/*.bzl',
  '**/*.rs',
  '**/*.py',
];

// Watch directories - update to match your project structure
// Checks for straylight-core/ first, then falls back to common alternatives
const possibleDirs = ['straylight-core', 'nix', 'src'];
const WATCH_DIRS = possibleDirs.filter(dir => {
  try {
    return existsSync(dir);
  } catch {
    return false;
  }
});

// If none exist, default to straylight-core (user can update)
if (WATCH_DIRS.length === 0) {
  WATCH_DIRS.push('straylight-core');
  console.warn('⚠️  No watch directories found. Defaulting to "straylight-core".');
  console.warn('   Update WATCH_DIRS in watch-and-validate.js to match your structure.');
}

function shouldValidate(filePath) {
  const ext = extname(filePath);
  const name = filePath.toLowerCase();
  const validExts = ['.nix', '.hs', '.purs', '.lean', '.sh', '.bash', '.lit', '.mdx', '.cpp', '.hpp', '.cc', '.h', '.cu', '.cuh', '.dhall', '.bzl', '.rs', '.py'];
  const validCompound = ['.lit.hs', '.lit.cpp', '.lit.purs'];
  
  // Check compound extensions first
  for (const compound of validCompound) {
    if (name.endsWith(compound)) return true;
  }
  
  return validExts.includes(ext);
}

async function validateFile(filePath) {
  try {
    const { stdout, stderr } = await execAsync(
      `node scripts/validate-file.js "${filePath}"`
    );
    
    if (stderr) {
      console.error(`❌ ${filePath}: ${stderr}`);
      return false;
    }
    
    console.log(`✅ ${filePath}: Valid`);
    return true;
  } catch (error) {
    console.error(`❌ ${filePath}: Validation failed`);
    console.error(`   ${error.message}`);
    return false;
  }
}

function watchDirectory(dir) {
  console.log(`Watching ${dir} for changes...`);
  
  watch(dir, { recursive: true }, async (eventType, filename) => {
    if (!filename) return;
    
    const filePath = `${dir}/${filename}`;
    
    if (!shouldValidate(filePath)) {
      return;
    }
    
    // Debounce - wait a bit for file write to complete
    setTimeout(async () => {
      console.log(`\n📝 File changed: ${filePath}`);
      await validateFile(filePath);
    }, 500);
  });
}

// Start watching
console.log('🔍 Straylight Protocol File Watcher');
console.log('Watching for protocol violations in real-time...\n');

for (const dir of WATCH_DIRS) {
  try {
    watchDirectory(dir);
  } catch (error) {
    console.error(`Error watching ${dir}: ${error.message}`);
  }
}

console.log('\nPress Ctrl+C to stop watching...');
