#!/usr/bin/env node

/**
 * Package VSCode extension as ZIP file
 * 
 * Usage: node scripts/package.js
 * 
 * Creates: prism-theme-generator-<version>.zip
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

const packageJson = JSON.parse(
  fs.readFileSync(path.join(__dirname, '..', 'package.json'), 'utf8')
);

const version = packageJson.version;
const extensionName = packageJson.name;
const zipName = `${extensionName}-${version}.zip`;

const rootDir = path.join(__dirname, '..');
const outDir = path.join(rootDir, 'out');

// Check if compiled output exists
if (!fs.existsSync(outDir)) {
  console.error('Error: Extension not compiled. Run "npm run compile" first.');
  process.exit(1);
}

// Create temp directory for packaging
const tempDir = path.join(rootDir, '.package-temp');
if (fs.existsSync(tempDir)) {
  fs.rmSync(tempDir, { recursive: true, force: true });
}
fs.mkdirSync(tempDir, { recursive: true });

// Files/directories to include
const includePaths = [
  'package.json',
  'README.md',
  'out',
  'media'
];

// Copy files
includePaths.forEach(item => {
  const src = path.join(rootDir, item);
  const dest = path.join(tempDir, item);
  
  if (fs.existsSync(src)) {
    const stat = fs.statSync(src);
    if (stat.isDirectory()) {
      fs.cpSync(src, dest, { recursive: true });
    } else {
      fs.copyFileSync(src, dest);
    }
    console.log(`Included: ${item}`);
  } else {
    console.warn(`Warning: ${item} not found, skipping`);
  }
});

// Create ZIP file
const zipPath = path.join(rootDir, zipName);
try {
  // Use PowerShell on Windows, zip on Unix
  const isWindows = process.platform === 'win32';
  
  if (isWindows) {
    // PowerShell Compress-Archive
    const zipCmd = `Compress-Archive -Path "${tempDir}\\*" -DestinationPath "${zipPath}" -Force`;
    execSync(zipCmd, { shell: 'powershell', stdio: 'inherit' });
  } else {
    // Unix zip command
    const zipCmd = `cd "${tempDir}" && zip -r "${zipPath}" .`;
    execSync(zipCmd, { stdio: 'inherit' });
  }
  
  console.log(`\n✅ Package created: ${zipName}`);
  console.log(`   Size: ${(fs.statSync(zipPath).size / 1024).toFixed(2)} KB`);
  console.log(`\nTo install:`);
  console.log(`   1. Open VSCode`);
  console.log(`   2. Press F1 → "Extensions: Install from VSIX..."`);
  console.log(`   3. Select ${zipName}`);
  console.log(`\nOr rename to .vsix and install directly.`);
} catch (error) {
  console.error('Error creating ZIP:', error.message);
  process.exit(1);
} finally {
  // Cleanup temp directory
  if (fs.existsSync(tempDir)) {
    fs.rmSync(tempDir, { recursive: true, force: true });
  }
}
