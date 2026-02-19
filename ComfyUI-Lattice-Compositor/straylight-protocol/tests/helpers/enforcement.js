/**
 * Enforcement Test Helpers
 * Utilities for testing enforcement mechanisms
 */

import { execSync } from 'child_process';
import { readFileSync, writeFileSync, unlinkSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';

/**
 * Execute MCP tool via command line (simulating MCP server call)
 */
export function callMcpTool(tool, args) {
  // For testing, we'll simulate MCP calls by directly importing and calling
  // the validation logic from validate-file.js
  const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
  
  if (tool === 'straylight_validate') {
    // Create temp file with code
    const tempFile = join(tmpdir(), `test-${Date.now()}.${args.type || 'nix'}`);
    try {
      writeFileSync(tempFile, args.code);
      const result = execSync(`node "${validateScript}" "${tempFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      return { valid: true, output: result };
    } catch (error) {
      return {
        valid: false,
        errors: error.stdout || error.stderr,
        output: error.stdout + error.stderr,
      };
    } finally {
      if (existsSync(tempFile)) unlinkSync(tempFile);
    }
  }
  
  // Other tools would need actual MCP server connection
  return { error: 'Tool not implemented in test helper' };
}

/**
 * Execute git hook in test environment
 */
export function executePreCommitHook(files) {
  const hookPath = join(process.cwd(), 'hooks', 'pre-commit');
  const tempDir = join(tmpdir(), `git-test-${Date.now()}`);
  
  try {
    // Create temp git repo structure
    execSync(`mkdir -p "${tempDir}/.git/hooks"`, { shell: true });
    execSync(`cp "${hookPath}" "${tempDir}/.git/hooks/pre-commit"`, { shell: true });
    
    // Create test files
    for (const [file, content] of Object.entries(files)) {
      const filePath = join(tempDir, file);
      const dir = filePath.substring(0, filePath.lastIndexOf('/'));
      execSync(`mkdir -p "${dir}"`, { shell: true });
      writeFileSync(filePath, content);
    }
    
    // Try to execute hook
    const result = execSync(`cd "${tempDir}" && bash .git/hooks/pre-commit`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    return { success: true, output: result };
  } catch (error) {
    return {
      success: false,
      exitCode: error.status || 1,
      output: error.stdout + error.stderr,
    };
  } finally {
    // Cleanup
    try {
      execSync(`rm -rf "${tempDir}"`, { shell: true });
    } catch {}
  }
}

/**
 * Simulate CI workflow validation steps
 */
export function simulateCiWorkflow(files) {
  const results = [];
  
  for (const [file, content] of Object.entries(files)) {
    const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
    const tempFile = join(tmpdir(), `ci-test-${Date.now()}-${file}`);
    
    try {
      writeFileSync(tempFile, content);
      const result = execSync(`node "${validateScript}" "${tempFile}"`, {
        encoding: 'utf-8',
        stdio: 'pipe',
      });
      results.push({ file, valid: true, output: result });
    } catch (error) {
      results.push({
        file,
        valid: false,
        errors: error.stdout + error.stderr,
      });
    } finally {
      if (existsSync(tempFile)) unlinkSync(tempFile);
    }
  }
  
  return results;
}

/**
 * Simulate file watcher validation
 */
export function simulateFileWatcher(file, content) {
  const validateScript = join(process.cwd(), 'scripts', 'validate-file.js');
  const tempFile = join(tmpdir(), `watcher-test-${Date.now()}-${file}`);
  
  try {
    writeFileSync(tempFile, content);
    const result = execSync(`node "${validateScript}" "${tempFile}"`, {
      encoding: 'utf-8',
      stdio: 'pipe',
    });
    return { valid: true, output: result };
  } catch (error) {
    return {
      valid: false,
      errors: error.stdout + error.stderr,
    };
  } finally {
    if (existsSync(tempFile)) unlinkSync(tempFile);
  }
}
