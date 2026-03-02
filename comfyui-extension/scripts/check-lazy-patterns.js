#!/usr/bin/env node
/**
 * Lazy Code Pattern Detector
 * 
 * Detects lazy code patterns that violate System F/Omega principles:
 * - `??` (nullish coalescing)
 * - `?.` (optional chaining)
 * - `|| []` (lazy array defaults)
 * - `|| {}` (lazy object defaults)
 * - `return null` / `return undefined` (except documented exceptions)
 * - `as any` / `: any` (type escapes)
 * - `!` (non-null assertions)
 * 
 * Usage: node scripts/check-lazy-patterns.js [--fix] [--strict]
 */

import { readFileSync, readdirSync, statSync } from "fs";
import { join, relative } from "path";
import { fileURLToPath } from "url";
import { dirname } from "path";

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);
const rootDir = join(__dirname, "..");
const srcDir = join(rootDir, "ui", "src");

const EXCLUDE_PATTERNS = [
  /node_modules/,
  /\.git/,
  /dist/,
  /build/,
  /coverage/,
  /\.next/,
  /\.vite/,
  /\.cache/,
];

const EXCLUDE_FILES = [
  /\.d\.ts$/,
  /\.test\.ts$/,
  /\.spec\.ts$/,
  /\.test\.vue$/,
  /\.spec\.vue$/,
];

const ALLOWED_PATTERNS = [
  // Comments/documentation
  /\/\/.*\?\?/,
  /\/\*.*\?\?.*\*\//,
  /\/\/.*\?\./,
  /\/\*.*\?\..*\*\//,
  // String literals
  /["'].*\?\?.*["']/,
  /["'].*\?\.*["']/,
];

const EXCEPTION_COMMENTS = [
  /Vue template compatibility/,
  /valid exception/,
  /System F\/Omega.*exception/,
  /template.*compatibility/,
];

function shouldCheckFile(filePath) {
  if (EXCLUDE_PATTERNS.some((pattern) => pattern.test(filePath))) {
    return false;
  }
  if (EXCLUDE_FILES.some((pattern) => pattern.test(filePath))) {
    return false;
  }
  return /\.(ts|vue|js)$/.test(filePath);
}

function isAllowedPattern(line, pattern) {
  return ALLOWED_PATTERNS.some((allowed) => allowed.test(line));
}

function hasExceptionComment(lines, lineIndex) {
  // Check 3 lines before and after
  const start = Math.max(0, lineIndex - 3);
  const end = Math.min(lines.length, lineIndex + 4);
  const context = lines.slice(start, end).join("\n");
  return EXCEPTION_COMMENTS.some((pattern) => pattern.test(context));
}

function findLazyPatterns(filePath) {
  const content = readFileSync(filePath, "utf-8");
  const lines = content.split("\n");
  const issues = [];

  lines.forEach((line, index) => {
    const lineNum = index + 1;
    const relativePath = relative(rootDir, filePath);

    // Skip comments and string literals
    if (isAllowedPattern(line, "")) {
      return;
    }

    // Check for ?? (nullish coalescing)
    if (/\?\?/.test(line) && !isAllowedPattern(line, "??")) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "??",
          code: line.trim(),
          severity: "error",
          message: "Nullish coalescing (??) detected. Use explicit pattern matching instead.",
        });
      }
    }

    // Check for ?. (optional chaining) - only in production code
    if (/\?\./.test(line) && !isAllowedPattern(line, "?.")) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "?.",
          code: line.trim(),
          severity: "error",
          message: "Optional chaining (?.) detected. Use explicit nested if conditions instead.",
        });
      }
    }

    // Check for || [] (lazy array defaults)
    if (/\|\|\s*\[\]/.test(line)) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "|| []",
          code: line.trim(),
          severity: "error",
          message: "Lazy array default (|| []) detected. Use explicit Array.isArray() check instead.",
        });
      }
    }

    // Check for || {} (lazy object defaults)
    if (/\|\|\s*\{\}/.test(line)) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "|| {}",
          code: line.trim(),
          severity: "error",
          message: "Lazy object default (|| {}) detected. Use explicit object type check instead.",
        });
      }
    }

    // Check for return null/undefined (except documented exceptions)
    if (/return\s+(null|undefined)/.test(line)) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "return null/undefined",
          code: line.trim(),
          severity: "error",
          message: "Return null/undefined detected. Throw explicit error or document as valid exception.",
        });
      }
    }

    // Check for as any / : any (type escapes)
    if (/(:\s*any\b|as\s+any\b)/.test(line)) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "as any / : any",
          code: line.trim(),
          severity: "warn",
          message: "Type escape (as any / : any) detected. Use proper type narrowing instead.",
        });
      }
    }

    // Check for ! (non-null assertions)
    if (/[^=!<>]\s*!\s*[^=]/.test(line) && /[a-zA-Z_$][a-zA-Z0-9_$]*\s*!/.test(line)) {
      if (!hasExceptionComment(lines, index)) {
        issues.push({
          file: relativePath,
          line: lineNum,
          pattern: "!",
          code: line.trim(),
          severity: "warn",
          message: "Non-null assertion (!) detected. Use explicit type guard instead.",
        });
      }
    }
  });

  return issues;
}

function scanDirectory(dir, issues = []) {
  const entries = readdirSync(dir);

  for (const entry of entries) {
    const fullPath = join(dir, entry);
    const stat = statSync(fullPath);

    if (stat.isDirectory()) {
      if (!EXCLUDE_PATTERNS.some((pattern) => pattern.test(fullPath))) {
        scanDirectory(fullPath, issues);
      }
    } else if (shouldCheckFile(fullPath)) {
      const fileIssues = findLazyPatterns(fullPath);
      issues.push(...fileIssues);
    }
  }

  return issues;
}

function main() {
  const args = process.argv.slice(2);
  const strict = args.includes("--strict");
  const fix = args.includes("--fix");

  console.log("🔍 Scanning for lazy code patterns...\n");

  const issues = scanDirectory(srcDir);

  const errors = issues.filter((i) => i.severity === "error");
  const warnings = issues.filter((i) => i.severity === "warn");

  // Group by pattern type
  const byPattern = {};
  issues.forEach((issue) => {
    if (!byPattern[issue.pattern]) {
      byPattern[issue.pattern] = [];
    }
    byPattern[issue.pattern].push(issue);
  });

  // Print summary
  console.log("📊 Summary:");
  console.log(`   Total issues: ${issues.length}`);
  console.log(`   Errors: ${errors.length}`);
  console.log(`   Warnings: ${warnings.length}\n`);

  if (Object.keys(byPattern).length > 0) {
    console.log("📋 By Pattern:");
    Object.entries(byPattern).forEach(([pattern, patternIssues]) => {
      console.log(`   ${pattern}: ${patternIssues.length}`);
    });
    console.log();
  }

  // Print errors
  if (errors.length > 0) {
    console.log("❌ Errors:");
    errors.forEach((issue) => {
      console.log(`   ${issue.file}:${issue.line}`);
      console.log(`      Pattern: ${issue.pattern}`);
      console.log(`      ${issue.message}`);
      console.log(`      Code: ${issue.code}`);
      console.log();
    });
  }

  // Print warnings (if strict mode)
  if (strict && warnings.length > 0) {
    console.log("⚠️  Warnings:");
    warnings.forEach((issue) => {
      console.log(`   ${issue.file}:${issue.line}`);
      console.log(`      Pattern: ${issue.pattern}`);
      console.log(`      ${issue.message}`);
      console.log(`      Code: ${issue.code}`);
      console.log();
    });
  }

  // Exit with error code if issues found
  const exitCode = strict ? (issues.length > 0 ? 1 : 0) : (errors.length > 0 ? 1 : 0);
  process.exit(exitCode);
}

main();
