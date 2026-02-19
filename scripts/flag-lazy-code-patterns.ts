#!/usr/bin/env tsx
/**
 * Lazy Code Pattern Flagging Tool
 *
 * Identifies suspicious lazy code patterns that need manual review.
 * Does NOT fix them - only flags for human judgment.
 *
 * Usage:
 *   npx tsx scripts/flag-lazy-code-patterns.ts > lazy-code-audit.md
 *
 * Patterns Flagged:
 * - Type escapes (as any, : any, as unknown)
 * - Suspicious defensive guards (?? 0 where 0 is invalid, etc.)
 * - Optional chaining abuse (?.)
 * - NaN/Infinity from operations
 * - Functions that should return values but are : void
 */

import { readFileSync, readdirSync, statSync, writeFileSync } from "fs";
import { join, relative } from "path";

const UI_SRC = join(process.cwd(), "ui/src");

interface Flag {
  file: string;
  line: number;
  pattern: string;
  code: string;
  severity: "HIGH" | "MEDIUM" | "LOW";
  reason: string;
  suggestion?: string;
}

const flags: Flag[] = [];

// Patterns that indicate invalid defaults
const INVALID_ZERO_PATTERNS = [
  /frameCount\s*[?:]\s*0/,
  /frame\s*[?:]\s*0/,
  /id\s*[?:]\s*0/,
  /layerId\s*[?:]\s*0/,
  /duration\s*[?:]\s*0/,
  /width\s*[?:]\s*0/,
  /height\s*[?:]\s*0/,
  /fps\s*[?:]\s*0/,
];

// Patterns that indicate division operations (potential NaN/Infinity)
const DIVISION_PATTERNS = [
  /\w+\s*\/\s*0\b/,
  /\w+\s*\/\s*\w+\s*[?:]\s*0/,
  /\w+\s*\/\s*\([^)]*\)\s*[?:]\s*0/,
];

function findTypeScriptFiles(): string[] {
  const files: string[] = [];

  function walkDir(dir: string): void {
    const entries = readdirSync(dir);
    for (const entry of entries) {
      const fullPath = join(dir, entry);
      const stat = statSync(fullPath);

      if (stat.isDirectory()) {
        // Skip test directories
        if (
          entry === "__tests__" ||
          entry === "__mocks__" ||
          entry === "node_modules"
        ) {
          continue;
        }
        walkDir(fullPath);
      } else if (entry.endsWith(".ts") && !entry.endsWith(".test.ts")) {
        files.push(fullPath);
      }
    }
  }

  walkDir(UI_SRC);
  return files;
}

function flagPattern(
  file: string,
  line: number,
  code: string,
  pattern: string,
  severity: "HIGH" | "MEDIUM" | "LOW",
  reason: string,
  suggestion?: string,
): void {
  const relativePath = relative(UI_SRC, file).replace(/\\/g, "/");
  flags.push({
    file: relativePath,
    line,
    pattern,
    code: code.trim(),
    severity,
    reason,
    suggestion,
  });
}

function analyzeFile(file: string): void {
  const content = readFileSync(file, "utf-8");
  const lines = content.split("\n");

  lines.forEach((line, index) => {
    const lineNum = index + 1;
    const trimmed = line.trim();

    // Skip comments
    if (trimmed.startsWith("//") || trimmed.startsWith("*")) return;

    //                                                                      // high
    if (/\bas any\b/.test(line)) {
      flagPattern(
        file,
        lineNum,
        line,
        "as any",
        "HIGH",
        "Type safety bypassed - need to determine correct type",
        "Replace with proper type assertion or fix underlying type issue",
      );
    }

    if (/: any[^A-Za-z]/.test(line)) {
      flagPattern(
        file,
        lineNum,
        line,
        ": any",
        "HIGH",
        "Untyped parameter/variable - need to determine correct type",
        "Replace with proper type annotation",
      );
    }

    if (/\bas unknown\b/.test(line)) {
      flagPattern(
        file,
        lineNum,
        line,
        "as unknown",
        "MEDIUM",
        "Type escape hatch - verify if necessary",
        "Consider if proper type narrowing is possible",
      );
    }

    //                                                                    // medium
    for (const pattern of INVALID_ZERO_PATTERNS) {
      if (pattern.test(line)) {
        flagPattern(
          file,
          lineNum,
          line,
          "?? 0 (invalid default)",
          "MEDIUM",
          "Defaulting to 0 may be invalid for this property",
          "Verify if 0 is valid default, or add proper validation/error handling",
        );
        break;
      }
    }

    //                                                                    // medium
    for (const pattern of DIVISION_PATTERNS) {
      if (pattern.test(line) && !line.includes("Number.isFinite")) {
        flagPattern(
          file,
          lineNum,
          line,
          "Division operation",
          "MEDIUM",
          "Division operation may produce NaN or Infinity",
          "Add divisor validation or Number.isFinite check",
        );
        break;
      }
    }

    //                                                                    // medium
    if (/\?\./.test(line)) {
      // Check if there's a null check in previous lines (simple heuristic)
      const context = lines.slice(Math.max(0, index - 3), index + 1).join(" ");
      if (
        /if\s*\([^)]*===?\s*null|if\s*\([^)]*!==?\s*null/.test(context) &&
        !/if\s*\([^)]*\?\./.test(context)
      ) {
        flagPattern(
          file,
          lineNum,
          line,
          "?. (redundant)",
          "MEDIUM",
          "Optional chaining used but null check exists before",
          "Consider removing optional chaining if null is already checked",
        );
      }
    }

    //                                                                       // low
    if (/:\s*void\s*[={]/.test(line) && /function|const\s+\w+\s*=\s*\(/.test(line)) {
      // Heuristic: functions with "get", "find", "calculate" might should return
      if (/get|find|calculate|compute|check|has|is/.test(line)) {
        flagPattern(
          file,
          lineNum,
          line,
          ": void (should return?)",
          "LOW",
          "Function name suggests it should return a value",
          "Review if function should return boolean/number/object instead of void",
        );
      }
    }
  });
}

function generateReport(): string {
  const high = flags.filter((f) => f.severity === "HIGH");
  const medium = flags.filter((f) => f.severity === "MEDIUM");
  const low = flags.filter((f) => f.severity === "LOW");

  let report = `# Lazy Code Pattern Audit Report\n\n`;
  report += `**Generated:** ${new Date().toISOString()}\n`;
  report += `**Total Flags:** ${flags.length}\n`;
  report += `- 🔴 HIGH: ${high.length}\n`;
  report += `- 🟡 MEDIUM: ${medium.length}\n`;
  report += `- 🟢 LOW: ${low.length}\n\n`;
  report += `---\n\n`;

  // Group by file
  const byFile = new Map<string, Flag[]>();
  flags.forEach((flag) => {
    if (!byFile.has(flag.file)) {
      byFile.set(flag.file, []);
    }
    byFile.get(flag.file)!.push(flag);
  });

  // Sort files by flag count
  const sortedFiles = Array.from(byFile.entries()).sort(
    (a, b) => b[1].length - a[1].length,
  );

  report += `## By File (${sortedFiles.length} files)\n\n`;

  for (const [file, fileFlags] of sortedFiles) {
    report += `### \`${file}\` (${fileFlags.length} flags)\n\n`;

    // Group by severity
    const fileHigh = fileFlags.filter((f) => f.severity === "HIGH");
    const fileMedium = fileFlags.filter((f) => f.severity === "MEDIUM");
    const fileLow = fileFlags.filter((f) => f.severity === "LOW");

    if (fileHigh.length > 0) {
      report += `#### 🔴 HIGH Priority (${fileHigh.length})\n\n`;
      fileHigh.forEach((flag) => {
        report += `- **Line ${flag.line}:** \`${flag.pattern}\`\n`;
        report += `  - Code: \`${flag.code}\`\n`;
        report += `  - Reason: ${flag.reason}\n`;
        if (flag.suggestion) {
          report += `  - Suggestion: ${flag.suggestion}\n`;
        }
        report += `\n`;
      });
    }

    if (fileMedium.length > 0) {
      report += `#### 🟡 MEDIUM Priority (${fileMedium.length})\n\n`;
      fileMedium.forEach((flag) => {
        report += `- **Line ${flag.line}:** \`${flag.pattern}\`\n`;
        report += `  - Code: \`${flag.code}\`\n`;
        report += `  - Reason: ${flag.reason}\n`;
        if (flag.suggestion) {
          report += `  - Suggestion: ${flag.suggestion}\n`;
        }
        report += `\n`;
      });
    }

    if (fileLow.length > 0) {
      report += `#### 🟢 LOW Priority (${fileLow.length})\n\n`;
      fileLow.forEach((flag) => {
        report += `- **Line ${flag.line}:** \`${flag.pattern}\`\n`;
        report += `  - Code: \`${flag.code}\`\n`;
        report += `  - Reason: ${flag.reason}\n`;
        if (flag.suggestion) {
          report += `  - Suggestion: ${flag.suggestion}\n`;
        }
        report += `\n`;
      });
    }

    report += `---\n\n`;
  }

  // Summary by pattern type
  report += `## Summary by Pattern Type\n\n`;

  const byPattern = new Map<string, Flag[]>();
  flags.forEach((flag) => {
    if (!byPattern.has(flag.pattern)) {
      byPattern.set(flag.pattern, []);
    }
    byPattern.get(flag.pattern)!.push(flag);
  });

  const sortedPatterns = Array.from(byPattern.entries()).sort(
    (a, b) => b[1].length - a[1].length,
  );

  for (const [pattern, patternFlags] of sortedPatterns) {
    const highCount = patternFlags.filter((f) => f.severity === "HIGH").length;
    const mediumCount = patternFlags.filter((f) => f.severity === "MEDIUM").length;
    const lowCount = patternFlags.filter((f) => f.severity === "LOW").length;

    report += `### \`${pattern}\` (${patternFlags.length} instances)\n`;
    report += `- 🔴 HIGH: ${highCount}\n`;
    report += `- 🟡 MEDIUM: ${mediumCount}\n`;
    report += `- 🟢 LOW: ${lowCount}\n\n`;
  }

  return report;
}

async function main() {
  console.error("🔍 Finding TypeScript files...");
  const files = findTypeScriptFiles();
  console.error(`   Found ${files.length} files\n`);

  console.error("🔎 Analyzing files for suspicious patterns...");
  for (const file of files) {
    analyzeFile(file);
  }

  console.error(`\n📊 Found ${flags.length} suspicious patterns\n`);

  const report = generateReport();
  console.log(report);

  // Also write to file
  const reportPath = join(process.cwd(), "docs/LAZY_CODE_AUDIT.md");
  writeFileSync(reportPath, report, "utf-8");
  console.error(`\n✅ Report written to: ${reportPath}`);
}

main().catch((error) => {
  console.error("❌ Error:", error);
  process.exit(1);
});
