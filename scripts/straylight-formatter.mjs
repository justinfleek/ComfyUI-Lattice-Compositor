#!/usr/bin/env node
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                               // straylight // formatter
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import { readdirSync, readFileSync, statSync, writeFileSync } from "fs";
import { extname, join, relative } from "path";
import { argv, cwd } from "process";

const LINE_WIDTH = 78;
const HEAVY = "━"; // file-level framing
const DOUBLE = "═"; // major sections
const LIGHT = "─"; // subsections
const EM = "—"; // attribution

const SKIP_DIRS = [
  "node_modules",
  "dist",
  "dist-newstyle",
  ".git",
  "__pycache__",
  "coverage",
  "build",
];
const EXTENSIONS = [
  ".ts",
  ".tsx",
  ".js",
  ".jsx",
  ".mjs",
  ".cjs",
  ".vue",
  ".hs",
  ".nix",
  ".purs",
];

function getPrefix(filePath) {
  const ext = extname(filePath).toLowerCase();
  if ([".hs", ".purs"].includes(ext)) return "--";
  if ([".nix"].includes(ext)) return "#";
  return "//";
}

function makeLine(char, prefix) {
  const len = LINE_WIDTH - prefix.length - 1;
  return `${prefix} ${char.repeat(len)}`;
}

function rightAlign(text, prefix) {
  const padLen = LINE_WIDTH - prefix.length - 1 - text.length;
  return `${prefix} ${" ".repeat(Math.max(0, padLen))}${text}`;
}

function makeInlineHeader(name, prefix) {
  // # ── section name ─────────────────────────────────────────────────────────── (77 chars)
  const start = `${prefix} ${LIGHT}${LIGHT} ${name} `;
  const remaining = 77 - start.length;
  return start + LIGHT.repeat(Math.max(3, remaining));
}

function transformFile(content, filePath) {
  const prefix = getPrefix(filePath);
  const lines = content.split("\n");
  let changed = false;
  let firstEqualsBlockSeen = false;

  const result = lines.map((line, idx) => {
    const trimmed = line.trimEnd();

    // // ============ -> heavy (first) or double (subsequent)
    if (/^(\s*)(\/\/|--|#)\s*[=]{10,}\s*$/.test(trimmed)) {
      const m = trimmed.match(/^(\s*)(\/\/|--|#)/);
      let char;
      if (!firstEqualsBlockSeen) {
        char = HEAVY;
        firstEqualsBlockSeen = true;
      } else {
        char = DOUBLE;
      }
      const newLine = m[1] + makeLine(char, m[2]);
      if (newLine !== line) changed = true;
      return newLine;
    }

    // // ------------ -> light
    if (/^(\s*)(\/\/|--|#)\s*[-]{10,}\s*$/.test(trimmed)) {
      const m = trimmed.match(/^(\s*)(\/\/|--|#)/);
      const newLine = m[1] + makeLine(LIGHT, m[2]);
      if (newLine !== line) changed = true;
      return newLine;
    }

    // // SECTION TITLE -> right-aligned // section // title
    if (/^(\s*)(\/\/|--|#)\s+([A-Z][A-Z0-9 _-]*[A-Z0-9])\s*$/.test(trimmed)) {
      const m = trimmed.match(
        /^(\s*)(\/\/|--|#)\s+([A-Z][A-Z0-9 _-]*[A-Z0-9])\s*$/,
      );
      const indent = m[1];
      const cp = m[2];
      const words = m[3]
        .toLowerCase()
        .trim()
        .split(/[\s_-]+/)
        .filter(Boolean);
      const title = "// " + words.join(" // ");
      const newLine = indent + rightAlign(title, cp);
      if (newLine !== line) changed = true;
      return newLine;
    }

    // // -- section -- or // ── section ── -> inline header
    if (
      /^(\s*)(\/\/|--|#)\s*[-─]{2,}\s+([^-─]+)\s+[-─]{2,}\s*$/.test(trimmed)
    ) {
      const m = trimmed.match(
        /^(\s*)(\/\/|--|#)\s*[-─]{2,}\s+([^-─]+)\s+[-─]{2,}\s*$/,
      );
      const indent = m[1];
      const cp = m[2];
      const name = m[3].trim();
      const newLine = indent + makeInlineHeader(name, cp);
      if (newLine !== line) changed = true;
      return newLine;
    }

    // attribution: -- Author or — Author -> right-aligned — Author
    if (/^(\s*)(\/\/|--|#)\s+([-—])\s*([A-Z][\w\s.,]+)\s*$/.test(trimmed)) {
      const m = trimmed.match(
        /^(\s*)(\/\/|--|#)\s+([-—])\s*([A-Z][\w\s.,]+)\s*$/,
      );
      const indent = m[1];
      const cp = m[2];
      const attr = `${EM} ${m[4].trim()}`;
      const newLine = indent + rightAlign(attr, cp);
      if (newLine !== line) changed = true;
      return newLine;
    }

    return line;
  });

  return { content: result.join("\n"), changed };
}

function collectFiles(targetPath, files = []) {
  const stats = statSync(targetPath);
  if (stats.isFile()) {
    if (EXTENSIONS.includes(extname(targetPath).toLowerCase()))
      files.push(targetPath);
    return files;
  }
  if (stats.isDirectory() && !SKIP_DIRS.includes(targetPath.split("/").pop())) {
    for (const entry of readdirSync(targetPath)) {
      const full = join(targetPath, entry);
      const s = statSync(full);
      if (s.isFile() || (s.isDirectory() && !SKIP_DIRS.includes(entry))) {
        collectFiles(full, files);
      }
    }
  }
  return files;
}

function main() {
  const args = argv.slice(2);
  const dryRun = args.includes("--dry-run");
  const target = args.find((a) => !a.startsWith("--")) || cwd();
  const resolved = target.startsWith("/") ? target : join(cwd(), target);

  console.log(`// straylight // formatter`);
  console.log(`// mode: ${dryRun ? "dry-run" : "write"}\n`);

  const files = collectFiles(resolved);
  let changed = 0;

  for (const f of files) {
    try {
      const content = readFileSync(f, "utf-8");
      const result = transformFile(content, f);
      if (result.changed) {
        changed++;
        const rel = relative(cwd(), f);
        if (dryRun) {
          console.log(`// would change: ${rel}`);
        } else {
          writeFileSync(f, result.content, "utf-8");
          console.log(`// formatted: ${rel}`);
        }
      }
    } catch (e) {
      console.error(`// error: ${f} - ${e.message}`);
    }
  }

  console.log(`\n// changed: ${changed} files`);
}

main();
