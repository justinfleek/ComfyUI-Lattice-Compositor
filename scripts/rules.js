/**
 * Straylight Protocol Rules - Single Source of Truth
 * 
 * This module contains the canonical RULES object and MAX_FILE_LINES constant
 * that are used by all enforcement mechanisms (MCP server, validator, CI/CD, etc.)
 * 
 * Per SCOPE_GRAPH.md: "Single source of truth for rules"
 */

// File size limit: 500 lines per module
export const MAX_FILE_LINES = 500;

// Protocol rules extracted from RFCs
export const RULES = {
  nix: {
    forbidden: [
      {
        pattern: /^\s*with\s+lib\s*;/m,
        rule: "WSN-E001",
        message: "Use 'inherit (lib) x y;' instead of 'with lib;' (aleph-001, aleph-002 ALEPH-E001)",
        exception: /with\s+(pkgs|lib)\s*;\s*\[/, // Allow in list context per RFC ℵ-002
        check: (code, filePath) => {
          // Don't flag with lib; in comments
          const lines = code.split('\n');
          
          // First check for multi-line with lib; pattern
          // Pattern: "with" on one line, "lib;" on next line
          for (let i = 0; i < lines.length - 1; i++) {
            const line = lines[i];
            const nextLine = lines[i + 1];
            
            // Skip comment lines
            if (line.trim().startsWith('#')) continue;
            if (nextLine.trim().startsWith('#')) continue;
            
            // Check for multi-line: "with" at end of line, "lib;" at start of next
            if (/^\s*with\s*$/.test(line.trim()) && /^\s*lib\s*;/.test(nextLine.trim())) {
              // Check exception (list context) - look ahead a few lines
              const context = lines.slice(i, Math.min(i + 5, lines.length)).join('\n');
              if (/with\s+(pkgs|lib)\s*;\s*\[/.test(context)) return true;
              return false; // Found multi-line with lib; not in exception context
            }
          }
          
          // Check for with lib; anywhere in line (not just start)
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            // Skip comment lines
            if (line.trim().startsWith('#')) continue;
            
            // Check for with lib; pattern anywhere in line
            // Pattern: "with" followed by whitespace and "lib;"
            if (/\bwith\s+lib\s*;/.test(line)) {
              // Check exception (list context)
              if (/with\s+(pkgs|lib)\s*;\s*\[/.test(code)) return true;
              return false; // Found with lib; not in exception context
            }
          }
          return true;
        },
      },
      {
        pattern: /mkDerivation\s+rec\s*\{/,
        rule: "WSN-E002",
        message: "Use 'finalAttrs:' instead of 'rec' in mkDerivation (aleph-001, aleph-002 ALEPH-E002)",
      },
      {
        pattern: /rec\s*\{/,
        rule: "WSN-W001",
        message: "Avoid 'rec' attrsets - use 'finalAttrs:' or 'let'",
      },
      {
        pattern: /\b\w*[a-z][A-Z]\w*\b/,
        rule: "WSN-E003",
        message: "Use lisp-case, not camelCase or snake_case (aleph-001, aleph-002 ALEPH-E003)",
        check: (code, filePath) => {
          // Check for camelCase and snake_case identifiers
          // But exclude standard exceptions, comments, string literals, and heredoc contents

          // First, remove heredoc contents (''...'') from code to avoid false positives
          // Heredocs contain shell code, not Nix identifiers
          const codeWithoutHeredocs = code.replace(/''[\s\S]*?''/g, "''__HEREDOC__''");

          const lines = codeWithoutHeredocs.split('\n');
          const camelCasePattern = /\b\w*[a-z][A-Z]\w*\b/g;
          const snakeCasePattern = /\b\w*[a-z]_[a-z]\w*\b/g;
          // Standard Nix stdenv attributes that MUST be camelCase (API requirement)
          const exceptionWords = [
            // Core Nix functions and flake-parts
            'pkgs', 'lib', 'config', 'finalAttrs', 'mkDerivation', 'mkOption', 'mkIf', 'mkMerge', 'mkShell',
            'mkFlake', 'perSystem', 'flakeParts', 'devShells',
            // Standard nixpkgs URLs and attributes
            'NixOS', 'nixpkgs', 'nixosUnstable', 'nixosStable',
            // Package sets (required camelCase)
            'elmPackages', 'nodePackages', 'pythonPackages', 'haskellPackages', 'perlPackages',
            'rubyPackages', 'rustPackages', 'luaPackages', 'vimPlugins',
            // stdenv derivation phases (required camelCase)
            'buildPhase', 'installPhase', 'checkPhase', 'configurePhase', 'fixupPhase',
            'unpackPhase', 'patchPhase', 'preConfigurePhases', 'preBuildPhases',
            'preInstallPhases', 'postInstallPhases', 'postFixupPhases',
            // stdenv phase hooks (required camelCase)
            'preConfigure', 'postConfigure', 'preBuild', 'postBuild',
            'preInstall', 'postInstall', 'preFixup', 'postFixup',
            'preCheck', 'postCheck', 'preUnpack', 'postUnpack',
            'prePatch', 'postPatch',
            // stdenv inputs (required camelCase)
            'nativeBuildInputs', 'buildInputs', 'propagatedBuildInputs',
            'propagatedNativeBuildInputs', 'checkInputs', 'installCheckInputs',
            // Build system flags (required camelCase)
            'mesonFlags', 'cmakeFlags', 'configureFlags', 'makeFlags',
            'ninjaFlags', 'cargoFlags', 'goFlags',
            // stdenv attributes (required camelCase)
            'dontConfigure', 'dontBuild', 'dontInstall', 'dontFixup',
            'dontCheck', 'dontUnpack', 'dontPatch', 'dontStrip',
            'dontWrapGApps', 'dontWrapQtApps',
            // mkShell attributes (required camelCase)
            'shellHook', 'inputsFrom',
            // Derivation meta attributes (required camelCase)
            'mainProgram', 'outputsToInstall',
            // Fetchers (required camelCase)
            'fetchurl', 'fetchgit', 'fetchFromGitHub', 'fetchFromGitLab',
            // Python packages (required camelCase)
            'withPackages', 'sitePackages',
            // Write functions (required camelCase)
            'writeText', 'writeShellScript', 'writeShellApplication',
            'writeShellScriptBin', 'writeTextFile', 'writeScript', 'writeScriptBin',
            // Common path/module patterns (filesystem paths, not Nix identifiers)
            'TensorCore', 'AppData', 'LocalMachine', 'CurrentUser',
          ];

          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            // Skip comment lines
            if (line.trim().startsWith('#')) continue;
            // Skip heredoc placeholder lines
            if (line.includes('__HEREDOC__')) continue;

            // Skip if identifier is in a string literal (single or double quotes)
            // Check if line contains quoted strings and if identifier is inside them
            const stringPattern = /(["'])(?:(?=(\\?))\2.)*?\1/g;
            const stringRanges = [];
            let match;
            while ((match = stringPattern.exec(line)) !== null) {
              stringRanges.push({ start: match.index, end: match.index + match[0].length });
            }

            // Check for camelCase
            const camelMatches = [...line.matchAll(camelCasePattern)];
            for (const match of camelMatches) {
              const matchedText = match[0];
              const matchStart = match.index;
              const matchEnd = match.index + match[0].length;

              // Check if match is inside a string literal
              const inString = stringRanges.some(range => matchStart >= range.start && matchEnd <= range.end);
              if (inString) continue; // Skip camelCase in strings

              // Check if this match is an exception word
              const isException = exceptionWords.some(word => matchedText === word || matchedText.startsWith(word + '.'));
              if (!isException) {
                return false; // Found camelCase that's not an exception
              }
            }

            // Check for snake_case
            const snakeMatches = [...line.matchAll(snakeCasePattern)];
            for (const match of snakeMatches) {
              const matchedText = match[0];
              const matchStart = match.index;
              const matchEnd = match.index + match[0].length;

              // Check if match is inside a string literal
              const inString = stringRanges.some(range => matchStart >= range.start && matchEnd <= range.end);
              if (inString) continue; // Skip snake_case in strings

              // snake_case has no exceptions - always forbidden
              return false; // Found snake_case
            }
          }
          return true;
        },
      },
      {
        pattern: /straylight\.[a-zA-Z_]*[A-Z]/,
        rule: "WSN-E003",
        message: "camelCase in straylight.* namespace forbidden - use lisp-case",
      },
      {
        pattern: /default\.nix/,
        rule: "WSN-E005",
        message: "Don't use default.nix in packages - use {name}.nix (aleph-001, aleph-002 ALEPH-E005)",
        check: (code, filePath) => {
          // Normalize path
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          // Only check if filename is actually default.nix
          if (!normalizedPath.endsWith('/default.nix') && !normalizedPath.endsWith('\\default.nix')) {
            return true; // Not a default.nix file, skip check
          }
          // Allow default.nix in overlay directories (they're overlays, not packages)
          if (normalizedPath.includes('/overlays/')) return true;
          // Allow default.nix in flake directories (flake.nix is the entry point)
          if (normalizedPath.includes('/flake') && normalizedPath.endsWith('default.nix')) return true;
          // Otherwise, flag it
          return false;
        },
      },
      {
        pattern: /''[\s\S]*?''/,
        rule: "WSN-E006",
        message: "Heredocs forbidden - use writeText or file imports (aleph-001, aleph-002 ALEPH-E006)",
        exception: /(writeText|writeShellApplication|writeShellScript|shellHook|buildPhase|installPhase|checkPhase|configurePhase)/,
        check: (code, filePath) => {
          // Check if heredoc is in allowed context (writeText, writeShellScript, or stdenv phase)
          const heredocPattern = /''[\s\S]*?''/g;
          let match;
          const codeCopy = code; // Reset regex lastIndex
          while ((match = heredocPattern.exec(codeCopy)) !== null) {
            // Look backwards from match start to find allowed context
            const beforeMatch = code.substring(Math.max(0, match.index - 200), match.index);
            // Check if there's an allowed pattern before this heredoc
            // Pattern: writeText "name" '' or writeShellApplication '' or writeShellScript '' or shellHook = '' or buildPhase = ''
            const exceptionPattern = /(writeText|writeShellApplication|writeShellScript)\s*(?:"[^"]*"|\w+)?\s*''|(shellHook|buildPhase|installPhase|checkPhase|configurePhase|unpackPhase|patchPhase|fixupPhase|preConfigure|postConfigure|preBuild|postBuild|preInstall|postInstall|preCheck|postCheck)\s*=\s*''/;
            const hasException = exceptionPattern.test(beforeMatch + match[0]);
            if (!hasException) {
              return false; // Found heredoc not in exception context
            }
          }
          return true;
        },
      },
      {
        pattern: /\bif\s+.*\bthen\s+.*\belse\s+/,
        rule: "WSN-E007",
        message: "if/then/else in module config causes infinite recursion - use mkIf (aleph-001, aleph-002 ALEPH-E007)",
        context: "module",
        check: (code, filePath) => {
          // Don't flag if/then/else in string literals
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            // Skip comment lines
            if (line.trim().startsWith('#')) continue;
            
            // Check if if/then/else is in a string literal
            const stringPattern = /(["'])(?:(?=(\\?))\2.)*?\1/g;
            const stringRanges = [];
            let match;
            while ((match = stringPattern.exec(line)) !== null) {
              stringRanges.push({ start: match.index, end: match.index + match[0].length });
            }
            
            // Check for if/then/else pattern
            const ifPattern = /\bif\s+.*\bthen\s+.*\belse\s+/;
            const ifMatch = line.match(ifPattern);
            if (ifMatch) {
              const matchStart = ifMatch.index;
              const matchEnd = matchStart + ifMatch[0].length;
              // Check if match is inside a string literal
              const inString = stringRanges.some(range => matchStart >= range.start && matchEnd <= range.end);
              if (inString) continue; // Skip if/then/else in strings
              
              // Also check multi-line if/then/else (split across lines)
              // This is a simplified check - full multi-line would need more complex parsing
              return false; // Found if/then/else not in string
            }
          }
          return true;
        },
      },
      {
        pattern: /import\s*\(/,
        rule: "WSN-E008",
        message: "Import from derivation (IFD) forbidden - forces builds during evaluation (aleph-001, aleph-002 ALEPH-E008)",
        check: (code) => {
          // Check for import (derivation) pattern - IFD
          return !/import\s*\([^)]*(?:runCommand|mkDerivation|writeText|writeShellApplication|stdenv\.mkDerivation)/s.test(code);
        },
      },
      {
        pattern: /import\s+.*nixpkgs/,
        rule: "WSN-E010",
        message: "Per-flake nixpkgs config forbidden - use centralized straylight-naught config (aleph-001, aleph-002 ALEPH-E010)",
        check: (code) => {
          // Check for import inputs.nixpkgs { config... } pattern
          return !/import\s+.*nixpkgs\s*\{[^}]*config/s.test(code);
        },
      },
      {
        pattern: /nixpkgs\.config\.[a-zA-Z]/,
        rule: "WSN-E011",
        message: "nixpkgs.config.* assignment in NixOS config forbidden",
        context: "nixos",
      },
      {
        pattern: /\bcmake\b/i,
        rule: "STRAYLIGHT-003",
        message: "CMake is BANNED - use pkg-config or cmake-to-pc tool",
        exception: /(cmake-to-pc|cmakeFlags|cmake\.configure|cmake\.build)/,
        check: (code, filePath) => {
          // Check if cmake is in exception context
          // Exception patterns: cmakeFlags, cmake.configure, cmake.build, cmake-to-pc
          // Only match standalone "cmake" (not part of exception patterns)
          const lines = code.split('\n');
          const cmakePattern = /\bcmake\b/gi;
          
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            // Skip comment lines
            if (line.trim().startsWith('#')) continue;
            
            // Skip if cmake is in a string literal
            const stringPattern = /(["'])(?:(?=(\\?))\2.)*?\1/g;
            const stringRanges = [];
            let match;
            while ((match = stringPattern.exec(line)) !== null) {
              stringRanges.push({ start: match.index, end: match.index + match[0].length });
            }
            
            // Check for cmake in this line
            const codeCopy = line; // Reset regex
            let cmakeMatch;
            while ((cmakeMatch = cmakePattern.exec(codeCopy)) !== null) {
              const matchStart = cmakeMatch.index;
              const matchEnd = matchStart + cmakeMatch[0].length;
              
              // Check if match is inside a string literal
              const inString = stringRanges.some(range => matchStart >= range.start && matchEnd <= range.end);
              if (inString) continue; // Skip cmake in strings
              
              // Check if this "cmake" match is part of an exception pattern
              // Look at the text immediately after "cmake"
              const afterMatch = line.substring(matchEnd, Math.min(line.length, matchEnd + 15));
              
              // Check if "cmake" is followed by exception pattern characters
              // cmakeFlags: "cmake" followed by "Flags"
              // cmake.configure: "cmake" followed by ".configure"
              // cmake.build: "cmake" followed by ".build"
              // cmake-to-pc: "cmake" followed by "-to-pc"
              if (/^Flags|^\.configure|^\.build|^-to-pc/.test(afterMatch)) {
                continue; // Part of exception pattern, skip
              }
              
              // Also check before (for cases like "pkgs.cmakeFlags")
              const beforeMatch = line.substring(Math.max(0, matchStart - 10), matchStart);
              if (/Flags$|\.configure$|\.build$|-to-pc$/.test(beforeMatch)) {
                continue; // Part of exception pattern, skip
              }
              
              return false; // Found cmake not in exception context
            }
          }
          return true;
        },
      },
    ],
    warnings: [
      {
        pattern: /\bif\s+.*\bthen\s+.*\belse\s+/,
        rule: "WSN-W002",
        message: "if/then/else in module config - prefer mkIf",
        check: (code, filePath) => {
          // Check if it's in a module config block (has config = ...)
          // Match: config = if ... then ... else ... (multiline, allow newlines)
          const configMatch = /config\s*=\s*if\s+[\s\S]+?\bthen\s+[\s\S]+?\belse\s+/s.test(code);
          if (configMatch) {
            return false; // Found if/then/else in config
          }
          return true;
        },
      },
      {
        pattern: /''[\s\S]*?''/,
        rule: "WSN-W003",
        message: "Long inline string (>10 lines) - consider using writeText or file import",
        check: (code) => {
          // Check for multi-line strings exceeding 10 lines per RFC ℵ-002
          const matches = [...code.matchAll(/''([\s\S]*?)''/g)];
          for (const match of matches) {
            // Skip if it's in writeText/writeShellApplication context (exception)
            // Only allow camelCase function names (writeText), not lisp-case (write-text doesn't exist)
            const beforeMatch = code.substring(0, match.index);
            if (/(writeText|writeShellApplication|writeShellScript)/.test(beforeMatch)) {
              continue;
            }
            // Count lines in heredoc content (including empty lines)
            const content = match[1];
            const lines = content.split('\n').length;
            if (lines > 10) return false;
          }
          return true;
        },
      },
    ],
    required: [
      {
        pattern: /meta\s*=/,
        rule: "WSN-W004",
        message: "Packages should have 'meta' block",
        check: (code, filePath) => {
          // Only require meta for packages (mkDerivation), not modules
          if (!code.includes('mkDerivation')) return true;
          // Check for actual meta = pattern, not just the word "meta" in comments
          return /meta\s*=/.test(code);
        },
      },
      {
        pattern: /meta\s*=\s*\{[^}]*description/,
        rule: "WSN-W005",
        message: "meta should include 'description'",
        check: (code, filePath) => {
          // Only require description in meta for packages that have meta
          if (!code.includes('mkDerivation')) return true;
          if (!code.includes('meta')) return true; // WSN-W004 will catch missing meta
          // Check if meta block has description - need to handle nested braces
          const metaPattern = /meta\s*=\s*\{/g;
          let match;
          while ((match = metaPattern.exec(code)) !== null) {
            let braceCount = 1;
            let pos = match.index + match[0].length;
            let foundDescription = false;
            while (pos < code.length && braceCount > 0) {
              if (code[pos] === '{') braceCount++;
              else if (code[pos] === '}') braceCount--;
              else if (code.substring(pos, pos + 11) === 'description') {
                foundDescription = true;
              }
              pos++;
            }
            if (!foundDescription && braceCount === 0) {
              return false; // meta exists but no description
            }
          }
          return true;
        },
      },
      {
        pattern: /meta\s*=\s*\{[^}]*license/,
        rule: "WSN-W006",
        message: "meta should include 'license'",
        check: (code, filePath) => {
          // Only require license in meta for packages that have meta
          if (!code.includes('mkDerivation')) return true;
          if (!code.includes('meta')) return true; // WSN-W004 will catch missing meta
          // Check if meta block has license - need to handle nested braces
          const metaPattern = /meta\s*=\s*\{/g;
          let match;
          while ((match = metaPattern.exec(code)) !== null) {
            let braceCount = 1;
            let pos = match.index + match[0].length;
            let foundLicense = false;
            let foundDescription = false;
            while (pos < code.length && braceCount > 0) {
              if (code[pos] === '{') braceCount++;
              else if (code[pos] === '}') braceCount--;
              else {
                // Check if we're in a comment - skip comments
                const lineStart = code.lastIndexOf('\n', pos) + 1;
                const lineBeforePos = code.substring(lineStart, pos);
                if (!lineBeforePos.trim().startsWith('#')) {
                  const substr = code.substring(pos, pos + 12);
                  if (substr.startsWith('license')) foundLicense = true;
                  if (substr.startsWith('description')) foundDescription = true;
                }
              }
              pos++;
            }
            // Require license if description exists (package has meta)
            if (braceCount === 0 && foundDescription && !foundLicense) {
              return false; // meta exists with description but no license
            }
          }
          return true;
        },
      },
      {
        pattern: /meta\s*=\s*\{[^}]*mainProgram/,
        rule: "WSN-W007",
        message: "Packages with executables should include 'mainProgram' in meta",
        check: (code, filePath) => {
          // Check if package creates bin/ directory with executables
          // Only match explicit bin directory creation, not generic installPhase
          const hasBin = /(mkdir.*\$out\/bin|\$out\/bin\/|install.*-m755.*\$out\/bin|cp.*\$out\/bin)/.test(code);
          if (!hasBin) return true; // No executables, skip check

          if (/meta\s*=/.test(code)) {
            // Check if AT LEAST ONE meta block has mainProgram
            // (For flakes with multiple packages, at least the executable package should have it)
            const metaPattern = /meta\s*=\s*\{/g;
            let match;
            let anyHasMainProgram = false;
            while ((match = metaPattern.exec(code)) !== null) {
              let braceCount = 1;
              let pos = match.index + match[0].length;
              while (pos < code.length && braceCount > 0) {
                if (code[pos] === '{') braceCount++;
                else if (code[pos] === '}') braceCount--;
                else {
                  const lineStart = code.lastIndexOf('\n', pos) + 1;
                  const lineBeforePos = code.substring(lineStart, pos);
                  if (!lineBeforePos.trim().startsWith('#')) {
                    const substr = code.substring(pos, pos + 11);
                    if (substr === 'mainProgram') anyHasMainProgram = true;
                  }
                }
                pos++;
              }
            }
            if (!anyHasMainProgram) {
              return false; // Has executables but no mainProgram anywhere
            }
          }
          return true;
        },
      },
      {
        pattern: /mkDerivation\s*\(finalAttrs:/,
        rule: "WSN-E002-REQ",
        message: "Packages MUST use 'finalAttrs:' pattern",
        check: (code, filePath) => {
          if (/mkDerivation/.test(code)) {
            return /mkDerivation\s*\(finalAttrs:/.test(code);
          }
          return true;
        },
      },
      {
        pattern: /_class\s*=/,
        rule: "WSN-E004",
        message: "Non-flake modules must declare '_class' attribute (aleph-001, aleph-002 ALEPH-E004)",
        check: (code, filePath) => {
          // Normalize path
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          // Exclude index files (_index.nix) - they're just re-exports
          if (normalizedPath.includes('_index.nix')) return true;
          
          // Check if it's a module (has options/config, not mkDerivation)
          const hasOptions = /options\s*\./.test(code);
          const hasConfig = /config\s*\./.test(code);
          const hasMkDerivation = /mkDerivation/.test(code);
          const isModule = (hasOptions || hasConfig) && !hasMkDerivation;
          // Or check file path
          const isModulePath = normalizedPath.includes('/modules/') && (normalizedPath.includes('/nixos/') || normalizedPath.includes('/darwin/') || normalizedPath.includes('/home/'));
          if (isModule || isModulePath) {
            // Check for actual _class assignment, not just the word in comments
            const lines = code.split('\n');
            for (const line of lines) {
              if (line.trim().startsWith('#')) continue; // Skip comment lines
              if (/_class\s*=/.test(line)) return true;
            }
            return false; // Module but no _class assignment found
          }
          return true;
        },
      },
      {
        pattern: /mkOption\s*\{/,
        rule: "WSN-W005",
        message: "mkOption calls must include 'description' attribute",
        check: (code, filePath) => {
          // Find all mkOption calls - need to handle nested braces properly
          const mkOptionPattern = /mkOption\s*\{/g;
          let match;
          while ((match = mkOptionPattern.exec(code)) !== null) {
            // Find matching closing brace by counting braces
            let braceCount = 1;
            let pos = match.index + match[0].length;
            let blockStart = pos;
            
            while (pos < code.length && braceCount > 0) {
              if (code[pos] === '{') braceCount++;
              else if (code[pos] === '}') braceCount--;
              pos++;
            }
            
            // Extract the block content (between braces)
            const blockContent = code.substring(blockStart, pos - 1);
            
            // Check for description attribute (description = or description:)
            if (!/description\s*[=:]/.test(blockContent)) {
              return false; // Found mkOption without description
            }
          }
          return true;
        },
      },
    ],
  },
  bash: {
    required: [
      {
        pattern: /exec\s+["']?\$@["']?/,
        rule: "STRAYLIGHT-006-REQ",
        message: "Safe bash MUST end with 'exec \"$@\"' pattern",
        check: (code, filePath) => {
          const lines = code.split('\n').filter(l => l.trim() && !l.trim().startsWith('#'));
          // Check if any line contains both 'exec' and '"$@"' or "'$@'" anywhere on the line
          // This handles cases like: exec "$CXX" "${INCLUDE_ARGS[@]}" "$@"
          const hasExec = lines.some(l => {
            const hasExecKeyword = /\bexec\b/.test(l);
            const hasDollarAt = /["']?\$@["']?/.test(l);
            return hasExecKeyword && hasDollarAt;
          });
          if (!hasExec && lines.length > 0) {
            return false;
          }
          return true;
        },
      },
    ],
    forbidden: [
      {
        pattern: /\bif\s+\[/,
        rule: "STRAYLIGHT-006",
        message: "Bash logic forbidden - use Haskell script",
      },
      {
        pattern: /\bcase\s+\$/,
        rule: "STRAYLIGHT-006",
        message: "Bash logic forbidden - use Haskell script",
      },
      {
        pattern: /\bfor\s+\w+\s+in/,
        rule: "STRAYLIGHT-006",
        message: "Bash loops forbidden - use Haskell script",
      },
      {
        pattern: /\bwhile\s+\[/,
        rule: "STRAYLIGHT-006",
        message: "Bash loops forbidden - use Haskell script",
      },
      {
        pattern: /^\s*\w+\s*=/m,
        rule: "STRAYLIGHT-006",
        message: "Bash variable assignment forbidden - use Haskell",
        exception: /exec\s+["']?\$@["']?/,
      },
      {
        pattern: /\$\([^)]+\)/,
        rule: "STRAYLIGHT-006",
        message: "Command substitution forbidden - use Haskell",
        exception: /exec\s+["']?\$@["']?/,
      },
    ],
  },
  haskell: {
    required: [
      {
        pattern: /import\s+(Straylight|Aleph)\.Script/,
        rule: "STRAYLIGHT-004",
        message: "Scripts must import Straylight.Script or Aleph.Script (aleph-004)",
        check: (code, filePath) => {
          // Normalize file path separators
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          
          // Check if file has script-like structure (main :: IO () or similar)
          // Scripts have: main function, module Main, or executable entry point
          const hasScriptStructure = /\bmain\s*::\s*IO\s*\(\)/.test(code) || 
                                     /\bmain\s*::\s*IO\s+\w+/.test(code) ||
                                     /\bmain\s*=\s*/.test(code) ||
                                     /^module\s+Main/.test(code) ||
                                     /^module\s+Main\s+where/.test(code);
          
          // Check if it's a package file (has package-like module structure)
          // Package files have modules like Straylight.Nix.Packages.Something, not Main
          const isPackageFile = /module\s+\w+\.(Nix|Package|Packages|Packages\.\w+)/.test(code) ||
                                /module\s+Straylight\.Nix\./.test(code);
          
          // Only require for scripts - check if it's a script file (not in packages/, not a tool wrapper)
          const isScriptPath = normalizedPath.includes('/scripts/') && !normalizedPath.includes('/Tools/') && !normalizedPath.includes('/packages/');
          // Also check if it's a standalone script file (test files or any .hs/.purs file)
          // Include test-violations directory for test files
          const isStandaloneScript = /\.(hs|purs)$/.test(normalizedPath) && !normalizedPath.includes('/packages/') && !normalizedPath.includes('/src/') && (normalizedPath.includes('/test-violations/') || normalizedPath.includes('/scripts/'));
          
          // If it has script structure (module Main + main =), require import regardless of path
          //                                                                    // unless
          if (hasScriptStructure && !isPackageFile) {
            // Match actual import statements, not comments
            return /^import\s+Straylight\.Script/m.test(code);
          }
          
          // Legacy path-based check (for files without clear structure)
          if (isScriptPath || isStandaloneScript) {
            // Match actual import statements, not comments
            return /^import\s+Straylight\.Script/m.test(code);
          }
          
          return true;
        },
      },
    ],
    forbidden: [
      {
        pattern: /\bundefined\b/,
        rule: "STRAYLIGHT-007",
        message: "undefined forbidden - use Maybe/Option or explicit error handling",
        check: (code, filePath) => {
          // Normalize unicode to catch obfuscation attempts
          // Convert common unicode lookalikes to ASCII
          const normalized = code
            .replace(/[\u0430-\u044F]/g, (c) => {
              // Cyrillic lowercase to ASCII
              const map = { 'а': 'a', 'с': 'c', 'е': 'e', 'о': 'o', 'р': 'p', 'х': 'x', 'у': 'y' };
              return map[c] || c;
            })
            .replace(/[\u0410-\u042F]/g, (c) => {
              // Cyrillic uppercase to ASCII
              const map = { 'А': 'A', 'С': 'C', 'Е': 'E', 'О': 'O', 'Р': 'P', 'Х': 'X', 'У': 'Y' };
              return map[c] || c;
            });
          
          // Check for undefined in normalized code
          if (/\bundefined\b/.test(normalized)) {
            // Check if it's in a comment or string
            const lines = normalized.split('\n');
            for (let i = 0; i < lines.length; i++) {
              const line = lines[i];
              if (line.trim().startsWith('--') || line.trim().startsWith('//') || line.trim().startsWith('#')) continue;
              if (/["'].*\bundefined\b.*["']/.test(line)) continue;
              if (/\bundefined\b/.test(line)) {
                return false; // Found undefined
              }
            }
          }
          return true;
        },
      },
      {
        pattern: /\bnull\b/,
        rule: "STRAYLIGHT-007",
        message: "null forbidden - use Maybe/Option",
        check: (code, filePath) => {
          // In Haskell/PureScript, `null` is ALWAYS a function for checking empty collections
          // (from Prelude or qualified like V.null, Data.List.null)
          // It is NEVER a null value like in JavaScript/Java
          // Therefore, we allow ALL usage of null in Haskell/PureScript
          // The rule is primarily meant to catch null values in other languages
          return true; // Always valid in Haskell - null is a function
        },
      },
    ],
  },
  purescript: {
    required: [
      {
        pattern: /import\s+(Straylight|Aleph)\.Script/,
        rule: "STRAYLIGHT-004",
        message: "Scripts must import Straylight.Script or Aleph.Script (aleph-004)",
        check: (code, filePath) => {
          // Normalize file path separators
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          
          // Check if file has script-like structure (main :: Effect Unit or similar)
          // Scripts have: main function, module Main, or executable entry point
          const hasScriptStructure = /\bmain\s*::\s*Effect\s+Unit/.test(code) || 
                                     /\bmain\s*::\s*Effect\s+\w+/.test(code) ||
                                     /\bmain\s*=\s*/.test(code) ||
                                     /^module\s+Main/.test(code) ||
                                     /^module\s+Main\s+where/.test(code);
          
          // Check if it's a package file (has package-like module structure)
          // Package files have modules like Straylight.Nix.Packages.Something, not Main
          const isPackageFile = /module\s+\w+\.(Nix|Package|Packages|Packages\.\w+)/.test(code) ||
                                /module\s+Straylight\.Nix\./.test(code);
          
          // Only require for scripts - check if it's a script file (not in packages/, not a tool wrapper)
          const isScriptPath = normalizedPath.includes('/scripts/') && !normalizedPath.includes('/Tools/') && !normalizedPath.includes('/packages/');
          // Also check if it's a standalone script file (test files or any .hs/.purs file)
          // Include test-violations directory for test files
          const isStandaloneScript = /\.(hs|purs)$/.test(normalizedPath) && !normalizedPath.includes('/packages/') && !normalizedPath.includes('/src/') && (normalizedPath.includes('/test-violations/') || normalizedPath.includes('/scripts/'));
          
          // If it has script structure (module Main + main =), require import regardless of path
          //                                                                    // unless
          if (hasScriptStructure && !isPackageFile) {
            // Match actual import statements, not comments
            return /^import\s+Straylight\.Script/m.test(code);
          }
          
          // Legacy path-based check (for files without clear structure)
          if (isScriptPath || isStandaloneScript) {
            // Match actual import statements, not comments
            return /^import\s+Straylight\.Script/m.test(code);
          }
          
          return true;
        },
      },
    ],
    forbidden: [
      {
        pattern: /\bundefined\b/,
        rule: "STRAYLIGHT-007",
        message: "undefined forbidden - use Maybe/Option or explicit error handling",
      },
      {
        pattern: /\bnull\b/,
        rule: "STRAYLIGHT-007",
        message: "null forbidden - use Maybe/Option",
        check: (code, filePath) => {
          // In PureScript, `null` is a function for checking empty collections
          // It is not a null value like in JavaScript
          // Therefore, we allow usage of null in PureScript
          return true; // Always valid in PureScript - null is a function
        },
      },
      {
        pattern: /\bunsafeCoerce\b/,
        rule: "STRAYLIGHT-007",
        message: "unsafeCoerce forbidden - use proper type conversions",
      },
      {
        pattern: /\bunsafePartial\b/,
        rule: "STRAYLIGHT-007",
        message: "unsafePartial forbidden - handle all cases explicitly",
      },
      {
        pattern: /\bunsafePerformEffect\b/,
        rule: "STRAYLIGHT-007",
        message: "unsafePerformEffect forbidden - use Effect/Either properly",
      },
    ],
  },
  lean4: {
    forbidden: [
      {
        pattern: /\bsorry\b/,
        rule: "STRAYLIGHT-009",
        message: "sorry forbidden - proofs must be complete",
      },
      {
        pattern: /\baxiom\b/,
        rule: "STRAYLIGHT-009",
        message: "axiom forbidden without justification - use theorem with proof",
        exception: (code, match) => {
          const lines = code.split("\n");
          const beforeMatch = code.substring(0, match.index);
          const lineNum = beforeMatch.split("\n").length;
          if (lineNum < 2) return false;
          const prevLine = lines[lineNum - 2] ?? "";
          return /^\s*\/--/.test(prevLine) || /^\s*\/-!/.test(prevLine);
        },
      },
      {
        pattern: /\badmit\b/,
        rule: "STRAYLIGHT-009",
        message: "admit forbidden - proofs must be complete",
      },
      {
        pattern: /\bunsafe\b/,
        rule: "STRAYLIGHT-009",
        message: "unsafe operations forbidden - use safe alternatives",
      },
    ],
  },
  literate: {
    required: [
      {
        pattern: /@target:/,
        rule: "STRAYLIGHT-011-E001",
        message: "Code blocks must have @target annotation",
        check: (code, filePath) => {
          // Only validate literate programming files (.lit, .mdx, .lit.hs, .lit.cpp, .lit.purs)
          if (!filePath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          
          // Check for fenced code blocks with language identifiers
          const fencedBlocks = code.match(/```\w+[\s\S]*?```/g) || [];
          for (const block of fencedBlocks) {
            if (!/@target:/.test(block)) {
              return false;
            }
          }
          
          // Check for indented code blocks (4+ spaces, not in fenced block)
          const lines = code.split('\n');
          let inFencedBlock = false;
          let inIndentedBlock = false;
          let indentedBlockStart = -1;
          
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            
            // Track fenced blocks
            if (line.trim().startsWith('```')) {
              inFencedBlock = !inFencedBlock;
              if (!inFencedBlock) {
                // Exited fenced block, reset indented block tracking
                inIndentedBlock = false;
                indentedBlockStart = -1;
              }
              continue;
            }
            
            // Skip if inside fenced block
            if (inFencedBlock) continue;
            
            // Check for indented code block (4+ spaces, non-empty line)
            if (/^    [^\s]/.test(line)) {
              if (!inIndentedBlock) {
                // Starting new indented block
                inIndentedBlock = true;
                indentedBlockStart = i;
              }
            } else if (inIndentedBlock && line.trim() === '') {
              // Empty line in indented block - continue
              continue;
            } else if (inIndentedBlock && !/^    /.test(line)) {
              // End of indented block - check if it had annotations
              const blockLines = lines.slice(indentedBlockStart, i).join('\n');
              if (!/@target:/.test(blockLines) || !/@name:/.test(blockLines) || !/@description:/.test(blockLines)) {
                return false; // Indented block missing annotations
              }
              inIndentedBlock = false;
              indentedBlockStart = -1;
            }
          }
          
          // Check if we ended in an indented block
          if (inIndentedBlock) {
            const blockLines = lines.slice(indentedBlockStart).join('\n');
            if (!/@target:/.test(blockLines) || !/@name:/.test(blockLines) || !/@description:/.test(blockLines)) {
              return false; // Indented block missing annotations
            }
          }
          
          return true;
        },
      },
      {
        pattern: /@name:/,
        rule: "STRAYLIGHT-011-E001",
        message: "Code blocks must have @name annotation",
        check: (code, filePath) => {
          // Only validate literate programming files (.lit, .mdx, .lit.hs, .lit.cpp, .lit.purs)
          if (!filePath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          
          // Check for fenced code blocks
          const fencedBlocks = code.match(/```\w+[\s\S]*?```/g) || [];
          for (const block of fencedBlocks) {
            if (!/@name:/.test(block)) {
              return false;
            }
          }
          
          // Check for indented code blocks (same logic as @target check)
          const lines = code.split('\n');
          let inFencedBlock = false;
          let inIndentedBlock = false;
          let indentedBlockStart = -1;
          
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('```')) {
              inFencedBlock = !inFencedBlock;
              if (!inFencedBlock) {
                inIndentedBlock = false;
                indentedBlockStart = -1;
              }
              continue;
            }
            if (inFencedBlock) continue;
            
            if (/^    [^\s]/.test(line)) {
              if (!inIndentedBlock) {
                inIndentedBlock = true;
                indentedBlockStart = i;
              }
            } else if (inIndentedBlock && line.trim() === '') {
              continue;
            } else if (inIndentedBlock && !/^    /.test(line)) {
              const blockLines = lines.slice(indentedBlockStart, i).join('\n');
              if (!/@name:/.test(blockLines)) {
                return false;
              }
              inIndentedBlock = false;
              indentedBlockStart = -1;
            }
          }
          
          if (inIndentedBlock) {
            const blockLines = lines.slice(indentedBlockStart).join('\n');
            if (!/@name:/.test(blockLines)) {
              return false;
            }
          }
          
          return true;
        },
      },
      {
        pattern: /@description:/,
        rule: "STRAYLIGHT-011-E001",
        message: "Code blocks must have @description annotation",
        check: (code, filePath) => {
          // Only validate literate programming files (.lit, .mdx, .lit.hs, .lit.cpp, .lit.purs)
          if (!filePath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          
          // Check for fenced code blocks
          const fencedBlocks = code.match(/```\w+[\s\S]*?```/g) || [];
          for (const block of fencedBlocks) {
            if (!/@description:/.test(block)) {
              return false;
            }
          }
          
          // Check for indented code blocks (same logic as @target check)
          const lines = code.split('\n');
          let inFencedBlock = false;
          let inIndentedBlock = false;
          let indentedBlockStart = -1;
          
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('```')) {
              inFencedBlock = !inFencedBlock;
              if (!inFencedBlock) {
                inIndentedBlock = false;
                indentedBlockStart = -1;
              }
              continue;
            }
            if (inFencedBlock) continue;
            
            if (/^    [^\s]/.test(line)) {
              if (!inIndentedBlock) {
                inIndentedBlock = true;
                indentedBlockStart = i;
              }
            } else if (inIndentedBlock && line.trim() === '') {
              continue;
            } else if (inIndentedBlock && !/^    /.test(line)) {
              const blockLines = lines.slice(indentedBlockStart, i).join('\n');
              if (!/@description:/.test(blockLines)) {
                return false;
              }
              inIndentedBlock = false;
              indentedBlockStart = -1;
            }
          }
          
          if (inIndentedBlock) {
            const blockLines = lines.slice(indentedBlockStart).join('\n');
            if (!/@description:/.test(blockLines)) {
              return false;
            }
          }
          
          return true;
        },
      },
    ],
    forbidden: [
      {
        pattern: /@target:\s*(\w+)/g,
        rule: "STRAYLIGHT-011-E005",
        message: "Invalid @target value - must be one of: cpp23, tailwind4, daisyui, radix, vue, react",
        check: (code, filePath) => {
          // Only validate literate programming files
          if (!filePath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          const validTargets = ['cpp23', 'tailwind4', 'daisyui', 'radix', 'vue', 'react'];
          const matches = code.matchAll(/@target:\s*(\w+)/g);
          for (const match of matches) {
            if (match && match[1] && !validTargets.includes(match[1])) {
              return false; // Invalid target found
            }
          }
          return true;
        },
      },
      {
        pattern: /<<([\w-]+)>>/g,
        rule: "STRAYLIGHT-011-E003",
        message: "Undefined chunk reference",
        check: (code, filePath) => {
          // Only check literate programming files
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          if (!normalizedPath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          // Extract all chunk references <<name>> (allow hyphens)
          const refs = [...code.matchAll(/<<([\w-]+)>>/g)].map(m => m[1]);
          if (refs.length === 0) return true; // No references
          // Extract all chunk definitions @name: name (allow hyphens)
          const defs = [...code.matchAll(/@name:\s*([\w-]+)/g)].map(m => m[1]);
          // Check all refs exist in defs
          return refs.every(ref => defs.includes(ref));
        },
      },
      {
        pattern: /@name:\s*([\w-]+)/g,
        rule: "STRAYLIGHT-011-E002",
        message: "Duplicate chunk name",
        check: (code, filePath) => {
          // Only check literate programming files
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          if (!normalizedPath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          
          // Extract all chunk names (allow hyphens)
          const nameMatches = [...code.matchAll(/@name:\s*([\w-]+)/g)];
          const names = [];
          for (const match of nameMatches) {
            if (match && match[1]) names.push(match[1]);
          }
          
          // Check for duplicates
          const seen = new Set();
          for (const name of names) {
            if (!name) continue;
            if (seen.has(name)) return false;
            seen.add(name);
          }
          return true;
        },
      },
      {
        pattern: /@depends:/g,
        rule: "STRAYLIGHT-011-E004",
        message: "Circular chunk dependency detected",
        check: (code, filePath) => {
          // Only check literate programming files
          const normalizedPath = (filePath || '').replace(/\\/g, '/');
          if (!normalizedPath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          
          // Extract chunk dependencies: @name: name and @depends: [name1, name2]
          const chunks = new Map();
          const nameMatches = [...code.matchAll(/@name:\s*([\w-]+)/g)];
          
          // Build dependency graph - initialize all chunks
          for (const match of nameMatches) {
            const name = match[1];
            if (name) chunks.set(name, []);
          }
          
          // Add dependencies - find @name then @depends on following lines
          const lines = code.split('\n');
          let currentChunk = null;
          for (let i = 0; i < lines.length; i++) {
            const nameMatch = lines[i].match(/@name:\s*([\w-]+)/);
            if (nameMatch && nameMatch[1]) {
              currentChunk = nameMatch[1];
            }
            const depMatch = lines[i].match(/@depends:\s*\[([^\]]+)\]/);
            if (depMatch && depMatch[1] && currentChunk) {
              const deps = depMatch[1].split(',').map(d => d.trim().replace(/['"]/g, '')).filter(d => d.length > 0);
              if (deps.length > 0 && chunks.has(currentChunk)) {
                chunks.set(currentChunk, deps);
              }
            }
          }
          
          // Check for cycles using DFS
          const visited = new Set();
          const recStack = new Set();
          
          const hasCycle = (chunk) => {
            if (!chunk || !chunks.has(chunk)) return false;
            if (recStack.has(chunk)) return true; // Cycle detected
            if (visited.has(chunk)) return false; // Already processed
            
            visited.add(chunk);
            recStack.add(chunk);
            
            const deps = chunks.get(chunk) || [];
            for (const dep of deps) {
              if (dep && hasCycle(dep)) return true;
            }
            
            recStack.delete(chunk);
            return false;
          };
          
          for (const chunk of chunks.keys()) {
            if (!visited.has(chunk) && hasCycle(chunk)) {
              return false; // Cycle detected
            }
          }
          
          return true; // No cycles
        },
      },
      {
        pattern: /```[\s\S]*?```/g,
        rule: "STRAYLIGHT-010-BLOCK",
        message: "Code blocks must not exceed 500 lines",
        check: (code, filePath) => {
          // Only validate literate programming files
          if (!filePath.match(/\.(lit|mdx|lit\.hs|lit\.cpp|lit\.purs)$/)) return true;
          // Extract code blocks (content between ``` markers)
          // Find all code blocks by searching for ``` markers line by line
          const codeLines = code.split('\n');
          let inCodeBlock = false;
          let currentBlockLines = 0;
          
          for (let i = 0; i < codeLines.length; i++) {
            const line = codeLines[i];
            if (line.trim().startsWith('```')) {
              if (!inCodeBlock) {
                // Starting a new code block
                inCodeBlock = true;
                currentBlockLines = 0;
              } else {
                // Ending a code block
                if (currentBlockLines > 500) {
                  return false; // Code block exceeds 500 lines
                }
                inCodeBlock = false;
                currentBlockLines = 0;
              }
            } else if (inCodeBlock) {
              currentBlockLines++;
            }
          }
          
          // Check if we're still in a block at the end (malformed file)
          if (inCodeBlock && currentBlockLines > 500) {
            return false;
          }
          
          return true;
        },
      },
    ],
  },
  cpp23: {
    forbidden: [
      {
        pattern: /\bnullptr\b/,
        rule: "STRAYLIGHT-011-E006",
        message: "nullptr forbidden without explicit handling - use optional or smart pointers",
        check: (code, filePath) => {
          // Allow nullptr in CUDA files if explicitly handled (CUDA API requires it)
          const isCuda = filePath && (filePath.endsWith('.cu') || filePath.endsWith('.cuh'));
          if (isCuda) {
            // In CUDA, nullptr is acceptable for device pointer initialization
            // But should still be checked for proper handling
            return true; // Allow for now, could add stricter checks later
          }
          // For regular C++, check if nullptr is handled
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('//') || line.trim().startsWith('/*')) continue;
            if (/\bnullptr\b/.test(line)) {
              // Check if it's in a check/if statement or assignment with handling
              const hasHandling = /(if|assert|check|guard).*nullptr|nullptr.*\?/.test(code);
              if (!hasHandling) {
                return false; // Found nullptr without explicit handling
              }
            }
          }
          return true;
        },
      },
      {
        pattern: /\bnew\s+\w+/,
        rule: "STRAYLIGHT-011-E007",
        message: "Raw new forbidden - use smart pointers",
        check: (code, filePath) => {
          // Allow cudaMalloc in CUDA files (CUDA API)
          const isCuda = filePath && (filePath.endsWith('.cu') || filePath.endsWith('.cuh'));
          if (isCuda && /\bcudaMalloc\b/.test(code)) {
            return true; // CUDA memory allocation is acceptable
          }
          // Check for raw new
          if (/\bnew\s+\w+/.test(code)) {
            return false; // Found raw new
          }
          return true;
        },
      },
      {
        pattern: /\bdelete\s+/,
        rule: "STRAYLIGHT-011-E007",
        message: "Raw delete forbidden - use smart pointers",
        check: (code, filePath) => {
          // Allow cudaFree in CUDA files (CUDA API)
          const isCuda = filePath && (filePath.endsWith('.cu') || filePath.endsWith('.cuh'));
          if (isCuda && /\bcudaFree\b/.test(code)) {
            return true; // CUDA memory deallocation is acceptable
          }
          // Check for raw delete
          if (/\bdelete\s+/.test(code)) {
            return false; // Found raw delete
          }
          return true;
        },
      },
      {
        pattern: /\bcudaMalloc\b/,
        rule: "STRAYLIGHT-011-E008",
        message: "cudaMalloc must be paired with cudaFree or use RAII wrapper",
        check: (code, filePath) => {
          // Only check CUDA files
          if (!filePath || (!filePath.endsWith('.cu') && !filePath.endsWith('.cuh'))) {
            return true; // Not a CUDA file, skip
          }
          // Check if cudaMalloc is used
          if (!/\bcudaMalloc\b/.test(code)) {
            return true; // No cudaMalloc, skip
          }
          // Check if cudaFree is also present (basic check)
          const hasCudaFree = /\bcudaFree\b/.test(code);
          // Check if RAII wrapper is used (smart pointer or custom wrapper)
          const hasRAII = /(std::unique_ptr|std::shared_ptr|cuda_ptr|device_ptr)/.test(code);
          if (!hasCudaFree && !hasRAII) {
            return false; // cudaMalloc without cleanup
          }
          return true;
        },
      },
    ],
  },
  dhall: {
    forbidden: [
      {
        pattern: /builtins\.toNix/,
        rule: "STRAYLIGHT-012-E001",
        message: "builtins.toNix forbidden - use typed Dhall expressions instead",
      },
      {
        pattern: /env\s*=/,
        rule: "STRAYLIGHT-012-E002",
        message: "Raw env variables forbidden - use typed Input types",
        check: (code, filePath) => {
          // Allow env in comments or string literals
          // Allow env = when followed by type annotation (e.g., env = [] : List EnvVar)
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('--') || line.trim().startsWith('{-')) continue;
            if (/env\s*=/.test(line) && !line.includes('--') && !line.includes('{-')) {
              // Check if it's a typed initialization (has type annotation after =)
              if (/env\s*=\s*[^:]*\s*:\s*List/.test(line) || 
                  /env\s*=\s*[^:]*\s*:\s*Optional/.test(line) ||
                  /env\s*=\s*[^:]*\s*:\s*\w+\.EnvVar/.test(line)) {
                continue; // Typed initialization is allowed
              }
              return false; // Found raw env assignment
            }
          }
          return true;
        },
      },
    ],
    warnings: [
      {
        pattern: /let\s+\w+\s*=\s*\./,
        rule: "STRAYLIGHT-012-W001",
        message: "Relative imports - prefer absolute paths or package imports",
      },
    ],
  },
  bazel: {
    forbidden: [
      {
        pattern: /glob\(/,
        rule: "STRAYLIGHT-013-E001",
        message: "glob() forbidden - use explicit file lists per RFC ℵ-008",
      },
      {
        pattern: /prelude_/,
        rule: "STRAYLIGHT-013-E002",
        message: "prelude_ imports forbidden - use explicit typed toolchains",
      },
    ],
    warnings: [
      {
        pattern: /load\(/,
        rule: "STRAYLIGHT-013-W001",
        message: "Multiple load() statements - consider consolidating",
      },
    ],
  },
  rust: {
    forbidden: [
      {
        pattern: /\bunsafe\s+\{/,
        rule: "STRAYLIGHT-014-E001",
        message: "unsafe blocks forbidden - use safe alternatives",
        check: (code, filePath) => {
          // Allow unsafe in comments or string literals
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('//') || line.trim().startsWith('/*')) continue;
            if (/\bunsafe\s+\{/.test(line)) {
              return false; // Found unsafe block
            }
          }
          return true;
        },
      },
      {
        pattern: /\.unwrap\(\)/,
        rule: "STRAYLIGHT-014-E002",
        message: "unwrap() forbidden without explicit handling - use match, if let, or expect()",
        check: (code, filePath) => {
          // Allow unwrap in comments or test code
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('//') || line.trim().startsWith('/*')) continue;
            // Allow in test modules
            if (filePath && filePath.includes('/test') && filePath.includes('.rs')) {
              continue;
            }
            if (/\.unwrap\(\)/.test(line)) {
              return false; // Found unwrap()
            }
          }
          return true;
        },
      },
      {
        pattern: /\.unwrap_err\(\)/,
        rule: "STRAYLIGHT-014-E003",
        message: "unwrap_err() forbidden - use match or if let",
      },
      {
        pattern: /\.unwrap_or\(/,
        rule: "STRAYLIGHT-014-W001",
        message: "unwrap_or() - prefer match or if let for clarity",
      },
    ],
    required: [
      {
        pattern: /#\[derive\(/,
        rule: "STRAYLIGHT-014-REQ",
        message: "Structs should derive Debug, Clone, or other standard traits",
        check: (code, filePath) => {
          // Check if struct/enum definitions exist
          const hasStruct = /\bstruct\s+\w+/.test(code) || /\benum\s+\w+/.test(code);
          if (!hasStruct) return true; // No structs, skip check
          
          // Check if structs have derive attributes
          const structMatches = [...code.matchAll(/\bstruct\s+(\w+)/g)];
          for (const match of structMatches) {
            const structName = match[1];
            const beforeStruct = code.substring(0, match.index);
            // Check if derive is before this struct (within reasonable distance)
            const recentLines = beforeStruct.split('\n').slice(-5).join('\n');
            if (!/#\[derive\(/.test(recentLines)) {
              return false; // Struct without derive
            }
          }
          return true;
        },
      },
    ],
  },
  python: {
    forbidden: [
      {
        pattern: /\bNone\s*[=,)]/,
        rule: "STRAYLIGHT-015-E001",
        message: "None without explicit handling - use Optional type hints and explicit checks",
        check: (code, filePath) => {
          // Allow None in type hints (Optional[Type] = None)
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('#') || line.trim().startsWith('"""')) continue;
            // Allow in type hints: Optional[...] = None
            if (/Optional\[.*\]\s*=\s*None/.test(line)) continue;
            // Allow in comments
            if (/#.*None/.test(line)) continue;
            // Check for None assignments without Optional type hint
            if (/\bNone\s*[=,)]/.test(line) && !/Optional\[/.test(line)) {
              // Check if it's in a function signature with type hints
              const hasTypeHint = /:\s*Optional\[/.test(code.substring(0, code.indexOf(line)));
              if (!hasTypeHint) {
                return false; // Found None without Optional type hint
              }
            }
          }
          return true;
        },
      },
      {
        pattern: /#\s*type:\s*ignore/,
        rule: "STRAYLIGHT-015-E002",
        message: "type: ignore forbidden - fix type errors properly",
      },
      {
        pattern: /\bAny\b/,
        rule: "STRAYLIGHT-015-E003",
        message: "Any type forbidden - use specific types",
        check: (code, filePath) => {
          // Allow Any in comments or string literals
          const lines = code.split('\n');
          for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (line.trim().startsWith('#') || line.trim().startsWith('"""')) continue;
            // Allow in type hints only if it's typing.Any (imported)
            if (/from\s+typing\s+import.*Any/.test(code) && /\bAny\b/.test(line)) {
              // Check if it's actually used in a type hint
              if (/:\s*Any/.test(line) || /->\s*Any/.test(line)) {
                return false; // Found Any in type hint
              }
            }
            if (/\bAny\b/.test(line) && !/typing\.Any/.test(line)) {
              return false; // Found Any without typing prefix
            }
          }
          return true;
        },
      },
    ],
    required: [
      {
        pattern: /from\s+typing\s+import/,
        rule: "STRAYLIGHT-015-REQ",
        message: "Python files should use type hints",
        check: (code, filePath) => {
          // Check if file has functions/classes
          const hasFunctions = /\bdef\s+\w+/.test(code);
          const hasClasses = /\bclass\s+\w+/.test(code);
          if (!hasFunctions && !hasClasses) return true; // No functions/classes, skip
          
          // Check if typing is imported
          const hasTyping = /from\s+typing\s+import/.test(code) || /import\s+typing/.test(code);
          if (!hasTyping) {
            return false; // Has functions/classes but no typing imports
          }
          return true;
        },
      },
    ],
  },
  // Aleph-003: Prelude checks
  // Note: Prelude validation is primarily structural (using prelude functions)
  // This is enforced via code review and documentation, not pattern matching
  
  // Aleph-005: Nix Profiles checks
  // Note: Profile validation is primarily via flake structure
  // This is enforced via code review and documentation, not pattern matching
  
  // Aleph-007: Nix Formalization checks
  // Note: CA derivations and typed DSL validation requires infrastructure
  // This is enforced via code review and documentation, not pattern matching
  
  // Aleph-008: Continuity Project checks
  // Note: Dhall build language validation requires Dhall parser
  // This is enforced via code review and documentation, not pattern matching
};
