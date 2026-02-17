#!/usr/bin/env node
/**
 * Straylight Protocol MCP Server
 * 
 * Provides tools for validating code against Straylight Protocol rules,
 * generating templates, locating files, and finding examples.
 */

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import * as fs from "fs/promises";
import * as path from "path";
import { fileURLToPath } from "url";
import { RULES, MAX_FILE_LINES } from "../scripts/rules.js";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// File location decision tree from CONTRIBUTING.md
// Tries to detect project structure: straylight-core/ or root-level nix/
function locateFile(type, name) {
  // Try to detect base path (check if straylight-core exists, otherwise use root)
  // This is a best-guess - users should verify with straylight_locate tool
  const basePath = "straylight-core"; // Default, but can be overridden per project
  
  switch (type) {
    case "package":
      return `${basePath}/nix/packages/${name}.hs`;
    case "c++-lib":
    case "libmodern":
      return `${basePath}/nix/overlays/libmodern/${name}.nix`;
    case "script":
      return `${basePath}/nix/scripts/${name}.hs`;
    case "tool-wrapper":
      const pascalName = name
        .split("-")
        .map((w) => w[0].toUpperCase() + w.slice(1))
        .join("");
      return `${basePath}/nix/scripts/Straylight/Script/Tools/${pascalName}.hs`;
    case "domain-module":
      const modulePascal = name
        .split("-")
        .map((w) => w[0].toUpperCase() + w.slice(1))
        .join("");
      return `${basePath}/nix/modules/${modulePascal}.nix`;
    default:
      return null;
  }
}

function validateFileSize(code, filePath) {
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
        fix: `Split file into multiple modules, each under ${MAX_FILE_LINES} lines`,
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
        // Check failed - find line number
        const match = rule.pattern.exec(code);
        const lineNum = match ? code.substring(0, match.index).split('\n').length : 0;
        errors.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    } else {
      // Simple pattern match
      const match = rule.pattern.exec(code);
      if (match) {
        // Check exception if present
        if (rule.exception && rule.exception.test(code)) {
          continue; // Exception matched, skip this violation
        }
        const lineNum = code.substring(0, match.index).split('\n').length;
        errors.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    }
  }

  // Check required patterns
  for (const rule of RULES[type].required || []) {
    if (rule.check) {
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    } else {
      const match = rule.pattern.test(code);
      if (!match) {
        errors.push({
          line: 0,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    }
  }

  // Check warnings
  const warnings = [];
  for (const rule of RULES[type].warnings || []) {
    if (rule.check) {
      const checkResult = rule.check.length === 2 
        ? rule.check(code, filePath)
        : rule.check(code);
      if (!checkResult) {
        const match = rule.pattern.exec(code);
        const lineNum = match ? code.substring(0, match.index).split('\n').length : 0;
        warnings.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    } else {
      const match = rule.pattern.exec(code);
      if (match) {
        if (rule.exception && rule.exception.test(code)) {
          continue;
        }
        const lineNum = code.substring(0, match.index).split('\n').length;
        warnings.push({
          line: lineNum,
          rule: rule.rule,
          message: rule.message,
          fix: rule.fix || '',
        });
      }
    }
  }

  return {
    valid: errors.length === 0,
    errors,
    warnings,
  };
}

// Templates
const TEMPLATES = {
  package: (name) => `{-# LANGUAGE OverloadedStrings #-}

-- | ${name} - Description
module Pkg where

import Straylight.Nix.Package

pkg :: Drv
pkg =
    mkDerivation
        [ pname "${name}"
        , version "1.0.0"
        , src $
            fetchFromGitHub
                [ owner "owner"
                , repo "${name}"
                , rev "v1.0.0"
                , hash "sha256-..."
                ]
        , nativeBuildInputs ["make"]
        , description "Description of ${name}"
        , homepage "https://example.com/${name}"
        , license "mit"
        ]
`,

  script: (name) => `{-# LANGUAGE OverloadedStrings #-}

{- |
${name} - Description

Usage: ${name} [ARGS...]
-}
module Main where

import Straylight.Script hiding (FilePath)
import System.Environment (getArgs)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> script $ do
            echoErr "Usage: ${name} [ARGS...]"
            exit 1
        _ -> script $ do
            echoErr ":: Running ${name}"
            -- Your script logic here
`,

  "tool-wrapper": (name) => {
    const pascalName = name
      .split("-")
      .map((w) => w[0].toUpperCase() + w.slice(1))
      .join("");
    return `{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Straylight.Script.Tools.${pascalName}
Description : Typed wrapper for ${name}

@
import Straylight.Script
import qualified Straylight.Script.Tools.${pascalName} as ${pascalName}

main = script $ do
  ${pascalName}.run ${pascalName}.defaults [] ["."]
@
-}
module Straylight.Script.Tools.${pascalName} (
    -- * Options
    Options (..),
    defaults,

    -- * Invocation
    run,
    run_,
) where

import Straylight.Script hiding (FilePath)
import qualified Data.Text as T

{- | ${name} options

Use 'defaults' and override fields as needed:
> defaults { verbose = True }
-}
data Options = Options
    { verbose :: Bool
    -- ^ --verbose: Verbose output
    } deriving (Show, Eq)

defaults :: Options
defaults = Options
    { verbose = False
    }

-- | Run ${name} with options and paths
run :: Options -> [Text] -> [FilePath] -> Sh Text
run opts args paths = do
    let allArgs = if verbose opts then ["--verbose"] else []
    S.run "${name}" (allArgs <> args <> map S.toTextIgnore paths)

-- | Run ${name} without capturing output
run_ :: Options -> [Text] -> [FilePath] -> Sh ()
run_ opts args paths = do
    let allArgs = if verbose opts then ["--verbose"] else []
    S.run_ "${name}" (allArgs <> args <> map S.toTextIgnore paths)
`;
  },

  "bash-wrapper": (name) => `# Safe bash wrapper - only exec allowed
exec ${name} "$@"
`,

  "flake-module": (name) => `# nix/modules/flake/${name}.nix
_:
{ config, lib, ... }:
let
  cfg = config.straylight-naught.${name};
in
{
  _class = "flake";

  options.straylight-naught.${name} = {
    enable = lib.mkEnableOption "straylight-naught ${name}";
  };

  config = lib.mkIf cfg.enable {
    # Your module configuration here
  };
}
`,

  "nixos-module": (name) => `# nix/modules/nixos/${name}.nix
{ config, lib, ... }:
let
  cfg = config.straylight-naught.${name};
in
{
  _class = "nixos";

  options.straylight-naught.${name} = {
    enable = lib.mkEnableOption "straylight-naught ${name}";
  };

  config = lib.mkIf cfg.enable {
    # Your NixOS configuration here
  };
}
`,
};

// Example discovery
function findExamples(type) {
  const examples = {
    "tool-wrapper": [
      "straylight-core/nix/scripts/Straylight/Script/Tools/Rg.hs",
      "straylight-core/nix/scripts/Straylight/Script/Tools/Tar.hs",
      "straylight-core/nix/scripts/Straylight/Script/Tools/Jq.hs",
      "straylight-core/nix/scripts/Straylight/Script/Tools/Bwrap.hs",
    ],
    script: [
      "straylight-core/nix/scripts/oci-run.hs",
      "straylight-core/nix/scripts/vfio-bind.hs",
      "straylight-core/nix/scripts/gpu-run.hs",
      "straylight-core/nix/scripts/ch-run.hs",
    ],
    package: [
      "straylight-core/nix/packages/fmt.hs",
      "straylight-core/nix/packages/catch2.hs",
      "straylight-core/nix/packages/spdlog.hs",
      "straylight-core/nix/packages/zlib-ng.hs",
    ],
    "flake-module": [
      "straylight-core/nix/modules/flake/lint.nix",
      "straylight-core/nix/modules/flake/devshell.nix",
    ],
    "c++-lib": [
      "straylight-core/nix/overlays/libmodern/fmt.nix",
    ],
    "libmodern": [
      "straylight-core/nix/overlays/libmodern/fmt.nix",
    ],
  };
  return examples[type] || [];
}

// Plan generation
function generatePlan(task) {
  const lowerTask = task.toLowerCase();
  const docs = [];
  const examples = [];
  let location = null;
  let templateType = null;

  if (lowerTask.includes("package") || lowerTask.includes("derivation")) {
    docs.push("straylight-core/docs/rfc/straylight-001-standard-nix.md");
    docs.push("straylight-core/docs/guides/write-package.md");
    examples.push(...findExamples("package"));
    location = locateFile("package", "my-package");
    templateType = "package";
  } else if (lowerTask.includes("script") || lowerTask.includes("haskell")) {
    docs.push("straylight-core/docs/rfc/straylight-004-typed-unix.md");
    docs.push("straylight-core/docs/skills/straylight-script/SKILL.md");
    docs.push("straylight-core/docs/guides/write-script.md");
    examples.push(...findExamples("script"));
    location = locateFile("script", "my-script");
    templateType = "script";
  } else if (lowerTask.includes("tool") && lowerTask.includes("wrapper")) {
    docs.push("straylight-core/docs/rfc/straylight-004-typed-unix.md");
    examples.push(...findExamples("tool-wrapper"));
    location = locateFile("tool-wrapper", "my-tool");
    templateType = "tool-wrapper";
  } else if (lowerTask.includes("bash")) {
    docs.push("straylight-core/docs/rfc/straylight-006-safe-bash.md");
    location = locateFile("script", "my-wrapper");
    templateType = "bash-wrapper";
  } else if (lowerTask.includes("module") && lowerTask.includes("flake")) {
    docs.push("straylight-core/docs/rfc/straylight-001-standard-nix.md");
    examples.push(...findExamples("flake-module"));
    location = locateFile("flake-module", "my-module");
    templateType = "flake-module";
  } else if (lowerTask.includes("nixos")) {
    docs.push("straylight-core/docs/rfc/straylight-001-standard-nix.md");
    location = locateFile("nixos-module", "my-module");
    templateType = "nixos-module";
  } else {
    docs.push("straylight-core/CONTRIBUTING.md");
    docs.push("straylight-core/docs/rfc/straylight-001-standard-nix.md");
  }

  return { docs, examples, location, templateType };
}

// MCP Server setup
const server = new Server(
  {
    name: "straylight-protocol",
    version: "1.0.0",
  },
  {
    capabilities: {
      tools: {},
    },
  }
);

// List tools
server.setRequestHandler(ListToolsRequestSchema, async () => ({
  tools: [
    {
      name: "straylight_validate",
      description: "Validate code against Straylight Protocol rules",
      inputSchema: {
        type: "object",
        properties: {
          code: { type: "string", description: "Code to validate" },
          type: {
            type: "string",
            enum: ["nix", "bash", "haskell", "purescript", "lean4", "literate", "cpp23", "dhall", "bazel", "rust", "python"],
            description: "Code type",
          },
          filePath: { type: "string", description: "Optional file path for context-aware validation" },
        },
        required: ["code", "type"],
      },
    },
    {
      name: "straylight_template",
      description: "Generate starter code template",
      inputSchema: {
        type: "object",
        properties: {
          type: {
            type: "string",
            enum: [
              "package",
              "script",
              "tool-wrapper",
              "bash-wrapper",
              "flake-module",
              "nixos-module",
            ],
            description: "Template type",
          },
          name: { type: "string", description: "Name for the template" },
        },
        required: ["type", "name"],
      },
    },
    {
      name: "straylight_locate",
      description: "Determine correct file location",
      inputSchema: {
        type: "object",
        properties: {
          type: {
            type: "string",
            description: "File type (package, script, tool-wrapper, etc.)",
          },
          name: { type: "string", description: "File name" },
        },
        required: ["type", "name"],
      },
    },
    {
      name: "straylight_plan",
      description: "Get documentation and examples for a task",
      inputSchema: {
        type: "object",
        properties: {
          task: { type: "string", description: "Task description" },
        },
        required: ["task"],
      },
    },
    {
      name: "straylight_read",
      description: "Read file from straylight-core with automatic chunking for large files",
      inputSchema: {
        type: "object",
        properties: {
          path: { type: "string", description: "File path relative to project root" },
        },
        required: ["path"],
      },
    },
    {
      name: "straylight_examples",
      description: "Find reference implementation examples",
      inputSchema: {
        type: "object",
        properties: {
          type: {
            type: "string",
            description: "Example type (package, script, tool-wrapper, etc.)",
          },
        },
        required: ["type"],
      },
    },
    {
      name: "straylight_search",
      description: "Search codebase for patterns",
      inputSchema: {
        type: "object",
        properties: {
          pattern: { type: "string", description: "Search pattern" },
        },
        required: ["pattern"],
      },
    },
  ],
}));

// Handle tool calls
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  try {
    switch (name) {
      case "straylight_validate": {
        try {
          const filePath = args.filePath || '';
          const result = validateCode(args.code, args.type, filePath);
          
          // Format response for better readability
          if (result.valid) {
            return {
              content: [
                {
                  type: "text",
                  text: JSON.stringify({
                    valid: true,
                    warningCount: (result.warnings || []).length,
                    warnings: result.warnings || [],
                    message: result.warnings && result.warnings.length > 0
                      ? `Code passes validation with ${result.warnings.length} warning(s). Review warnings.`
                      : "Code passes Straylight Protocol validation",
                  }, null, 2),
                },
              ],
            };
          } else {
            const errorSummary = result.errors
              .map((e) => `Line ${e.line}: [${e.rule}] ${e.message}`)
              .join('\n');
            const warningSummary = (result.warnings || [])
              .map((w) => `Line ${w.line}: [${w.rule}] ⚠️ ${w.message}`)
              .join('\n');
            
            return {
              content: [
                {
                  type: "text",
                  text: JSON.stringify({
                    valid: false,
                    errorCount: result.errors.length,
                    warningCount: (result.warnings || []).length,
                    errors: result.errors,
                    warnings: result.warnings || [],
                    summary: errorSummary,
                    warningSummary: warningSummary,
                    message: `Code has ${result.errors.length} error(s) and ${(result.warnings || []).length} warning(s). Fix errors before writing.`,
                  }, null, 2),
                },
              ],
            };
          }
        } catch (error) {
          return {
            content: [
              {
                type: "text",
                text: JSON.stringify({
                  valid: false,
                  error: `Validation error: ${error.message}`,
                }, null, 2),
              },
            ],
            isError: true,
          };
        }
      }

      case "straylight_template": {
        const template = TEMPLATES[args.type];
        if (!template) {
          return {
            content: [
              {
                type: "text",
                text: `Unknown template type: ${args.type}`,
              },
            ],
            isError: true,
          };
        }
        const code = template(args.name);
        return {
          content: [
            {
              type: "text",
              text: code,
            },
          ],
        };
      }

      case "straylight_locate": {
        const location = locateFile(args.type, args.name);
        return {
          content: [
            {
              type: "text",
              text: location || `Unknown type: ${args.type}`,
            },
          ],
        };
      }

      case "straylight_plan": {
        const plan = generatePlan(args.task);
        return {
          content: [
            {
              type: "text",
              text: JSON.stringify(plan, null, 2),
            },
          ],
        };
      }

      case "straylight_examples": {
        const examples = findExamples(args.type);
        return {
          content: [
            {
              type: "text",
              text: JSON.stringify(examples, null, 2),
            },
          ],
        };
      }

      case "straylight_search": {
        // Simple search - in production would use ripgrep or similar
        return {
          content: [
            {
              type: "text",
              text: `Search for "${args.pattern}" - use grep/ripgrep in your terminal`,
            },
          ],
        };
      }

      case "straylight_read": {
        // Read file with chunking support for files >500 lines
        try {
          const filePath = path.resolve(__dirname, '..', args.path);
          const content = await fs.readFile(filePath, 'utf-8');
          const lines = content.split('\n');
          
          if (lines.length > MAX_FILE_LINES) {
            // Return file info and offer chunked reading
            const chunks = [];
            for (let i = 0; i < lines.length; i += MAX_FILE_LINES) {
              chunks.push({
                start: i + 1,
                end: Math.min(i + MAX_FILE_LINES, lines.length),
                lines: lines.slice(i, i + MAX_FILE_LINES).join('\n'),
              });
            }
            
            return {
              content: [
                {
                  type: "text",
                  text: JSON.stringify({
                    path: args.path,
                    totalLines: lines.length,
                    chunks: chunks.length,
                    warning: `File exceeds ${MAX_FILE_LINES} lines. Reading in ${chunks.length} chunks.`,
                    chunk1: chunks[0].lines,
                    allChunks: chunks.map((c, i) => ({
                      chunk: i + 1,
                      startLine: c.start,
                      endLine: c.end,
                      content: c.lines,
                    })),
                  }, null, 2),
                },
              ],
            };
          }
          
          return {
            content: [
              {
                type: "text",
                text: content,
              },
            ],
          };
        } catch (error) {
          return {
            content: [
              {
                type: "text",
                text: JSON.stringify({
                  error: `Failed to read file: ${error.message}`,
                  path: args.path,
                }, null, 2),
              },
            ],
            isError: true,
          };
        }
      }

      default:
        return {
          content: [
            {
              type: "text",
              text: `Unknown tool: ${name}`,
            },
          ],
          isError: true,
        };
    }
  } catch (error) {
    return {
      content: [
        {
          type: "text",
          text: `Error: ${error.message}`,
        },
      ],
      isError: true,
    };
  }
});

// Start server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error("Straylight Protocol MCP server running on stdio");
}

main().catch(console.error);
