# Skills Configuration Guide

## Overview

Skills are configured for three platforms:
- **Cursor**: `.cursor/skills/` (project-level)
- **OpenCode**: `.opencode/skills/` and `.claude/skills/` (project-level)
- **Claude Code**: `.claude/skills/` (project-level) + MCP integration

## Skill Locations

### Current Setup
All skills are copied to:
- ✅ `.cursor/skills/` - For Cursor IDE
- ✅ `.opencode/skills/` - For OpenCode (primary)
- ✅ `.claude/skills/` - For OpenCode (fallback) and Claude Code

### Source Location
Original skills are in `skills/` (root directory) - this is the source of truth.

## Automatic Triggers

### OpenCode
Configured in `opencode.json` via `permission.skill` patterns:

```json
{
  "permission": {
    "skill": {
      "*": "allow",                    // All skills allowed by default
      "creative-coder": "ask",         // Requires user approval
      "council": "allow"               // Explicitly allowed
    }
  }
}
```

**Permission Levels:**
- `allow` - Skill loads immediately when keywords match
- `deny` - Skill hidden, access rejected
- `ask` - User prompted for approval before loading

**How It Works:**
- OpenCode analyzes user messages for keywords matching skill descriptions
- If keywords match AND permission is `allow`, skill activates automatically
- Skills with `compatibility: opencode` in frontmatter are prioritized

### Claude Code
**No reliable automatic activation** - skills must be:
1. **Explicitly mentioned** by name in user message
2. **Referenced in CLAUDE.md** to establish patterns
3. **Triggered via custom hooks** (most reliable)

**Manual Triggers:**
- `council` skill: User message starts with "Council:"
- Other skills: Mention skill name explicitly ("use deterministic-coder", "apply expert-researcher")

### Cursor
**Automatic discovery** based on:
- Skill description keywords matching user intent
- File patterns in skill frontmatter (`globs`)
- `alwaysApply: true` flag in frontmatter

## Available Skills

| Skill | OpenCode | Claude Code | Cursor | Auto-Trigger |
|-------|----------|-------------|--------|--------------|
| `straylight-script` | ✅ | ✅ | ✅ | Keywords: "script", "bash", "shell" |
| `deterministic-coder` | ✅ | ✅ | ✅ | Keywords: "fix", "bug", "refactor", "implement" |
| `expert-researcher` | ✅ | ✅ | ✅ | Keywords: "research", "investigate", "verify" |
| `thorough-reading` | ✅ | ✅ | ✅ | Keywords: "read", "analyze", "review" |
| `verification` | ✅ | ✅ | ✅ | Keywords: "verify", "validate", "check" |
| `testing-methodology` | ✅ | ✅ | ✅ | Keywords: "test", "testing", "test suite" |
| `safe-refactoring` | ✅ | ✅ | ✅ | Keywords: "refactor", "refactoring" |
| `type-cleanup` | ✅ | ✅ | ✅ | Keywords: "type", "types", "typing" |
| `exploratory-architect` | ✅ | ✅ | ✅ | Keywords: "architecture", "design", "plan" |
| `creative-coder` | ⚠️ (ask) | ✅ | ✅ | Manual: "creative", "unconventional" |
| `council` | ✅ | ✅ | ✅ | Manual: "Council:" prefix |

## Skill Activation Examples

### OpenCode (Automatic)
```
User: "Fix the bug in the validation logic"
→ deterministic-coder activates automatically (keywords match + permission: allow)
```

### Claude Code (Manual)
```
User: "Council: How should we structure the testing strategy?"
→ council skill activates (explicit trigger)
```

### Cursor (Automatic)
```
User: "Read the entire file and trace dependencies"
→ thorough-reading activates (keywords match description)
```

## Configuration Files

### `opencode.json`
- Configures MCP servers
- Sets skill permissions
- Defines instructions

### `.claude/settings.json`
- Configures MCP servers for Claude Code
- No skill configuration (skills auto-discovered from `.claude/skills/`)

### `.cursor/rules/*.mdc`
- Cursor-specific rules
- Can reference skills in instructions

## Troubleshooting

### Skills Not Activating in OpenCode
1. Check `opencode.json` permissions
2. Verify skill has `compatibility: opencode` in frontmatter
3. Ensure skill is in `.opencode/skills/` or `.claude/skills/`
4. Check skill description includes relevant keywords

### Skills Not Activating in Claude Code
1. Skills don't auto-activate reliably
2. Explicitly mention skill name in request
3. Reference skills in `CLAUDE.md` for pattern recognition
4. Consider custom hooks for deterministic activation

### Skills Not Activating in Cursor
1. Verify skill is in `.cursor/skills/`
2. Check skill frontmatter has proper `description` with keywords
3. Ensure `globs` patterns match files being worked on
4. Check `alwaysApply: true` if skill should always be active

## Maintenance

When adding new skills:
1. Add to `skills/` (source of truth)
2. Run `node scripts/sync-skills.js` to sync to all locations
3. Update `opencode.json` permissions if needed
4. Update this document

### Sync Script

The `scripts/sync-skills.js` script automatically:
- Validates all skills (frontmatter, naming, format)
- Syncs from `skills/` to `.cursor/skills/`, `.opencode/skills/`, `.claude/skills/`
- Ensures consistency across all platforms

**Usage:**
```bash
# Sync all skills
node scripts/sync-skills.js

# Validate only (no sync)
node scripts/sync-skills.js --validate-only
```

### Testing Skill Activation

Test keyword matching for skills:
```bash
# Test all skills
node scripts/test-skill-activation.js

# Test specific skill
node scripts/test-skill-activation.js straylight-script
```
