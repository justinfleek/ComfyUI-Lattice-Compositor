# 🚀 START HERE: Straylight Protocol Bootstrap

**Welcome! This folder contains everything you need to enforce the Straylight Protocol in your project.**

## Quick Setup (3 Steps)

### 1. Copy Files to Your Project

**Linux/Mac:**
```bash
cp -r BOOTSTRAP/* /path/to/your/project/
```

**Windows (PowerShell):**
```powershell
Copy-Item -Recurse -Force BOOTSTRAP\* C:\path\to\your\project\
```

### 2. Install Dependencies

```bash
cd /path/to/your/project
npm install
```

### 3. Set Up Git Hook

**Linux/Mac:**
```bash
chmod +x hooks/pre-commit
ln -sf ../../hooks/pre-commit .git/hooks/pre-commit
```

**Windows (PowerShell):**
```powershell
New-Item -ItemType SymbolicLink -Path .git\hooks\pre-commit -Target ..\..\hooks\pre-commit -Force
```

## Test It Works

```bash
echo 'with lib;' > test.nix
git add test.nix
git commit -m "test"  # Should be BLOCKED ✅
rm test.nix
```

## What You Get

✅ **Pre-commit Hook** - Blocks commits with violations  
✅ **CI Workflow** - Validates on PR/push (if using GitHub)  
✅ **MCP Server** - AI assistant integration (Claude Code, OpenCode)  
✅ **Cursor Rules** - IDE guidance (Cursor IDE)  
✅ **Validation Scripts** - Manual validation tools  
✅ **Agent Configs** - AI instructions (all platforms)  

## Next Steps

1. **Read [README.md](./README.md)** for complete documentation
2. **Check [CHECKLIST.md](./CHECKLIST.md)** to verify setup
3. **Review [ENFORCEMENT_FLOW.md](./ENFORCEMENT_FLOW.md)** to understand how enforcement works
4. **Configure your AI assistant:**
   - **Claude Code**: Run `npm run straylight:setup-claude` or see [.claude/README.md](./.claude/README.md)
   - **OpenCode**: Copy `opencode.json` to `~/.config/opencode/opencode.json`
   - **Cursor**: Rules are automatically loaded from `.cursor/rules/`

## Important Notes

- **Project Structure**: The system assumes an `straylight-core/` directory. If your project uses a different structure, see [PROJECT_STRUCTURE.md](./PROJECT_STRUCTURE.md)
- **Protocol Docs**: You need an `straylight-protocol/` folder with RFCs, OR the docs in `straylight-core/docs/rfc/`
- **Node.js**: Requires Node.js 18+ (check with `node --version`)

## Need Help?

- **Setup Issues**: See [README.md](./README.md) troubleshooting section
- **Understanding Flow**: See [ENFORCEMENT_FLOW.md](./ENFORCEMENT_FLOW.md)
- **Project Structure**: See [PROJECT_STRUCTURE.md](./PROJECT_STRUCTURE.md)

---

**🎉 You're ready to code with full Straylight Protocol enforcement!**
