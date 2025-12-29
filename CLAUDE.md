# CLAUDE.md — SECURITY AUDIT PROTOCOL v4.0

## PROJECT OVERVIEW
Motion graphics compositor as ComfyUI custom node pack.
- **Open Source**: Node pack for creating AI video control signals
- **Pro**: Standalone product with LLM, locked nodes, Weyl API integration

## PHASE 1 STATUS: ✅ COMPLETE (TypeScript/Frontend)

| Control | File | Tests |
|---------|------|-------|
| Expression Sandbox | services/expressions/sesEvaluator.ts | 86/86 |
| URL Validation | services/security/urlValidator.ts | 37 |
| JSON Sanitization | services/security/jsonSanitizer.ts | 37 |

## PHASE 2 STATUS: 🔴 IN PROGRESS (Python Backend)

### Python Files to Audit (21 total)

#### /nodes/ (Priority - these are the ComfyUI nodes)
| File | Status | Risk |
|------|--------|------|
| controlnet_preprocessors.py | ⬜ PENDING | HIGH |
| lattice_layer_decomposition.py | ⬜ PENDING | HIGH |
| compositor_node.py | ⬜ PENDING | MEDIUM |
| lattice_api_proxy.py | ⬜ PENDING | MEDIUM |
| lattice_frame_interpolation.py | ⬜ PENDING | MEDIUM |
| lattice_stem_separation.py | ⬜ PENDING | MEDIUM |
| lattice_vectorize.py | ⬜ PENDING | MEDIUM |
| __init__.py | ⬜ PENDING | LOW |

#### /scripts/ (Lower priority - test utilities)
| File | Status |
|------|--------|
| decomp_local.py | ⬜ PENDING |
| decomp_run.py | ⬜ PENDING |
| run_decomposition_gpu.py | ⬜ PENDING |
| run_decomp_comfyui.py | ⬜ PENDING |
| run_decomp_now.py | ⬜ PENDING |
| test_*.py (6 files) | ⬜ PENDING |

---

## DANGEROUS PATTERNS TO FIND

### CRITICAL (must fix immediately)
```python
trust_remote_code=True      # Executes arbitrary Python from model repo
exec(user_input)            # Direct code execution
eval(user_input)            # Direct code execution
```

### HIGH (fix or justify)
```python
pickle.load(f)              # Can execute arbitrary code
torch.load(path)            # Uses pickle internally
subprocess.call(user_input) # Command injection
os.system(user_input)       # Command injection
```

### SAFE ALTERNATIVES
```python
# Instead of trust_remote_code=True
trust_remote_code=False

# Instead of torch.load
from safetensors.torch import load_file
weights = load_file(path)

# Instead of pickle
import json
data = json.load(f)
```

---

## AUDIT PROCESS

### For each Python file:
1. Read entire file
2. Search for dangerous patterns
3. Document in AUDIT/PYTHON_FINDINGS.md:
   - File path
   - Line numbers with issues
   - What the code does
   - Risk level
   - Recommended fix
4. Fix critical issues immediately
5. Mark file as AUDITED in this doc

### Findings format:
```markdown
## [filename] - [RISK LEVEL]

**Lines with issues:** X, Y, Z

**Issue 1:** Line X - trust_remote_code=True
- Context: Loading HuggingFace model
- Risk: Arbitrary code execution
- Fix: Set to False, verify model works

**Issue 2:** ...
```

---

## MODEL REGISTRY SYSTEM (After Python Audit)

### Goal
Secure model downloading with hash verification.

### Components
1. `modelRegistry.json` - Approved models with SHA256
2. `modelDownloader.py` - Download + verify from HuggingFace
3. ComfyUI integration - Proper folder placement

### Registry format:
```json
{
  "models": {
    "depth-anything-v3": {
      "repo": "depth-anything/Depth-Anything-V2-Large",
      "files": ["model.safetensors"],
      "sha256": "abc123...",
      "comfyui_path": "models/depth"
    }
  }
}
```

---

## FILES (COMMIT STATUS)

| File | Git Status | Notes |
|------|------------|-------|
| CLAUDE.md | ✅ Commit | Public audit protocol |
| INVENTORY.md | ✅ Commit | No secrets |
| SECURITY_ARCHITECTURE.md | ❌ LOCAL ONLY | Contains vulnerability map |
| AUDIT/*.md | ✅ Commit | Findings only, not exploitation details |

---

## ABSOLUTE RULES

1. **NEVER commit SECURITY_ARCHITECTURE.md** - scrub if accidentally pushed
2. **Document before fixing** - create audit trail
3. **One file at a time** - thorough analysis
4. **Prefer safetensors** - no pickle execution risk
5. **No trust_remote_code=True** - ever
6. **Validate all node inputs** - ComfyUI nodes receive user data

---

## AFTER PYTHON AUDIT: Remaining Work

| Priority | Task | Phase |
|----------|------|-------|
| 1 | Nested composition depth limits | TypeScript |
| 2 | Model registry + secure downloader | Python |
| 3 | Template signing (official templates) | Both |
| 4 | LLM boundaries (Pro only) | Future |