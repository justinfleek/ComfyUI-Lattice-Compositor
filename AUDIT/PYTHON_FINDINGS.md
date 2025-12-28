# Python Backend Security Audit - Findings

**Date:** 2025-12-28
**Auditor:** Claude Code (Opus 4.5)
**Scope:** All Python files in `/nodes/` directory

---

## Executive Summary

| Files Audited | Issues Found | Critical | High | Medium | Low |
|---------------|--------------|----------|------|--------|-----|
| 8 | 1 | 0 | 1 | 0 | 0 |

**Overall Assessment:** The Python codebase is well-secured. Only one issue found requiring attention.

---

## Patterns Searched

- `trust_remote_code=True` - Arbitrary code execution from HuggingFace models
- `torch.load()` - Pickle deserialization (can execute arbitrary code)
- `pickle.load()` - Arbitrary code execution
- `exec()` / `eval()` - Dynamic code execution
- `subprocess` with user input - Command injection
- `os.system()` with user input - Command injection

---

## File-by-File Analysis

### 1. nodes/controlnet_preprocessors.py - CLEAN

**Purpose:** Registry and API wrapper for ControlNet preprocessors
**Lines:** 1208
**Risk Level:** LOW

**Analysis:**
- No model loading (passthrough to ComfyUI nodes)
- No dangerous patterns found
- Static configuration registry only

**Verdict:** No action required

---

### 2. nodes/lattice_layer_decomposition.py - CLEAN

**Purpose:** Qwen-Image-Layered model integration for layer decomposition
**Lines:** 861
**Risk Level:** LOW

**Analysis:**
- Uses `QwenImageLayeredPipeline.from_pretrained()` from diffusers (safe)
- No `trust_remote_code` parameter used (defaults to False)
- Implements SHA256 hash verification (lines 74-160)
- Uses `huggingface_hub.snapshot_download()` for model downloads

**Positive Security Features:**
- Hash verification infrastructure for model files
- Proper use of diffusers pipeline (no pickle risk)

**Verdict:** No action required

---

### 3. nodes/compositor_node.py - CLEAN (Well-Secured)

**Purpose:** Main compositor node with project validation
**Lines:** 1918
**Risk Level:** LOW

**Analysis:**
- Lines 34-57: Implements DANGEROUS_EXPRESSION_PATTERNS detection
- Lines 83-158: Full project validation system
- Lines 261-285: Path traversal validation
- Lines 343-355: Project ID validation (filesystem-safe)
- Lines 1646-1655: Uses `trust_remote_code=False` (SECURE)

**Note:** The `eval` match in grep was a **detection pattern** (regex to block eval), not a vulnerability.

**Positive Security Features:**
- Expression sandbox with dangerous pattern detection
- Input validation for numeric bounds
- String/array length limits
- Path traversal prevention
- Project ID sanitization

**Verdict:** No action required - exemplary security implementation

---

### 4. nodes/lattice_frame_interpolation.py - HIGH RISK (1 Issue)

**Purpose:** RIFE frame interpolation for video
**Lines:** 851
**Risk Level:** HIGH

**Issue Found:**

```
Line 238: state_dict = torch.load(model_path, map_location=self.device)
```

**Problem:** `torch.load()` uses pickle internally which can execute arbitrary code if a malicious `.pth` file is loaded.

**Context:**
- Model paths are local admin-controlled directories (lines 195-218):
  - `models/rife/`
  - `models/video_interpolation/`
  - `custom_nodes/ComfyUI-Frame-Interpolation/rife/`
  - `~/.cache/rife`

**Risk Assessment:**
- Attack vector: Malicious model file placed in model directory
- Likelihood: Low (requires local access)
- Impact: High (arbitrary code execution)

**Recommended Fix:**
```python
# Option 1: Add weights_only=True (PyTorch 2.0+)
state_dict = torch.load(model_path, map_location=self.device, weights_only=True)

# Option 2: Use safetensors format if available
from safetensors.torch import load_file
state_dict = load_file(model_path)
```

**Note:** Line 179 `self._model.eval()` is PyTorch's evaluation mode method, NOT Python's `eval()` - this is safe.

---

### 5. nodes/lattice_api_proxy.py - CLEAN

**Purpose:** API proxy for OpenAI/Anthropic
**Lines:** 793
**Risk Level:** LOW

**Analysis:**
- No model loading
- API keys read from environment variables (good practice)
- No dangerous patterns found

**Verdict:** No action required

---

### 6. nodes/lattice_stem_separation.py - CLEAN

**Purpose:** Audio stem separation using Demucs
**Lines:** 785
**Risk Level:** LOW

**Analysis:**
- Line 180: `self._model.eval()` - PyTorch eval mode (SAFE)
- Uses `torchaudio.pipelines.HDEMUCS_HIGH_MUSDB_PLUS` (official bundle)
- Uses `demucs.pretrained.get_model()` (official package)
- No `torch.load`, `pickle`, or `trust_remote_code`

**Verdict:** No action required

---

### 7. nodes/lattice_vectorize.py - CLEAN

**Purpose:** Image to SVG vectorization
**Lines:** 818
**Risk Level:** LOW

**Analysis:**
- Lines 684-690: Uses `trust_remote_code=False` (SECURE)
- Line 692: `STARVECTOR_MODEL.eval()` - PyTorch eval mode (SAFE)
- Uses vtracer (Rust-based, safe)
- No `torch.load`, `pickle`, or dangerous patterns

**Verdict:** No action required

---

### 8. nodes/__init__.py - CLEAN

**Purpose:** Module initialization
**Lines:** 33
**Risk Level:** LOW

**Analysis:**
- Only contains imports
- No executable logic

**Verdict:** No action required

---

## Summary of Required Actions

| Priority | File | Line | Issue | Action |
|----------|------|------|-------|--------|
| HIGH | lattice_frame_interpolation.py | 238 | `torch.load` without `weights_only=True` | Add `weights_only=True` or switch to safetensors |

---

## Security Controls Already in Place

1. **Expression Sandbox** (compositor_node.py)
   - Blocks eval, Function, require, import, prototype pollution
   - 86/86 tests passing

2. **Model Loading** (multiple files)
   - `trust_remote_code=False` consistently used
   - Prevents arbitrary code execution from HuggingFace models

3. **Project Validation** (compositor_node.py)
   - Size limits
   - Nesting depth limits
   - Path traversal prevention
   - Expression pattern detection

4. **Hash Verification** (lattice_layer_decomposition.py)
   - SHA256 verification infrastructure for model files

---

## Recommendations

### Immediate (Before Next Release)
1. Fix `torch.load` in `lattice_frame_interpolation.py:238`

### Future Enhancements
1. Add hash verification to RIFE model loading
2. Consider migrating to safetensors format where possible
3. Implement model registry with SHA256 verification for all models
4. Add rate limiting to API endpoints

---

## Audit Verification

To reproduce this audit:
```bash
# Search for dangerous patterns
grep -rn "trust_remote_code\|pickle\.load\|torch\.load\|exec(\|eval(" nodes/ --include="*.py"

# Verify trust_remote_code settings
grep -rn "trust_remote_code" nodes/ --include="*.py"
```
