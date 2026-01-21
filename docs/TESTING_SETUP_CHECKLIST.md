# Complete Testing Setup Checklist

## ✅ Already Configured

- [x] **Terminal size fix** - Prevents "bogus screen size" warnings
- [x] **Playwright config** - Configured with WebGL/WebGPU support
- [x] **Test helpers** - Comprehensive `CompositorHelper` class
- [x] **E2E test structure** - Smoke tests, tutorials, export tests
- [x] **Nix dev environment** - All Python packages ready
- [x] **Test scripts** - `test:playwright` commands ready

## 🔧 Still Need to Set Up

### 1. Playwright Browsers Installation
**Status**: ⚠️ Not installed yet
**Action**: Run `npx playwright install chromium` in Nix shell

### 2. CI/CD E2E Tests
**Status**: ❌ Missing from CI workflow
**Action**: Add E2E test job to `.github/workflows/ci.yml`

### 3. ComfyUI Test Setup Script
**Status**: ❌ Missing
**Action**: Create script to start ComfyUI for testing

### 4. Test Environment Variables
**Status**: ⚠️ Hardcoded in config
**Action**: Add `.env.test` for test configuration

### 5. Screenshot/Artifact Handling
**Status**: ⚠️ Partially configured
**Action**: Ensure screenshots directory exists, add to CI artifacts

### 6. GPU/WebGL Testing in CI
**Status**: ⚠️ Needs special runner
**Action**: Configure CI for GPU-enabled testing (or use software rendering)

### 7. Test Data/Assets
**Status**: ⚠️ Need to verify
**Action**: Ensure test assets are available

### 8. Test Isolation/Cleanup
**Status**: ⚠️ Need to verify
**Action**: Ensure tests clean up after themselves

## Priority Order

1. **Playwright browsers** (required to run tests)
2. **ComfyUI setup script** (required for E2E tests)
3. **CI/CD integration** (for automated testing)
4. **Environment variables** (for flexibility)
5. **GPU testing setup** (for WebGL/WebGPU tests)
