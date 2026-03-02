# Isospin Deployment Instructions

## Prerequisites
- Buck2 build system (8.0.0+)
- Rust 1.89.0+
- NixOS (optional, for dev environment)

## Quick Start

1. Extract artifacts:
```bash
tar -xzf isospin_sources.tar.gz
tar -xzf isospin_build_config.tar.gz
```

2. Build Firecracker:
```bash
buck2 build //firecracker:firecracker_binary
```

3. Build Cloud Hypervisor:
```bash
buck2 build //cloud-hypervisor:cloud_hypervisor_binary
```

4. Run all tests:
```bash
buck2 test //...
```

## Platform-Specific Builds

### x86_64 Linux
```bash
buck2 build //firecracker:firecracker_binary --platforms=//platforms:x86_64-linux
buck2 build //cloud-hypervisor:cloud_hypervisor_binary --platforms=//platforms:x86_64-linux
```

### aarch64 Linux
```bash
buck2 build //firecracker:firecracker_binary --platforms=//platforms:aarch64-linux
buck2 build //cloud-hypervisor:cloud_hypervisor_binary --platforms=//platforms:aarch64-linux
```

## Development Environment (Nix)
```bash
nix develop
```

## Test Validation
```bash
./run_tests.sh      # Run all validation tests
./validate_builds.sh # Comprehensive build validation
```

## Project Structure
- `firecracker/` - Firecracker microVM hypervisor
- `cloud-hypervisor/` - Cloud Hypervisor VMM
- `platforms/` - Platform configurations
- `prelude/` - Common build rules
- `3rdparty/` - External dependencies
