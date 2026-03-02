# Unified dependency management using Firecracker versions
# Conforce Cloud Hypervisor to use Firecracker's newer versions

load("@prelude//rust:defs.bzl", "rust_prebuilt_library")

# Rust version convergence constants
RUST_VERSIONS = {
    "kvm_bindings": {
        "version": "0.14.0", 
        "features": ["fam-wrappers", "serde"],
    },
    "kvm_ioctls": {
        "version": "0.24.0",
        "features": [],
    },
    "vm_memory": {
        "version": "0.17.1",
        "features": ["backend-mmap", "backend-bitmap"],
    },
    "vmm_sys_util": {
        "version": "0.15.0", 
        "features": ["with-serde"],
    },
    "linux_loader": {
        "version": "0.13.2",
        "features": ["bzimage", "elf", "pe"],
    },
    "libc": {
        "version": "0.2.179",
        "features": [],
    },
    "serde": {
        "version": "1.0.228",
        "features": ["derive", "rc"],
    },
    "serde_json": {
        "version": "1.0.149", 
        "features": [],
    },
    "thiserror": {
        "version": "2.0.17",
        "features = []",
    },
    "uuid": {
        "version": "1.19.0",
        "features": [],
    },
    "clap": {
        "version": "4.5.54",
        "features": ["derive", "string"],
    },
    "tokio": {
        "version": "1.42.0", 
        "features": ["full"],
    },
    "displaydoc": {
        "version": "0.2.5",
        "features": [],
    },
    "zerocopy": {
        "version": "0.8.33",
        "features": [],
    },
}

def rust_workspace():
    """Unified Rust workspace with version convergence"""
    
    # Core virtualization dependencies (Firecracker versions)
    _create_rust_dep("kvm_bindings")
    _create_rust_dep("kvm_ioctls")
    _create_rust_dep("vm_memory") 
    _create_rust_dep("vmm_sys_util")
    _create_rust_dep("linux_loader")
    
    # Essential utilities
    _create_rust_dep("libc")
    _create_rust_dep("serde")
    _create_rust_dep("serde_json")
    _create_rust_dep("thiserror")
    _create_rust_dep("uuid")
    _create_rust_dep("clap")
    _create_rust_dep("tokio")
    _create_rust_dep("displaydoc") 
    _create_rust_dep("zerocopy")

def _create_rust_dep(crate_name):
    """Create unified Rust dependency"""
    config = RUST_VERSIONS[crate_name]
    
    rust_prebuilt_library(
        name = crate_name,
        crate_root = "src/lib.rs",
        features = config.get("features", []),
        # This will be resolved via Buck2's crate registry
        version = config["version"],
        edition = "2024",
    )

# Git dependencies (micro_http)
def _git_deps():
    rust_external_repo(
        name = "micro_http",
        type = "git",
        urls = ["https://github.com/firecracker-microvm/micro-http.git"],
        commit = "main",
    )