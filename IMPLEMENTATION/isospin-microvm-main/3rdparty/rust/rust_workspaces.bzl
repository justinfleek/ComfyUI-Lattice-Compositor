# Common Rust dependencies for both Firecracker and Cloud Hypervisor
# Centralized dependency management for isospin monorepo

load("@rules_rust//crate:defs.bzl", "crate")

def rust_workspaces():
    """Define external Rust dependencies for isospin projects"""
    
    # Core virtualization dependencies (shared by both)
    crate(
        name = "kvm_bindings",
        version = "0.12.1",
        features = ["fam-wrappers"],
    )
    
    crate(
        name = "kvm_ioctls", 
        version = "0.22.1",
    )
    
    crate(
        name = "vm_memory",
        version = "0.16.1",
        features = ["backend-mmap", "backend-atomic"],
    )
    
    crate(
        name = "vmm_sys_util",
        version = "0.12.1",
    )
    
    # Async and networking
    crate(
        name = "tokio",
        version = "1.42.0",
        features = ["full"],
    )
    
    crate(
        name = "serde",
        version = "1.0.217",
        features = ["derive"],
    )
    
    crate(
        name = "serde_json",
        version = "1.0.134",
    )
    
    crate(
        name = "bincode",
        version = "1.3.3",
    )
    
    # Testing frameworks
    crate(
        name = "criterion",
        version = "0.5.1",
        dev_dependency = True,
    )
    
    crate(
        name = "proptest",
        version = "1.5.0", 
        dev_dependency = True,
    )
    
    # Security and system utilities
    crate(
        name = "seccompiler",
        version = "0.4.0",
    )
    
    crate(
        name = "userfaultfd",
        version = "0.8.1",
    )
    
    # Virtio infrastructure
    crate(
        name = "virtio_queue",
        version = "0.14.0",
    )
    
    crate(
        name = "virtio_bindings",
        version = "0.2.2",
    )
    
    # System interfaces
    crate(
        name = "libc",
        version = "0.2.169",
    )
    
    crate(
        name = "nix",
        version = "0.29.0",
    )
    
    crate(
        name = "errno",
        version = "0.3.10",
    )
    
    # Error handling
    crate(
        name = "thiserror",
        version = "2.0.9",
    )
    
    crate(
        name = "anyhow",
        version = "1.0.95",
    )
    
    # Logging
    crate(
        name = "log",
        version = "0.4.25",
    )
    
    crate(
        name = "env_logger",
        version = "0.11.6",
        dev_dependency = True,
    )