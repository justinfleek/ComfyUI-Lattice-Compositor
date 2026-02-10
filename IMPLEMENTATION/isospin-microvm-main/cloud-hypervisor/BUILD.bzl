# Modern Cloud Hypervisor build structure using unified versions

load("@prelude//rust:defs.bzl", "rust_library", "rust_binary")

# Start with leaf libraries - serial_buffer (zero dependencies)
rust_library(
    name = "serial_buffer_lib",
    srcs = glob(["src/**/*.rs"]),
    deps = [
        "//third_party:thiserror",  # Unified Firecracker version
    ],
    edition = "2024",
    # Cross-platform support
    target_compatible_with = [
        "config//platforms:x86_64-linux",
        "config//platforms:aarch64-linux", 
    ],
)