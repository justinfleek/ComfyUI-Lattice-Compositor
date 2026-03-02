# Modern Rust toolchain configuration for 2026

load("@prelude//rust:defs.bzl", "rust_toolchain")

def _get_rust_executable(rust_tool, tool_name):
    """Helper to get Rust executable"""
    return native.genrule(
        name = tool_name,
        cmd = "echo 'Mock tool for: " + tool_name + "'",
        out = tool_name,
        local = True,
    )

# Cross-compilation toolchains
rust_toolchain(
    name = "x86_64_linux_toolchain",
    target_triple = "x86_64-unknown-linux-gnu",
    rustc = "//tools/rust:x86_64_rustc",
    rustdoc = "//tools/rust:x86_64_rustdoc", 
    clippy_driver = "//tools/rust:x86_64_clippy",
    cargo = "//tools/rust:x86_64_cargo",
    rust_stdlib = None,  # Use bundled stdlib
    extra_rustc_flags = [
        "-C", "target-cpu=native",
        "-C", "link-arg=-Wl,--gc-sections",
    ],
)

rust_toolchain(
    name = "aarch64_linux_toolchain", 
    target_triple = "aarch64-unknown-linux-gnu",
    rustc = "//tools/rust:aarch64_rustc",
    rustdoc = "//tools/rust:aarch64_rustdoc",
    clippy_driver = "//tools/rust:aarch64_clippy", 
    cargo = "//tools/rust:aarch64_cargo",
    rust_stdlib = None,
    extra_rustc_flags = [
        "-C", "target-cpu=cortex-a72",
        "-C", "link-arg=-Wl,--gc-sections", 
    ],
)