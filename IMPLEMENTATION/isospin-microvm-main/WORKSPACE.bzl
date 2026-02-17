cell(
    name = "isospin"
)

# Load modern Buck2 Rust rules
load("@prelude//rust:defs.bzl", "rust_binary", "rust_library", "rust_proc_macro", "rust_test")

# External dependency cells for 2026 patterns
load("//third_party:deps.bzl", "rust_workspace")
rust_workspace()

# Platform definitions using modern constraints
load("//config/platforms:platforms.bzl", "platforms")
platforms()

# Toolchain registration
register_toolchains("//tools/rust:rust_toolchain")

# Config modifiers for different build scenarios
load("//config/modifiers:modifiers.bzl", "configuration_modifiers")
configuration_modifiers()