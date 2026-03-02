load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains")
load("@rules_rust//rust/workspace.bzl", "rust.workspace")
load("@bazel_skylib//:workspace.bzl", "bazel_skylib_workspace")

# Initialize base dependencies
bazel_skylib_workspace()
rules_rust_dependencies()
rust_register_toolchains(
    edition = "2024",
    version = "1.89.0",
)

# Configure Rust workspace
rust.workspace()