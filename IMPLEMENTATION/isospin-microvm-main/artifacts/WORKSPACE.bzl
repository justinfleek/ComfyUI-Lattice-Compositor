workspace(
    name = "isospin",
    managed_directories = {
        "3rdparty": {
            "type": "third-party",
        },
    },
)

# Load Buck2 built-in rules
load("@bazel_skylib//:lib.bzl", "selects")
load("@bazel_features//:features.bzl", "bazel_features")

# Define repository rules for external dependencies
load("//3rdparty/rust:rust_repositories.bzl", "rust_repositories")
load("//3rdparty/rust:rust_workspaces.bzl", "rust_workspaces")

# Initialize Rust toolchain and repositories
rust_repositories()
rust_workspaces()

# Platform configurations
load("//platforms:platforms.bzl", "platforms")
platforms()

# Common prelude exports
package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],  # Apache 2.0
)

# Register execution toolchains
register_toolchains("//toolchains/rust:rust_toolchain")