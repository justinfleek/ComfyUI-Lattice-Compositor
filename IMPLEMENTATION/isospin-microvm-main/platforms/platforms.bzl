load("@bazel_skylib//:lib.bzl", "selects")

# Platform definitions for isospin builds
# Supported: x86_64 and aarch64 Linux platforms

# CPU Constraints
package(default_visibility = ["//visibility:public"])

constraint_setting(
    name = "cpu",
    default_constraint_value = ":x86_64",
)

constraint_value(
    name = "x86_64",
    constraint_setting = ":cpu",
    description = "x86_64 CPU architecture",
)

constraint_value(
    name = "aarch64",
    constraint_setting = ":cpu",
    description = "aarch64 CPU architecture",
)

# OS Constraints
constraint_setting(
    name = "os",
    default_constraint_value = ":linux",
)

constraint_value(
    name = "linux",
    constraint_setting = ":os",
    description = "Linux operating system",
)

# Platform definitions
platform(
    name = "x86_64-linux",
    constraint_values = [
        ":x86_64",
        ":linux",
    ],
)

platform(
    name = "aarch64-linux",
    constraint_values = [
        ":aarch64", 
        ":linux",
    ],
)