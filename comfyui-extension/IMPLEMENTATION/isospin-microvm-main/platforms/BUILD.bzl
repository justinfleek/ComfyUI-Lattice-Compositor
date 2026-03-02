# Minimal root BUILD.bzl for Buck2
# All targets will be defined in subdirectories

# Default platform for local builds
platform(
    name = "default",
    constraint_values = [],
)