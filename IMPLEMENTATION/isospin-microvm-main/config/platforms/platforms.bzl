# Modern platform constraints for 2026 Buck2

# CPU constraint settings
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

# OS constraint settings
constraint_setting(
    name = "os",
    default_constraint_value = ":linux",
)

constraint_value(
    name = "linux",
    constraint_setting = ":os", 
    description = "Linux operating system",
)

# Modern platform definitions
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

def platforms():
    """Register all platforms"""
    pass