# Configuration modifiers for different build scenarios

def production_transition_impl(platform, refs):
    """Production build optimization"""
    return {
        "rust.opt_level": "3",
        "rust.debug_assertions": False,
        "rust.overflow_checks": False, 
        "rust.lto": "fat",
    }

def development_transition_impl(platform, refs):
    """Development build configuration"""
    return {
        "rust.opt_level": "0",
        "rust.debug_assertions": True,
        "rust.overflow_checks": True,
        "rust.lto": "off",
    }

def ci_transition_impl(platform, refs):
    """CI build configuration"""
    return {
        "rust.opt_level": "2", 
        "rust.debug_assertions": True,
        "rust.overflow_checks": True,
        "rust.lto": "thin",
    }

# Modern transition definitions
transition(
    impl = development_transition_impl,
    refs = ["config/platforms:..."],
)

# Build modifiers
def configuration_modifiers():
    """Register all configuration modifiers"""
    pass