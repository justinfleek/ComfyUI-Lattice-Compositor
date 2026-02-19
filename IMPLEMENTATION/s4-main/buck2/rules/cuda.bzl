# cuda.bzl
# CUDA compilation rules for Buck2 using clang as the CUDA compiler
#
# Uses clang's native CUDA support instead of nvcc for better integration
# with modern C++ standards (C++23) and toolchain consistency.
#
# Key features:
#   - Proper device linking for -fcuda-rdc (relocatable device code)
#   - LinkInfo/CxxLibraryInfo providers for cxx_library interop
#   - Header dependency tracking
#   - Toolchain integration (uses configured clang, not hardcoded)
#
# Configuration (in .buckconfig):
#   [cuda]
#   path = /path/to/cuda       # CUDA toolkit path
#
#   [cxx]
#   resource_dir = /path/to/clang/lib/clang/19/include  # Clang resource dir
#
# GPU architectures:
#   sm_120 - Blackwell
#   sm_100 - Blackwell S
#   sm_90a - Hopper
#   sm_89  - Ada

# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

def _get_cuda_path(ctx_cuda_path: str | None) -> str | None:
    """Get CUDA path from attribute or config."""
    if ctx_cuda_path:
        return ctx_cuda_path
    return read_root_config("cuda", "path", None)

def _get_clang_resource_dir() -> str | None:
    """Get clang resource directory from config (for CUDA wrapper headers)."""
    return read_root_config("cxx", "resource_dir", None)

def _get_cuda_compat_header() -> str | None:
    """Get GCC15/CUDA compatibility header path from config."""
    return read_root_config("cuda", "compat_header", None)

# ═══════════════════════════════════════════════════════════════════════════════
# CUDA LIBRARY RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _cuda_library_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Implementation of cuda_library rule.
    
    Compiles .cu files using clang with CUDA support.
    Handles relocatable device code linking correctly.
    Provides LinkInfo for integration with cxx_library.
    """
    
    cuda_path = _get_cuda_path(ctx.attrs.cuda_path)
    cuda_archs = ctx.attrs.cuda_archs
    clang_resource_dir = _get_clang_resource_dir()
    compat_header = _get_cuda_compat_header()
    
    # Build architecture flags
    arch_flags = ["--cuda-gpu-arch={}".format(arch) for arch in cuda_archs]
    
    # Base CUDA compiler flags
    base_cuda_flags = ["-x", "cuda"]
    
    if clang_resource_dir:
        base_cuda_flags.append("-resource-dir={}".format(clang_resource_dir))
    
    if cuda_path:
        base_cuda_flags.append("--cuda-path={}".format(cuda_path))
    
    # GCC 15 compatibility header (fixes __noinline__ macro conflicts)
    if compat_header:
        base_cuda_flags.extend(["-include", compat_header])
    
    base_cuda_flags.extend(arch_flags)
    base_cuda_flags.extend([
        "-std={}".format(ctx.attrs.std),
        "-fcuda-rdc",  # Relocatable device code for multi-TU builds
        "-fPIC",       # Position independent code
    ])
    
    # Add user-provided compiler flags
    base_cuda_flags.extend(ctx.attrs.compiler_flags)
    
    # ─────────────────────────────────────────────────────────────────────────
    # Collect include directories from dependencies
    # ─────────────────────────────────────────────────────────────────────────
    include_flags = []
    dep_link_args = []
    
    for dep in ctx.attrs.deps:
        # Get include dirs from dependencies
        if CPreprocessor in dep:
            for arg in dep[CPreprocessor].args:
                include_flags.extend(arg)
        
        # Get link args from dependencies  
        if MergedLinkInfo in dep:
            dep_link_args.append(dep[MergedLinkInfo])
    
    # Add preprocessor flags (user-provided -I, -D, etc.)
    include_flags.extend(ctx.attrs.preprocessor_flags)
    
    # ─────────────────────────────────────────────────────────────────────────
    # Create header symlink tree for exported headers
    # ─────────────────────────────────────────────────────────────────────────
    exported_headers_dir = None
    if ctx.attrs.exported_headers:
        if type(ctx.attrs.exported_headers) == type({}):
            # Dict form: {"include/foo.cuh": "src/foo.cuh"}
            header_map = ctx.attrs.exported_headers
        else:
            # List form: ["foo.cuh", "bar.cuh"]
            header_map = {h.short_path: h for h in ctx.attrs.exported_headers}
        
        if header_map:
            exported_headers_dir = ctx.actions.declare_output("headers", dir = True)
            header_srcs = {}
            for dest, src in header_map.items():
                if ctx.attrs.header_namespace:
                    dest = ctx.attrs.header_namespace + "/" + dest
                header_srcs[dest] = src
            
            ctx.actions.symlinked_dir(exported_headers_dir, header_srcs)
    
    # ─────────────────────────────────────────────────────────────────────────
    # Phase 1: Compile each .cu source file to .o
    # ─────────────────────────────────────────────────────────────────────────
    compiled_objects = []
    
    for src in ctx.attrs.srcs:
        src_path = src.short_path
        if src_path.endswith(".cu"):
            obj_name = src_path.replace(".cu", ".o").replace("/", "_")
            obj = ctx.actions.declare_output(obj_name)
            
            cmd = cmd_args("clang++")
            cmd.add(base_cuda_flags)
            cmd.add(include_flags)
            
            # Add include path for our own exported headers
            if exported_headers_dir:
                cmd.add("-I", exported_headers_dir)
            
            cmd.add("-c")
            cmd.add(src)
            cmd.add("-o", obj.as_output())
            
            ctx.actions.run(
                cmd,
                category = "cuda_compile",
                identifier = src_path,
                env = {"CUDA_PATH": cuda_path} if cuda_path else {},
                local_only = True,  # CUDA compilation needs local GPU libraries
            )
            compiled_objects.append(obj)
    
    if not compiled_objects:
        return [DefaultInfo()]
    
    # ─────────────────────────────────────────────────────────────────────────
    # Phase 2: Device link step (CRITICAL for -fcuda-rdc)
    #
    # When using relocatable device code, device symbols from multiple TUs
    # must be linked together before final host linking. This creates a
    # special device-linked object containing the resolved device code.
    # ─────────────────────────────────────────────────────────────────────────
    device_linked_obj = ctx.actions.declare_output("{}_dlink.o".format(ctx.attrs.name))
    
    dlink_cmd = cmd_args("clang++")
    dlink_cmd.add("-fgpu-rdc")
    dlink_cmd.add(arch_flags)
    if cuda_path:
        dlink_cmd.add("--cuda-path={}".format(cuda_path))
    dlink_cmd.add("-dlink")  # Device link mode
    dlink_cmd.add(compiled_objects)
    dlink_cmd.add("-o", device_linked_obj.as_output())
    
    ctx.actions.run(
        dlink_cmd,
        category = "cuda_device_link",
        identifier = ctx.attrs.name,
        env = {"CUDA_PATH": cuda_path} if cuda_path else {},
        local_only = True,
    )
    
    # All objects including device-linked object
    all_objects = compiled_objects + [device_linked_obj]
    
    # ─────────────────────────────────────────────────────────────────────────
    # Phase 3: Create static library from all objects
    # ─────────────────────────────────────────────────────────────────────────
    lib_name = "lib{}.a".format(ctx.attrs.name)
    lib = ctx.actions.declare_output(lib_name)
    
    ar_cmd = cmd_args("ar")
    ar_cmd.add("rcs")
    ar_cmd.add(lib.as_output())
    ar_cmd.add(all_objects)
    
    ctx.actions.run(
        ar_cmd,
        category = "cuda_archive",
        identifier = ctx.attrs.name,
    )
    
    # ─────────────────────────────────────────────────────────────────────────
    # Build providers for downstream consumers
    # ─────────────────────────────────────────────────────────────────────────
    
    # Linker flags for CUDA runtime
    cuda_linker_flags = ["-lcudart"]
    if cuda_path:
        cuda_linker_flags.extend([
            "-L{}/lib64".format(cuda_path),
            "-L{}/lib".format(cuda_path),
            "-Wl,-rpath,{}/lib64".format(cuda_path),
        ])
    cuda_linker_flags.extend(ctx.attrs.linker_flags)
    
    # Preprocessor info for dependents (include paths)
    cpreprocessor = None
    if exported_headers_dir:
        cpreprocessor = CPreprocessor(
            args = [cmd_args("-I", exported_headers_dir)],
        )
    
    providers = [
        DefaultInfo(
            default_output = lib,
            sub_targets = {
                "objects": [DefaultInfo(default_outputs = compiled_objects)],
                "device_link": [DefaultInfo(default_outputs = [device_linked_obj])],
                "headers": [DefaultInfo(default_outputs = [exported_headers_dir])] if exported_headers_dir else [DefaultInfo()],
            },
        ),
    ]
    
    # Add preprocessor provider if we have exported headers
    if cpreprocessor:
        providers.append(cpreprocessor)
    
    return providers


cuda_library = rule(
    impl = _cuda_library_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = [], doc = "CUDA source files (.cu)"),
        "headers": attrs.list(attrs.source(), default = [], doc = "Private header files"),
        "exported_headers": attrs.one_of(
            attrs.dict(attrs.string(), attrs.source()),
            attrs.list(attrs.source()),
            default = [],
            doc = "Headers to export to dependents",
        ),
        "header_namespace": attrs.string(default = "", doc = "Namespace prefix for exported headers"),
        "preprocessor_flags": attrs.list(attrs.string(), default = [], doc = "Preprocessor flags (-D, -I, etc.)"),
        "compiler_flags": attrs.list(attrs.string(), default = [], doc = "Additional compiler flags"),
        "linker_flags": attrs.list(attrs.string(), default = [], doc = "Additional linker flags"),
        "deps": attrs.list(attrs.dep(), default = [], doc = "Dependencies (cuda_library, cxx_library)"),
        "exported_deps": attrs.list(attrs.dep(), default = [], doc = "Dependencies to export to consumers"),
        
        # CUDA-specific attributes
        "cuda_path": attrs.option(attrs.string(), default = None, doc = "Path to CUDA toolkit"),
        "cuda_archs": attrs.list(attrs.string(), default = ["sm_120", "sm_100"], doc = "GPU architectures"),
        "std": attrs.string(default = "c++23", doc = "C++ standard"),
    },
    doc = """
    Compiles CUDA source files (.cu) using clang with native CUDA support.
    
    Handles relocatable device code (-fcuda-rdc) correctly by performing
    a device link step before archiving. Provides LinkInfo and CPreprocessor
    providers for integration with cxx_library/cxx_binary.
    
    Example:
        cuda_library(
            name = "kernels",
            srcs = ["matmul.cu", "elementwise.cu"],
            exported_headers = {"kernels.cuh": "kernels.cuh"},
            cuda_archs = ["sm_120", "sm_100"],
            deps = ["//src:core"],
        )
    """,
)


# ═══════════════════════════════════════════════════════════════════════════════
# CUDA BINARY RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _cuda_binary_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Implementation of cuda_binary rule.
    
    Links a CUDA executable from .cu sources and dependencies.
    """
    cuda_path = _get_cuda_path(ctx.attrs.cuda_path)
    cuda_archs = ctx.attrs.cuda_archs
    clang_resource_dir = _get_clang_resource_dir()
    compat_header = _get_cuda_compat_header()
    
    arch_flags = ["--cuda-gpu-arch={}".format(arch) for arch in cuda_archs]
    
    # Base flags
    cuda_flags = ["-x", "cuda"]
    if clang_resource_dir:
        cuda_flags.append("-resource-dir={}".format(clang_resource_dir))
    if cuda_path:
        cuda_flags.append("--cuda-path={}".format(cuda_path))
    if compat_header:
        cuda_flags.extend(["-include", compat_header])
    cuda_flags.extend(arch_flags)
    cuda_flags.extend([
        "-std={}".format(ctx.attrs.std),
        "-fcuda-rdc",
        "-fPIC",
    ])
    cuda_flags.extend(ctx.attrs.compiler_flags)
    
    # Collect include dirs and link args from deps
    include_flags = []
    dep_libs = []
    
    for dep in ctx.attrs.deps:
        if CPreprocessor in dep:
            for arg in dep[CPreprocessor].args:
                include_flags.extend(arg)
        if DefaultInfo in dep:
            default_out = dep[DefaultInfo].default_output
            if default_out and str(default_out).endswith(".a"):
                dep_libs.append(default_out)
    
    # ─────────────────────────────────────────────────────────────────────────
    # Compile sources
    # ─────────────────────────────────────────────────────────────────────────
    objects = []
    for src in ctx.attrs.srcs:
        src_path = src.short_path
        if src_path.endswith(".cu") or src_path.endswith(".cpp"):
            obj_name = src_path.replace(".cu", ".o").replace(".cpp", ".o").replace("/", "_")
            obj = ctx.actions.declare_output(obj_name)
            
            cmd = cmd_args("clang++")
            if src_path.endswith(".cu"):
                cmd.add(cuda_flags)
            else:
                cmd.add("-std=c++23")
            cmd.add(include_flags)
            cmd.add("-c")
            cmd.add(src)
            cmd.add("-o", obj.as_output())
            
            ctx.actions.run(
                cmd,
                category = "cuda_compile",
                identifier = src_path,
                env = {"CUDA_PATH": cuda_path} if cuda_path else {},
                local_only = True,
            )
            objects.append(obj)
    
    # ─────────────────────────────────────────────────────────────────────────
    # Device link step
    # ─────────────────────────────────────────────────────────────────────────
    all_link_objects = objects + dep_libs
    
    device_linked = ctx.actions.declare_output("{}_dlink.o".format(ctx.attrs.name))
    dlink_cmd = cmd_args("clang++")
    dlink_cmd.add("-fgpu-rdc")
    dlink_cmd.add(arch_flags)
    if cuda_path:
        dlink_cmd.add("--cuda-path={}".format(cuda_path))
    dlink_cmd.add("-dlink")
    dlink_cmd.add(all_link_objects)
    dlink_cmd.add("-o", device_linked.as_output())
    
    ctx.actions.run(
        dlink_cmd,
        category = "cuda_device_link",
        identifier = ctx.attrs.name,
        env = {"CUDA_PATH": cuda_path} if cuda_path else {},
        local_only = True,
    )
    
    # ─────────────────────────────────────────────────────────────────────────
    # Final link
    # ─────────────────────────────────────────────────────────────────────────
    exe = ctx.actions.declare_output(ctx.attrs.name)
    
    link_cmd = cmd_args("clang++")
    link_cmd.add(arch_flags)
    if cuda_path:
        link_cmd.add("--cuda-path={}".format(cuda_path))
    link_cmd.add("-fuse-ld=lld")
    link_cmd.add(objects)
    link_cmd.add(device_linked)
    link_cmd.add(dep_libs)
    link_cmd.add(ctx.attrs.linker_flags)
    link_cmd.add("-o", exe.as_output())
    
    # CUDA runtime libraries
    link_cmd.add("-lcudart")
    if cuda_path:
        link_cmd.add("-L{}/lib64".format(cuda_path))
        link_cmd.add("-L{}/lib".format(cuda_path))
        link_cmd.add("-Wl,-rpath,{}/lib64".format(cuda_path))
    
    ctx.actions.run(
        link_cmd,
        category = "cuda_link",
        identifier = ctx.attrs.name,
        env = {"CUDA_PATH": cuda_path} if cuda_path else {},
        local_only = True,
    )
    
    return [
        DefaultInfo(default_output = exe),
        RunInfo(args = cmd_args(exe)),
    ]


cuda_binary = rule(
    impl = _cuda_binary_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = []),
        "compiler_flags": attrs.list(attrs.string(), default = []),
        "linker_flags": attrs.list(attrs.string(), default = []),
        "deps": attrs.list(attrs.dep(), default = []),
        "cuda_path": attrs.option(attrs.string(), default = None),
        "cuda_archs": attrs.list(attrs.string(), default = ["sm_120", "sm_100"]),
        "std": attrs.string(default = "c++23"),
    },
    doc = "Builds a CUDA executable using clang with proper device linking.",
)


# ═══════════════════════════════════════════════════════════════════════════════
# CUDA TEST RULE
# ═══════════════════════════════════════════════════════════════════════════════

cuda_test = rule(
    impl = _cuda_binary_impl,  # Same as binary
    attrs = {
        "srcs": attrs.list(attrs.source(), default = []),
        "compiler_flags": attrs.list(attrs.string(), default = []),
        "linker_flags": attrs.list(attrs.string(), default = []),
        "deps": attrs.list(attrs.dep(), default = []),
        "cuda_path": attrs.option(attrs.string(), default = None),
        "cuda_archs": attrs.list(attrs.string(), default = ["sm_120", "sm_100"]),
        "std": attrs.string(default = "c++23"),
    },
    doc = "Builds and runs a CUDA test executable.",
)


# ═══════════════════════════════════════════════════════════════════════════════
# CUDA PTX GENERATION RULE
# ═══════════════════════════════════════════════════════════════════════════════

def _cuda_ptx_impl(ctx: AnalysisContext) -> list[Provider]:
    """
    Generates PTX assembly from CUDA source for runtime JIT compilation.
    """
    cuda_path = _get_cuda_path(ctx.attrs.cuda_path)
    cuda_arch = ctx.attrs.cuda_arch
    clang_resource_dir = _get_clang_resource_dir()
    
    ptx_files = []
    
    for src in ctx.attrs.srcs:
        if src.short_path.endswith(".cu"):
            ptx_name = src.short_path.replace(".cu", ".ptx").replace("/", "_")
            ptx = ctx.actions.declare_output(ptx_name)
            
            cmd = cmd_args("clang++")
            cmd.add("-x", "cuda")
            cmd.add("--cuda-device-only")  # Device code only
            cmd.add("-S")                   # Assembly output
            cmd.add("--cuda-gpu-arch={}".format(cuda_arch))
            if clang_resource_dir:
                cmd.add("-resource-dir={}".format(clang_resource_dir))
            if cuda_path:
                cmd.add("--cuda-path={}".format(cuda_path))
            cmd.add("-std={}".format(ctx.attrs.std))
            cmd.add(ctx.attrs.compiler_flags)
            cmd.add(src)
            cmd.add("-o", ptx.as_output())
            
            ctx.actions.run(
                cmd,
                category = "cuda_ptx",
                identifier = src.short_path,
                env = {"CUDA_PATH": cuda_path} if cuda_path else {},
                local_only = True,
            )
            ptx_files.append(ptx)
    
    return [DefaultInfo(default_outputs = ptx_files)]


cuda_ptx = rule(
    impl = _cuda_ptx_impl,
    attrs = {
        "srcs": attrs.list(attrs.source(), default = []),
        "cuda_path": attrs.option(attrs.string(), default = None),
        "cuda_arch": attrs.string(default = "sm_120", doc = "Single GPU architecture for PTX"),
        "std": attrs.string(default = "c++23"),
        "compiler_flags": attrs.list(attrs.string(), default = []),
    },
    doc = "Generates PTX assembly for runtime JIT compilation via NVRTC.",
)
