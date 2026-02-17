# AWS-LC library provider for Buck2

def _aws_lc_impl(ctx: AnalysisContext) -> list[Provider]:
    """Build aws-lc via Nix and provide library artifacts."""
    
    # Build aws-lc via Nix
    out = ctx.actions.declare_output("aws-lc")
    
    nix_build = cmd_args([
        "sh", "-c",
        """
        set -e
        nix build --no-link --print-out-paths ./toolchains/nix#aws-lc | while read store_path; do
            if [ -d "$store_path/lib" ]; then
                cp -r "$store_path" "$1"
                break
            fi
        done
        """,
        "--",
        out.as_output(),
    ])
    
    ctx.actions.run(nix_build, category = "nix_aws_lc", local_only = True)
    
    return [
        DefaultInfo(
            default_output = out,
            sub_targets = {
                "libaws_lc_0_35_0_crypto.a": [DefaultInfo(default_output = out)],
                "libaws_lc_0_35_0_ssl.a": [DefaultInfo(default_output = out)],
                "include": [DefaultInfo(default_output = out)],
            }
        ),
    ]

aws_lc = rule(
    impl = _aws_lc_impl,
    attrs = {},
)