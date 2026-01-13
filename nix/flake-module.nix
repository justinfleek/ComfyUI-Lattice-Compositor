{ inputs, ... }:
{
  # Expose overlays via flake-parts
  flake.overlays.default = import ./overlays/default.nix;

  perSystem =
    {
      pkgs,
      system,
      ...
    }:
    {
      # Dev shell: Python + uv, Bun; keep it light for ComfyUI envs
      devShells.default = pkgs.mkShell {
        packages = with pkgs; [
          python3
          python3Packages.pytest
          python3Packages.pytest-cov
          python3Packages.pytest-asyncio
          uv
          bun
          git
        ];
      };

      # UI package built with bun2nix v2
      # bun2nix v2: use packages.${system}.default instead of lib
      packages.ui = pkgs.callPackage ./packages/ui.nix {
        bun2nix = inputs.bun2nix.packages.${system}.default;
        inherit (pkgs) bun;
        inherit (pkgs) nodejs_20;
      };

      # treefmt: always on (nixfmt, statix, deadnix, ruff)
      # Note: biome disabled in treefmt due to treefmt-nix validation issue
      # that strips out our "off" linting settings. Use biome directly for formatting.
      treefmt = {
        projectRootFile = "flake.nix";
        programs = {
          nixfmt.enable = true;
          statix.enable = true;
          deadnix.enable = true;
          ruff.enable = true;
        };
      };
    };
}
