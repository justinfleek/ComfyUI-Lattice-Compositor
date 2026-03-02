# Templates Reference

Source: `nix/templates/`

Available templates for `nix flake init`.

## default

Full straylight setup with formatter, linter, devshell, and prelude.

```bash
nix flake init -t github:straylight-software/straylight
```

Features:

- All flake modules imported
- Formatter enabled
- Devshell enabled
- Prelude access via `config.straylight.prelude`

## minimal

Just nixpkgs with straylight overlays. No formatter, no devshell.

```bash
nix flake init -t github:straylight-software/straylight#minimal
```

Features:

- Only `nixpkgs` module imported
- Minimal configuration
- Good for adding straylight to existing projects

## nv

NVIDIA development setup with CUDA SDK.

```bash
nix flake init -t github:straylight-software/straylight#nv
```

Features:

- NVIDIA SDK enabled
- CUDA packages available
- GPU stdenvs accessible

## dhall-configured

Configuration via Dhall instead of Nix.

```bash
nix flake init -t github:straylight-software/straylight#dhall-configured
```

## nickel-configured

Configuration via Nickel instead of Nix.

```bash
nix flake init -t github:straylight-software/straylight#nickel-configured
```

## Template Contents

### default/flake.nix

```nix
{
  description = "Project powered by straylight";

  inputs = {
    straylight.url = "github:straylight-software/straylight";
    nixpkgs.follows = "straylight/nixpkgs";
    flake-parts.follows = "straylight/flake-parts";
  };

  outputs = inputs@{ flake-parts, straylight, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ straylight.modules.flake.default ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];

      straylight = {
        formatter.enable = true;
        devshell.enable = true;
        nixpkgs.allow-unfree = true;
      };

      perSystem = { config, pkgs, ... }:
        let
          inherit (config.straylight) prelude;
        in {
          packages.default = pkgs.hello;
        };
    };
}
```

### minimal/flake.nix

```nix
{
  description = "Minimal project with straylight nixpkgs";

  inputs = {
    straylight.url = "github:straylight-software/straylight";
    nixpkgs.follows = "straylight/nixpkgs";
    flake-parts.follows = "straylight/flake-parts";
  };

  outputs = inputs@{ flake-parts, straylight, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ straylight.modules.flake.nixpkgs ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];

      straylight.nixpkgs.allow-unfree = true;

      perSystem = { pkgs, ... }: {
        packages.default = pkgs.hello;
      };
    };
}
```
