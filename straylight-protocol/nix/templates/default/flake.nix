{
  description = "Project powered by straylight-naught";

  inputs = {
    straylight-naught.url = "github:straylight-software/straylight-naught";
    nixpkgs.follows = "straylight-naught/nixpkgs";
    flake-parts.follows = "straylight-naught/flake-parts";
  };

  outputs =
    inputs@{ flake-parts, straylight-naught, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ straylight-naught.modules.flake.default ];
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];

      straylight-naught = {
        formatter.enable = true;
        devshell.enable = true;
        nixpkgs.allow-unfree = true;
      };

      perSystem =
        { config, pkgs, ... }:
        let
          # The Weyl Prelude is available via config.straylight.prelude
          inherit (config.straylight) prelude;
          inherit (prelude)
            stdenv
            fetch
            render
            license
            ;
        in
        {
          packages.default = pkgs.hello;

          # Example using prelude
          # packages.my-tool = stdenv.default {
          #   pname = "my-tool";
          #   version = "0.1.0";
          #
          #   src = fetch.github {
          #     owner = "me";
          #     repo = "my-tool";
          #     rev = "v0.1.0";
          #     hash = "sha256-...";
          #   };
          #
          #   meta = {
          #     description = "My tool";
          #     license = license.mit;
          #   };
          # };
        };
    };
}
