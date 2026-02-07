{
  description = "Minimal project with straylight-naught nixpkgs";

  inputs = {
    straylight-naught.url = "github:straylight-software/straylight-naught";
    nixpkgs.follows = "straylight-naught/nixpkgs";
    flake-parts.follows = "straylight-naught/flake-parts";
  };

  outputs =
    inputs@{ flake-parts, straylight-naught, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ straylight-naught.modules.flake.nixpkgs ];
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
        "x86_64-darwin"
      ];

      straylight-naught.nixpkgs.allow-unfree = true;

      perSystem =
        { pkgs, ... }:
        {
          packages.default = pkgs.hello;
        };
    };
}
