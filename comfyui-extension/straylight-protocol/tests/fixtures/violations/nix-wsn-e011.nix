# Violation: WSN-E011 - nixpkgs.config.* in NixOS
{ config, pkgs, ... }:
{
  nixpkgs.config.allowUnfree = true;
}
