# Violation: WSN-E002 - mkDerivation rec
{ pkgs }:
pkgs.mkDerivation rec {
  name = "test";
}
