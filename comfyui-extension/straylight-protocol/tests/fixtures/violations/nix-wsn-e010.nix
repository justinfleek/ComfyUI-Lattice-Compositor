# Violation: WSN-E010 - Per-flake nixpkgs config
import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/master.tar.gz") {
  config = { };
}
