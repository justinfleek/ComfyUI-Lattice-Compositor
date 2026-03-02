# nix/overlays/pure-sarcasm.nix
#
# PureScript WASM backend (pure-sarcasm) overlay
#
# pure-sarcasm is an experimental Wasm-GC backend for PureScript.
# This overlay provides a Nix package for it.
#
# Source: https://github.com/ajnsit/pure-sarcasm
#
{ pkgs, lib, ... }:
let
  # Build pure-sarcasm from source
  # NOTE: This is experimental and may need adjustments based on actual build process
  pure-sarcasm = pkgs.buildNpmPackage rec {
    pname = "pure-sarcasm";
    version = "0.1.0"; # Update when actual version is known

    src = pkgs.fetchFromGitHub {
      owner = "ajnsit";
      repo = "pure-sarcasm";
      # Use latest commit or specific tag when available
      rev = "main"; # TODO: Pin to specific commit/tag
      hash = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="; # TODO: Update with actual hash
    };

    npmDepsHash = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="; # TODO: Update with actual hash

    # Build the PureScript WASM compiler
    buildPhase = ''
      runHook preBuild
      
      # Install dependencies
      npm install
      
      # Build pure-sarcasm
      npm run build || true  # May not have build script yet
      
      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall
      
      # Install the purs-sarcasm binary
      mkdir -p $out/bin
      
      # The exact binary name/location depends on pure-sarcasm's structure
      # This is a placeholder - adjust based on actual output
      if [ -f "dist/purs-sarcasm.js" ]; then
        # Node.js-based compiler
        cat > $out/bin/purs-sarcasm <<EOF
      #!${pkgs.nodejs}/bin/node
      ${lib.readFile ./dist/purs-sarcasm.js}
      EOF
        chmod +x $out/bin/purs-sarcasm
      elif [ -f "bin/purs-sarcasm" ]; then
        # Pre-built binary
        cp bin/purs-sarcasm $out/bin/purs-sarcasm
        chmod +x $out/bin/purs-sarcasm
      else
        # Fallback: create a stub that explains the situation
        cat > $out/bin/purs-sarcasm <<EOF
      #!/bin/sh
      echo "pure-sarcasm build not yet complete"
      echo "See: https://github.com/ajnsit/pure-sarcasm"
      echo ""
      echo "To use PureScript packages, add pure-sarcasm to your overlay"
      echo "or use Haskell (.hs) files instead - same API."
      exit 1
      EOF
        chmod +x $out/bin/purs-sarcasm
      fi
      
      runHook postInstall
    '';

    meta = with lib; {
      description = "PureScript Wasm-GC backend (experimental)";
      homepage = "https://github.com/ajnsit/pure-sarcasm";
      license = licenses.mit; # TODO: Verify actual license
      maintainers = [ ];
      platforms = platforms.all;
    };
  };
in
{
  # Add pure-sarcasm to pkgs
  pure-sarcasm = pure-sarcasm;
}
