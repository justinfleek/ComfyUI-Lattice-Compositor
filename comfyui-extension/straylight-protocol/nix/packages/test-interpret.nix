# Test package demonstrating phases.interpret usage
# This shows how to use typed actions in traditional mkDerivation phases
#
{ pkgs
, straylight
}:

pkgs.stdenv.mkDerivation {
  pname = "test-interpret";
  version = "1.0";

  src = pkgs.writeText "package.json" ''
    {
      "name": "test-interpret",
      "version": "1.0.0"
    }
  '';

  nativeBuildInputs = [
    pkgs.jq
    pkgs.patchelf
  ];

  # Use typed actions in traditional phase
  # This demonstrates incremental adoption: one phase uses typed actions,
  # while the rest of the package remains traditional mkDerivation
  postInstall = straylight.phases.interpret [
    # Jq query action - extract version from package.json
    {
      action = "toolRun";
      pkg = "${pkgs.jq}/bin/jq";
      args = [ "-r" ".version" "$out/package.json" ];
    }
    # PatchElf action - set rpath on binary (if it existed)
    # This is a demonstration - the binary doesn't exist, but shows the pattern
    {
      action = "patchelfRpath";
      path = "bin/test-app";
      rpaths = [ "$out/lib" ];
    }
    # Install action - create a simple binary
    {
      action = "install";
      mode = 755;
      src = "${pkgs.writeScript "test-app" "#!/bin/sh\necho 'test-interpret v1.0.0'\n"}/bin/test-app";
      dst = "bin/test-app";
    }
  ];

  installPhase = ''
    mkdir -p $out
    cp $src $out/package.json
    
    # Create a dummy binary for patchelf test (if patchelf is available)
    if command -v patchelf >/dev/null 2>&1; then
      echo '#!/bin/sh' > $out/bin/test-app
      echo 'echo "test-interpret v1.0.0"' >> $out/bin/test-app
      chmod +x $out/bin/test-app
    fi
  '';

  meta = {
    description = "Test package for phases.interpret - demonstrates incremental adoption";
    homepage = "https://github.com/straylight-software/straylight-protocol";
    license = pkgs.lib.licenses.mit;
    platforms = pkgs.lib.platforms.all;
  };
}
