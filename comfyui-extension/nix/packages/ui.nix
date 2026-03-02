{
  lib,
  bun2nix,
  bun,
  nodejs_20,
}:

# Use bun2nix v2 API: mkDerivation with fetchBunDeps
bun2nix.mkDerivation {
  pname = "lattice-compositor-ui";
  version = "1.0.0";

  src = lib.cleanSourceWith {
    src = ./../../ui;
    filter =
      path: _type:
      let
        base-name = baseNameOf path;
      in
      base-name != "node_modules"
      && base-name != "dist"
      && base-name != ".git"
      && base-name != "bun.lock"
      && base-name != "package-lock.json";
  };

  # bun2nix v2: fetchBunDeps requires bunNix file
  # For now, we'll need to generate bun.nix from bun.lock first
  # This can be done with: nix run github:nix-community/bun2nix -- bun2nix ui/bun.lock > ui/bun.nix
  # For now, using a placeholder - will need to generate bun.nix file
  bunDeps = bun2nix.fetchBunDeps {
    bunNix = ./../../ui/bun.nix;
  };

  nativeBuildInputs = [
    bun
    nodejs_20
  ];

  buildPhase = ''
    runHook preBuild

    # Build the UI (dependencies are handled by bun2nix)
    bun run build

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    # Copy build output
    mkdir -p $out
    cp -r dist/* $out/

    runHook postInstall
  '';

  meta = {
    description = "Lattice Compositor UI";
    homepage = "https://github.com/weyl-ai/lattice-compositor";
    license = lib.licenses.mit;
    maintainers = [ ];
  };
}
