# Valid Nix file - follows all rules
{ pkgs, lib }:
pkgs.mkDerivation (finalAttrs: {
  name = "test-package";
  meta = {
    description = "A test package";
    license = lib.licenses.mit;
    main-program = "test";
  };
})
