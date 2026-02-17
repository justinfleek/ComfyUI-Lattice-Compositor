# Test 32: cmake.build (should be OK - exception)

{ pkgs, lib }:

pkgs.mkDerivation (finalAttrs: {
  name = "test";
  
  buildPhase = ''
    cmake.build
  '';
  
  meta = {
    description = "Test";
    license = lib.licenses.mit;
  };
})
