# Test 31: cmake.configure (should be OK - exception)

{ pkgs, lib }:

pkgs.mkDerivation (finalAttrs: {
  name = "test";
  
  configurePhase = ''
    cmake.configure
  '';
  
  meta = {
    description = "Test";
    license = lib.licenses.mit;
  };
})
