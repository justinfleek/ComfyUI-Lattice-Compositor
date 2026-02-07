# Test 22: CMake in buildInputs (should be caught - still banned)

{ pkgs, lib }:

pkgs.mkDerivation (finalAttrs: {
  name = "test";
  
  # This should be caught - cmake in buildInputs is banned
  buildInputs = [ pkgs.cmake ];
  
  meta = {
    description = "Test";
    license = lib.licenses.mit;
  };
})
