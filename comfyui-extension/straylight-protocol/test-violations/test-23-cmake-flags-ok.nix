# Test 23: CMake flags (should be OK - exception)

{ pkgs, lib }:

pkgs.mkDerivation (finalAttrs: {
  name = "test";
  
  # This should be OK - cmakeFlags is exception
  cmakeFlags = [ "-DCMAKE_BUILD_TYPE=Release" ];
  
  meta = {
    description = "Test";
    license = lib.licenses.mit;
  };
})
