# Test 21: CMake in exception contexts (should be allowed)
# But cmake elsewhere should be caught

{ pkgs, lib }:

pkgs.mkDerivation {
  name = "test";
  
  # These should be OK (exceptions):
  cmakeFlags = [ "-DCMAKE_BUILD_TYPE=Release" ];
  nativeBuildInputs = [ pkgs.cmake ];
  
  configurePhase = ''
    cmake.configure
    cmake.build
  '';
  
  # This should be caught:
  buildInputs = [ pkgs.cmake ];  -- Using cmake package
}
