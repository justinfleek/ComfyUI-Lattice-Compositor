# Test package demonstrating CMake typed actions usage
# This shows how to use typed CMake actions in traditional mkDerivation phases
#
{ pkgs
, straylight
}:

let
  # Import CMake tools (in real usage, these come from WASM)
  inherit (straylight.phases) interpret;
in

pkgs.stdenv.mkDerivation {
  pname = "test-cmake";
  version = "1.0";

  src = pkgs.writeTextDir "CMakeLists.txt" ''
    cmake_minimum_required(VERSION 3.10)
    project(test-cmake)

    add_executable(test-app main.cpp)
    install(TARGETS test-app DESTINATION bin)
  '';

  nativeBuildInputs = [
    pkgs.cmake
  ];

  # Use typed CMake actions in traditional phases
  # This demonstrates incremental adoption: one phase uses typed actions,
  # while the rest of the package remains traditional mkDerivation
  preConfigure = interpret [
    #                                                                        // cm
    {
      action = "toolRun";
      pkg = "${pkgs.cmake}/bin/cmake";
      args = [
        "-S" "."
        "-B" "build"
        "-DBUILD_STATIC_LIBS=ON"
        "-DBUILD_SHARED_LIBS=OFF"
        "-DBUILD_TESTING=OFF"
      ];
    }
  ];

  buildPhase = interpret [
    #                                                                        // cm
    {
      action = "toolRun";
      pkg = "${pkgs.cmake}/bin/cmake";
      args = [ "--build" "build" ];
    }
  ];

  installPhase = interpret [
    #                                                                        // cm
    {
      action = "toolRun";
      pkg = "${pkgs.cmake}/bin/cmake";
      args = [ "--install" "build" "--prefix" "$out" ];
    }
  ];

  # Create a dummy main.cpp for the test
  postUnpack = ''
    mkdir -p $sourceRoot
    cat > $sourceRoot/main.cpp << 'EOF'
    #include <iostream>
    int main() {
      std::cout << "test-cmake v1.0.0" << std::endl;
      return 0;
    }
    EOF
  '';

  meta = {
    description = "Test package for CMake typed actions - demonstrates incremental adoption";
    homepage = "https://github.com/straylight-software/straylight-protocol";
    license = pkgs.lib.licenses.mit;
    platforms = pkgs.lib.platforms.all;
  };
}
