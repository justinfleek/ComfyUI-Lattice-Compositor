To compile with CMake on Windows 64bit, tested with MSVC 2022:
 - Ignore the "windows_dependencies" folder; it is used for setting up the project on Windows without CMake
 - Download freeglut from the "Download freeglut 3.0.0 for MSVC" link on https://www.transmissionzero.co.uk/software/freeglut-devel/ and unpack to a folder of your choosing. (For this document, let's assume it's in "C:/Libraries/", so there should be a folder "C:/Libraries/freeglut/lib" now.)
 - In "C:/Libraries/freeglut/lib", delete "freeglut.lib", and replace it with the version of this file found in the "/x64" subfolder. (You can then delete the "/x64" subfolder.)
 - Download the GLEW "Windows 32-bit and 64-bit" binaries from https://glew.sourceforge.net/index.html and unpack to a folder of your choosing. (We will assume there is now a folder "C:/Libraries/glew-2.1.0/lib".)
 
 - Run CMake in the root folder of the TopoFixer repository (where this readme is located), and set the subfolder "build/" as the build directory. Choose "Visual Studio 17 2022" as the generator, and leave other options empty/default, so x64 is used.
 - During configuration, set a PATH-type variable "CMAKE_PREFIX_PATH" with the value "C:/Libraries/freeglut;C:/Libraries/glew-2.1.0".
 - Finish the CMake configuration and generate the MSVC 2022 solution.
 - Build the projects "mesh_reconstruction" and "mesh_reconstruction_no_visual". This will build the abseil, Triangle, TopoFixer, and TopoFixerRender projects as dependencies. Depending on the configuration (Debug or Release), this will generate a subfolder "build/Debug" or "build/Release" with executables for the "mesh_construction" projects and .dlls for the TopoFixer/TopoFixerRender projects.
 - Copy "freeglut.dll" from the folder "C:/Libraries/freeglut/bin/x64/" and "glew32.dll" from "C:/Libraries/glew-2.1.0/bin/Release/x64" to the folder where the .exe and .dll where generated. (Do this for each configuration.)