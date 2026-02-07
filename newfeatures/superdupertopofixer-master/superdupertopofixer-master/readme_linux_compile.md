- Update submodules
```sh
git submodule update --init
```
- Install freeglut, glew and xkbcommon libraries. 
```sh
sudo apt-get install freeglut3-dev libglew-dev libxkbcommon-dev
```
- Use CMake as usual to build the project. 
```sh
mkdir build
cd build
cmake ..
cmake --build .
```