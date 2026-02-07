# Le Groupe Wojtan's Marvel of Meticulous MPM Mayhem

An *explicit* material-point method solver, using the [Moving Least Square MPM](https://yuanming.taichi.graphics/publication/2018-mlsmpm/) discretization.

This project serves as the macroscopic half of the paper *Numerical Homogenization of Sand from Grain-level Simulations*, though hopefully it can serve a generic MPM solver as well. See also [the repository for the *microscopic* counterpart of grain homogenization](https://git.ista.ac.at/wojtan-group/yi-lu-chen/lgw-gggg).

## Features
* A new plastic flow algorithm, as detailed in our paper.
* Generalized elasticity and plasticity models based on homogenized data of sand simulations.
* Explicit MPM solver with adaptive timestepping with method by [Sun et al.](https://doi.org/10.1111/cgf.14101).
* Two-way rigid body coupling with [Hu et al.](https://yuanming.taichi.graphics/publication/2018-mlsmpm/)'s method and [Chen et al.](https://git.ista.ac.at/wojtan-group/yi-lu-chen/frictionfrenzy)'s rigid body solver.
* Sparse block grid inspired by [Braun et al.](https://ge.in.tum.de/publications/very-large-scale-two-phase-flip/)
* An parallel, atomic operation-free particle-to-grid routine.
* Advection:
    * [APIC](https://dl.acm.org/doi/10.1145/2766996)
    * [ASFLIP](https://raymondyfei.github.io/asflip/)
* Elasticity models:
    * [Fixed corotated linear elasticity](https://dl.acm.org/doi/10.5555/2422356.2422361)
    * [St. Vernant–Kirchhoff elasticity with Hencky strain](https://dl.acm.org/doi/10.1145/2897824.2925906)
    * Generalized Hencky strain elasticity
* Plasticity models:
    * Deformation-based:
        * Eulerian fluid
        * Snow [(Stomakhin et al.)](https://doi.org/10.1145/2461912.2461948)
    * Stress-based:
        * Drucker–Prager
        * Mohr–Coulomb
        * Generalized Mohr–Coulomb
* Volume correction:
    * Volume change compensation ([Tampubolon et al.](https://doi.org/10.1145/3072959.3073651))
    * Density-based deformation enforcement ([Gao et al.](https://doi.org/10.1145/3197517.3201309))
* Export particles to Stanford PLY with deformation information.

## Limitations

Currently only one material is allowed per simulation.

## Build
Building is tested on both `g++` and `clang++`.

### Dependencies
The programs require the following dependencies installed *on your system*:

* eigen >= 3.4.0
* glfw3
* libzip
* boost
* libX11
* suitesparse

Additionally, the following libraries:

* [FrictionFrenzy](https://git.ista.ac.at/wojtan-group/yi-lu-chen/frictionfrenzy) (and its dependencies)
* [libigl](https://libigl.github.io)
* [rapidjson](https://rapidjson.org)
* [Dear ImGui](https://www.dearimgui.com/)
* [Magnum](https://magnum.graphics)
	* corrade
	* magnum-intergration
	* magnum-plugins

are included as submodules in the repository. Download them with:
```
git submodule update --init --recursive
```
or, during cloning:
```
git clone --recursive-submodules git@git.ista.ac.at:yichen/mpm-codes.git
```
From here on, there are three ways to build the package.

### CMake (Tested on Ubuntu 22.04 and NixOS)

1. Install the system dependencies. For Ubuntu users, run
```
sudo apt install cmake libeigen3-dev libglfw3-dev libzip-dev libboost-dev libx11-dev libsuitesparse-dev
```
The correct OpenMP implementation is also required for the project to compile with Clang. On Ubuntu 22.04 it is named `libomp-dev`.

2. Configure and build the project with CMake and make.  
```
mkdir build
cd build
cmake ../
make -j
```

For NixOS users, the extra `BUILD_NIX_PACKAGE` flag must be set:
```
cmake -DBUILD_NIX_PACKAGE=ON ../
```

After compilation, the binaries should be found under `./Release/bin/`.

### Nix shell
You can also temporarily install all system dependencies using the [Nix package manager](https://nixos.org/). With Nix installed, simply go to the project root folder and run
```
nix-shell
```
or, if flakes are enabled:
```
nix develop
```

This creates a development shell in which all dependencies are installed. Now we can proceed with the build process:
```
mkdir build
cd build
cmake ../ #-DBUILD_NIX_PACKAGE still needed for NixOS!
make -j
```

> :information_source: NOTE
> 
> Both Nix Shells and Nix builds still require iniializing submodules!

### Nix build

You can also build the entire project as a Nix package by running from the project root:
```
nix-build
```
Nix will build and install the project under `./result/*`.

#### Using flakes
Nix flakes by default do not allow git submodules in packages. With the respective submodules pulled, run `nix build` with the following query to compile the nix package:
```
nix build ".?submodules=1#"
```
This works with version 2.28.3, which is the latest stable version in nixpkgs as of June 2025.

`BUILD_NIX_PACKAGE=ON` is automatically set in `default.nix`, and no further configuration should be required.

## Usage
Run a simulation with 
```
./Release/bin/mpm3DApp /path/to/config.jsonc
```
A corresponding GUI-less application named `CLImpm3DApp` can also be used.

The config file format is `jsonc` (JSON with comments and trailing commas). Some examples of config files can be found in `configs/`, with `configs/rigid_body_test/rigid_body_test.jsonc` exposing most of the options available.

## Contributors

* Mickaël Ly
* Yi-Lu Chen

