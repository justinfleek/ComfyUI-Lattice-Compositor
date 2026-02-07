# Le Groupe Wojtan's Graphics of Gravelly Granular Grandeur

This project serves as the reference implementation of the *microscopic* half of the paper *Numerical Homogenization of Sand from Grain-level Simulations*. To use the homogenized materials in a continuum simulation, see [the repository for the *macroscopic* counterpart of the grain homogenization](https://git.ista.ac.at/wojtan-group/yi-lu-chen/lgw-mmmm).

## Table of Contents
1. [Introduction](#introduction)
2. [Build](#how-to-build)
3. [Usage](#usage)

## Introduction

The project consists of the following binaries after compilation:

* `Homogenization`: the main homogenization program with GUI.
* `CLIHomogenization`: command-line-only equivalent.

> :information_source: NOTE
> 
> The GUI program is limited to run at 60 frames per second. For this reason it is recommended to use the CLI program for normal use.


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
* [yaml-cpp](https://github.com/jbeder/yaml-cpp)
* [CNPY](https://github.com/rogersce/cnpy)
* [Dear ImGui](https://www.dearimgui.com/)
* [ImGuiFileDialog](https://github.com/aiekick/ImGuiFileDialog)
* [ImGuizmo](https://github.com/CedricGuillemet/ImGuizmo)
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
git clone --recursive-submodules git@git.ista.ac.at:yichen/homogenized-grains.git
```

In particuar, we use a [custom fork](https://git.ista.ac.at/yichen/cnpy/-/tree/libzip-fixed) of CNPY which fixes its corrupting of NPZ files larger than 4GB (See [this issue](https://github.com/rogersce/cnpy/issues/39)).

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
> Both Nix Shells and Nix builds still require initializing submodules!

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

### Extracting homogenized stresses

If the project was build with nix, either with `nix-shell` or `nix-build` on a *non* NixOS distro, then the produced binaries further require NixGL to run. See [its official github repo](https://github.com/nix-community/nixGL) for setup instructions. Then, execute the binaries with
```
nixGL -- path/to/binaries/Homogenization
```
`Homogenization` requires no arguments, with the input file provided via the file dialog. `CLIHomogenization` receives one arguments:
```
path/to/binaries/CLIHomogenization input.yaml
```

Input files can be found in the `scenes` directory. The options have some overlap with [GGGFFFF](https://git.ista.ac.at/wojtan-group/yi-lu-chen/contactsimulation), but currently there is no documentation for individual homogenization experiments due to the overwhelming number of parameters. Hopefully this will change in the future :(

The homogenized stresses are output directly to `stdout`. To save them to a file, simply redirect the results:
```
path/to/binaries/CLIHomogenization input.yaml > path/to/output.log
```

### Generating homogenized elasticity and plasticity

Once the homogenization process stops, you can output an elasticity model using the provided python script
```
python python/elasticity_batch.py path/to/log/file1.log path/to/log/file2.log [...]
```

The script takes an arbitrary number of arguments, and each added log file is averaged together. The log files averaged therefore need to have the *exact* same procedure preformed for each log file. Similarly, you can generate a plasticity model with
```
python python/mohr_batch.py path/to/log/file1.log path/to/log/file2.log [...]
```

The output models can be directly used in the MPM solver [here](https://git.ista.ac.at/wojtan-group/yi-lu-chen/mpm-codes). 
