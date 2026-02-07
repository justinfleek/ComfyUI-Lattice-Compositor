# Le Groupe Wojtan's Frolic of Frenetic Friction Frenzy

Reference implementation of the paper
[Primal–Dual Non-Smooth Friction for Rigid Body Animation](https://visualcomputing.ist.ac.at/publications/2024/PDNSF/)

* [Project website](https://visualcomputing.ist.ac.at/publications/2024/PDNSF/)
* [Paper](https://pub.ista.ac.at/group_wojtan/projects/2024_Chen_FrictionFrenzy/sig24_friction_authors.pdf)
* [Video](https://pub.ista.ac.at/group_wojtan/projects/2024_Chen_FrictionFrenzy/friction_frenzy_main_video.mp4)

This work proposes a novel friction solver based on the primal–dual interior point method, with a specific focus on *accurate*, *non-smooth* Coulomb friction under *many bodies* and *many contacts*.

## FAQ

### Why a separate library?

Since its publication at ACM SIGGRAPH 2024, the project received several improvements has been used in several other projects. We decided therefore to split the rigid body solver from its graphical user interface and strip down the solver to its bare essentials.

In particular, the following changes and improvements have been made:

* The configuration of the rigid-body solver no longer depends exclusively on YAML.
* A change in friction constraint definition provides better stability and convergence, especially for low friction (μ <= 0.04).
* Contacts are now grouped and solved separately for each connected components. The accuracy of a group of contats will not affect the accuracy and convergence of contacts far away. 
* Baumgarte stabilization (spring-based contacts) now has an extra option to depend on *contact area*.
* Added simulation on *periodic domains*.
* The Dzhanibekov effect is added to spinning rigid bodies. The lack of this was a mistake in the original code, but does not significantly change the algorithm.
* [Suitesparse](https://people.engr.tamu.edu/davis/suitesparse.html) is now used to solve for contact forces in simulations with a moderate number of rigid bodies (from 300 to 10000 bodies). All examples in the original paper now simulate considerably faster than what was reported.
* Signed distance fields for non-convex meshes can now be calculated either with [libigl](https://libigl.github.io)'s AABB tree (as it was in the original implementation) or with [Discregrid](https://github.com/InteractiveComputerGraphics/Discregrid).

> :information_source: NOTE
> 
> For many simulations, Discregrid will not actually provide any speed benefits and will incur an extra initialization overhead.
> On the other hand, Discregrid is more efficient if:
> * the mesh itself is very detailed.
> * there are few meshes.
> * you need to query the signed distance field of a single mesh many times.
> 
> Such a scenario may include, for example, coupling rigid bodies to fluid or MPM simulations.

### What about the GUI?

For the GUI originally part of the project, see [this repository](https://git.ista.ac.at/wojtan-group/yi-lu-chen/contactsimulation). You are of course welcome to write your own if you fancy :p.

### Can I use the original program as published at SIGGRAPH?

There's probably no real benefit to this, but you can find the original code [here](https://git.ista.ac.at/yichen/primal-dual-friction-public)

### Isn't “frenetic” and “frenzy” in the same sentence redundant?

Um…… next.

## Build

Building is tested on both `g++` and `clang++`.

### Dependencies
The programs require the following dependencies installed *on your system*:

* eigen >= 3.4.0
* boost
* suitesparse

Additionally, the following libraries:

* [AMGCL](https://github.com/ddemidov/amgcl)
* [libccd](https://github.com/danfis/libccd)
* [Flexible Collision Library](https://github.com/flexible-collision-library/fcl)
* [libigl](https://libigl.github.io/)
* [Discregrid](https://github.com/InteractiveComputerGraphics/Discregrid)

are included as submodules in the repository. Download them with:
```
git submodule update --init --recursive
```
or, during cloning:
```
git clone --recursive-submodules git@git.ista.ac.at:yichen/frictionfrenzy.git
```
### Including the library in CMake

To add the library in CMake, add the following lines to your `CMakeLists.txt`:
```
add_subdirectory(frictionfrenzy)
set_property(TARGET __ff_FrictionFrenzy APPEND PROPERTY
	INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR}/frictionfrenzy/src)
```
and link to the library with:
```
target_link_library(Your_Application FrictionFrenzy::FrictionFrenzy)
```

In your C++ code, include the library with `#include <FrictionFrenzy.h>`.

More documentation and examples hopefully to come...

