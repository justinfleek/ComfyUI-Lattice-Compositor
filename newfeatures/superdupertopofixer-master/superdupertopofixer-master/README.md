# Multi-Material Mesh-Based Surface Tracking with Implicit Topology Changes

A robust surface tracking library that handles topology changes in large non-manifold meshes with arbitrary deformations.

The main use case of the library is to support simulations with non-manifold surface meshes. The simulation code advects the mesh, putting it into the entangled state. Our surface tracking resolves
the entanglements and provides a clean mesh ready for the next step of the simulation. Addtionally, the algorithm handles mesh overlaps and self-inversions for static meshes, so it can also be used to compute approximate mesh booleans. 

The tracker was first presented in "Multi-Material Mesh-Based Surface Tracking with Implicit Topology Changes" at ACM SIGGRAPH 2024.

- [Project page](https://visualcomputing.ist.ac.at/publications/2024/SDTF/)
- [Paper (48MB)](https://pub.ista.ac.at/group_wojtan/projects/2024_MultimatMeshing/SuperDuperTopoFixer.pdf)

## Building the project
Refer to [Windows](readme_windows_compile.txt) or [Linux](readme_linux_compile.md) instructions to build the project. The examples below assume that you have successfully compiled `mesh_reconstruction` binary.

## Reproducibility
If you plan to use this library in your project, we recommend to use the `master` branch which contains most up-to-date version of the project with all the performance improvements and bug fixes.

If you want to test specifically the version of the code which was used to generate examples in the original paper, you should switch to `v1.0.0` tag. 

## Running examples

### General approach
The surface tracker is run by invoking `TopoFixerViewer` (with GUI) or `TopoFixer` binaries (just command-line) with the correct parameter file. 

Most of the examples have one config file stored in the `configs` directory. Contents of the config will inform you about the input file and custom parameters being used for this example. 
The full list of parameters can be viewed in [src/binaries/parameters.h](src/schemes/TopoFixerSettings.h).

To run an example that saves outputs, make sure to create an output directory where the output files will be written. Otherwise, the simulation will run but won't write any outputs onto a disk. 

### Three overlapping balls
This example demostrates how the surface tracker works on a static input. 
The main config is located in `configs/three_balls.cfg`. The provided obj file specifies three spheres of different materials that overlap. You can think of it as a snapshot coming out of the external simulation.  
The binary loads the file, runs the surface tracking pipeline on it and visualizes the output without creating any output file.

This example checks that all steps of the pipeline work as expected.
For real simulations it is better to use the surface tracker as a library and communicate with it via API due to loss of precision when serializing to ASCII files.


```sh
./build/TopoFixerViewer -input_params=configs/three_balls.cfg
```

### Curl noise
Curl noise example takes 4 non-overlapping spheres of different materials as the initial configuration and sends them through a divergence-free field. 

```sh
mkdir -p outputs/curlnoise
./build/TopoFixerViewer -input_params=configs/curlnoise.cfg
```

Find the outputs in `outputs/curlnoise`. If there are no outputs, make sure you created the correct directory before running our mesher.

### Dr. Krabunkle

We start with a base input mesh `testinputs/crab.obj` which was cleaned from duplicate triangles. This crab mesh has its legs represented as separate components overlapping with the body.

Firstly, let's generate a correctly separated non-manifold mesh with the legs properly attached. 

```sh
mkdir -p outputs/crab
./build/TopoFixerViewer -input_params=configs/crab.cfg
```

These commands will produce a resolved mesh at `outputs/crab/crab_multimaterial.obj`.


Secondly, we clone the crab to produce Dr. Krabunkle mesh with overlaps.

```sh
./build/TopoFixerViewer -input_params=configs/crabunkle_multiply.cfg
```


Finally, Dr. Krabunkle assumes its final separated form with the help of our mesher. 

```sh
./build/TopoFixerViewer -input_params=configs/crabunkle_intersect.cfg
```

## Viewer commands

Mouse options are:
* Drag MMB: Orbit camera
* Shift+Drag MMB: Pan camera
* Shift+Ctrl+Drag MMB: Dolly camera
* Wheel: zoom
* LMB: Select mesh face, or grid face on the boundary of the complex cell region

The keyboard shortcuts are:
* R: reset camera location
* M: cycle mesh visualization
* G: cycle grid visualization (boundary of complex cell region)
* . and , : next/prev half corner
* T: twin half corner
* O: opposite half corner
* 1-4: switch grid element selection to vertex/edge/face/cell
* 2, 3: repress to change orientation of selected grid edge/face
* X, Shift+X, Y, Shift+Y, Z, Shift+Z: move currently selected grid element along axis
* Enter: Open command line
* C: Enter clipping plane mode. Enables:
  * X, Y, Z: align clipping plane with coordinate plane. Repress to switch orientation
  * Move mouse up/down: move clipping plane
  * C: Make clipping plane parallel to camera plane. Repress to switch orientation
  * Escape: Reset clipping to previous state
  * LMB, Enter: Confirm
  * RMB, Delete: Disable clipping plane
* S: Start/Step.
  * `Fixer` configuration: run the full process
  * `Scene` configuration: run n steps if interactive_mode_steps>0, otherwise runs the full process
* P: Pause toggle.
  * `Interactive` configuration: run the full simulation, update the viewer every interactive_mode_steps steps
* Esc x2: Quit

Commands line commands are:
* sg {v|e|f|c} id: to select grid element
* sm {v|h|f} id: to select mesh element (this is based on my implementation of a linear view of the loaded mesh; but we can switch it over your linear mesh eventually)
* unload: unloads the scene
* load path: runs the specified parameter file and loads the result

## Citation
```
@article{MultimaterialMeshing24,
  author = {Heiss-Synak, Peter and Kalinov, Aleksei and Strugaru, Malina and Etemadi, Arian and Yang, Huidong and Wojtan, Chris},
  title = {Multi-Material Mesh-Based Surface Tracking with Implicit Topology Changes},
  year = {2024},
  issue_date = {October 2024},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  volume = {43},
  number = {4},
  journal = {ACM Trans. Graph.},
  month = {sep},
  articleno = {171},
  numpages = {14},
  keywords = {surface tracking, topology change, nonmanifold meshes, multi-material flows, solid modeling}
}
```