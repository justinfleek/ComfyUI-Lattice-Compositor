/* StateSaver.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2022
 *
 * A module that saves and restores the internal state of Grid and Mesh during algorithm execution.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "../datastructures/Grid3DSparseCubical.h"
#include "../datastructures/Mesh3DCornerTable.h"
#include "../datastructures/Mesh3DSaveState.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// StateSaver saves and restores the internal state of the two main datastructures of the algorithm:
// mesh and grid. This module can be used to roll back an unsuccessful operation that changed grid
// or mesh primitives.
// The grid is saved directly as a copy of the same object. The mesh is saved using an instance of
// Mesh3DSaveState that the class provides. Saving MeshCornerTable directly as a copy of an object
// wouldn't work, because mesh primitives are allocated on the heap and pointers between them become
// invalidated when copied. StateSaver also takes care of correctly updating mesh pointers saved
// within grid datastructures that are invalidated during saving and loading operations.
// NOTE: if new data structures on the grid holding pointers to mesh primitives are added, it is
// necessary to add an update rule for these pointers into function update_mesh_pointers in the grid
// class.

// TODO: This class breaks the module convention as there is no explicit run function. It also
// accepts concrete implementations of grid and mesh instead of generic interfaces. This should be
// considered if mesh or grid implementations ever become expanded to other types.
class StateSaver {
 public:
	StateSaver(const TopoFixerSettings& settings) : settings(&settings) {}
	void save(Grid3DSparseCubical grid, Mesh3DCornerTable& mesh);
	void load(Grid3DSparseCubical& grid, Mesh3DCornerTable& mesh) const;

 private:
	const TopoFixerSettings* settings;
	Grid3DSparseCubical grid_;
	Mesh3DSaveState mesh_save_state_;
};