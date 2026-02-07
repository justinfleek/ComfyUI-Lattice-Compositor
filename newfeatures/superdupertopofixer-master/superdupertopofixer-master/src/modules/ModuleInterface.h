/* ModuleInterface.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the module interface. It lists the virtual functions that each module has
 * to implement.
 *
 * TODO:
 * - add functions that will be implemented in child module classes
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <iostream>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../submodules/GridMeshIntersector.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this interface defines functions that modules are required to implement
class ModuleInterface {
 public:
	// constructors
	ModuleInterface() = default;
	virtual ~ModuleInterface() = default;

	// functions

	// virtual functions
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
	                int orientation) = 0;
};
