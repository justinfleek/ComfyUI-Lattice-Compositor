/* MeshSewer.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the module that sews the remeshed and the non-remeshed triangles together.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "ModuleInterface.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the mesh sewer module
class MeshSewer : public ModuleInterface {
 public:
	// constructors
	MeshSewer(const TopoFixerSettings& settings) : settings(&settings){};
	virtual ~MeshSewer() = default;

	// functions
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersection,
	                int orientation) override;

	private:
	const TopoFixerSettings* settings;
};
