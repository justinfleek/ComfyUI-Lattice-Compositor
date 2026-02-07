/* MeshSewer.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the module that sews the remeshed and the non-remeshed
 * triangles together.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "MeshSewer.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// function that coordinates the run of the mesh sewer module
// TODO: reimplement
int MeshSewer::run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersection,
                   int orientation) {
	int return_value = 0;

	if (settings->verbosity >= 1) {
		std::cout << "-mesh sewer finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}
