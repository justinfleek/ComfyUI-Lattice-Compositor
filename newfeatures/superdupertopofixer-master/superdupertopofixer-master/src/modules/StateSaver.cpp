/* StateSaver.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2022
 *
 * A module that saves and restores the internal state of Grid and Mesh during algorithm execution.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include "StateSaver.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// NOTE: One potential potential optimization to consider:
// We will always save the mesh. But we will not load it unless something bad happens.
// Because we expect bad events happening more rarely than the good ones, it makes sense to offload
// heavier tasks to the load function. For example, updating the mesh pointers on the grid can be
// combined in one step in the load function. The result code will be messier but the trade-off
// might be worth it.

void StateSaver::save(Grid3DSparseCubical grid, Mesh3DCornerTable& mesh) {
	grid_ = std::move(grid);
	mesh_save_state_ = mesh.getCurrentSaveState();
	grid_.update_mesh_pointers(mesh_save_state_);
	if (settings->verbosity >= 1) {
		std::cout << "state saved" << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
}

void StateSaver::load(Grid3DSparseCubical& grid, Mesh3DCornerTable& mesh) const {
	Mesh3DSaveState idx_to_pointers = mesh.restoreFromSaveState(mesh_save_state_);
	grid = grid_;
	grid.update_mesh_pointers(idx_to_pointers);
	if (settings->verbosity >= 1) {
		std::cout << "state loaded" << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
}