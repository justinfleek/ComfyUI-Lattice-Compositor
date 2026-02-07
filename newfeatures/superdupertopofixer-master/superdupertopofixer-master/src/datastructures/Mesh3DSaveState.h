/* Mesh3DSaveState.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * The structure to represent the state of the mesh data structure in a format suitable for long
 * term storage.
 *
 *
 */
#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <unordered_map>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// A structure to hold a snapshot of the mesh, namely information about vertices, triangles,
// half-corners, and their connectivity, in a persistent way. This means that objects themselves are
// stored instead of just pointers.

// The structure can be used for other derived classes of Mesh3DInterface. Such mesh implemetations
// then define which fields to use and how in their getCurrentSaveState and restoreFromSaveState
// functions. As such, the structure is not optimized for storage.
class Mesh3DSaveState {
 public:
	// Index conversion maps used to associate a pointer to a primitive with its vector index in the
	// save state arrays when saving, and a vector index in a save state array with a pointer to a
	// primitive when loading. Both indices and pointers are represented as the same type for
	// convenience, one can be obtained from the other by recasting (eg. to obtain the array index
	// from a pointer, it is enough to recast the pointer to an intergal value). These maps should be
	// used to maintain correct associations among mesh primitives (eg. next() value of a halfcorner).
	absl::flat_hash_map<Mesh3DVertex*, Mesh3DVertex*> vertices_indices;
	absl::flat_hash_map<Mesh3DTriangle*, Mesh3DTriangle*> triangles_indices;
	absl::flat_hash_map<Mesh3DHalfCorner*, Mesh3DHalfCorner*> hfc_indices;

	// Save state arrays, these vectors contains all the data of the mesh primitives.
	std::vector<Mesh3DVertex> vertices;
	std::vector<Mesh3DTriangle> triangles;
	std::vector<Mesh3DHalfCorner> half_corners;
};