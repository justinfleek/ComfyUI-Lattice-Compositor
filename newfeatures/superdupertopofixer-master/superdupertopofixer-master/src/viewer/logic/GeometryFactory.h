#pragma once

#include <absl/container/flat_hash_set.h>

#include <Eigen/Core>

#include "LinearMesh3DView.h"
#include "datastructures/Grid3DInterface.h"
#include "gl/LineMesh.h"
#include "gl/TriangleMesh.h"

// The GeometryFactory class uses the mesh and grid data from the TopoFixer application to generate
// gl::TriangleMesh and gl::LineMesh data that can be displayed in the application.

namespace sdtf::viewer::logic {
;
class GeometryFactory {
 public:
	GeometryFactory(const LinearMesh3DView& mesh, const Grid3DInterface& grid);

	// Turns the mesh data structure into a triangle mesh, with face indices (starting at
	// index_offset), and per-label colors. The face_color_perturbation parameter adds a bit of color
	// noise to each face color to make two adjacent faces easier to distinguish in the absence of
	// lighting.
	std::unique_ptr<gl::TriangleMesh> makeTriangleMesh(float face_color_perturbation = 0.0f,
	                                                   unsigned int index_offset = 0u);
	// Returns a line mesh of the mesh data structure
	std::unique_ptr<gl::LineMesh> makeLineMesh();

	// Returns a mesh representation of the boundary of the complex cell region. This consists of a
	// line mesh representing every edge in the boundary, and a triangle mesh that contains a square
	// for each face. All these faces are linearly renumbered, such that the i-th face has id
	// face_ids[i]. The index buffer of the triangle_mesh contains the index i+index_offset (use the
	// index_offset to distinguish grid face indices from mesh face indices).
	void makeComplexCellSetBoundaryMeshes(std::unique_ptr<gl::TriangleMesh>* triangle_mesh,
	                                      std::unique_ptr<gl::LineMesh>* line_mesh,
	                                      std::vector<long long>* face_ids,
	                                      unsigned int index_offset = 0u);

 private:
	void initColors();

	// Returns the ids of all faces that constitute the boundary of a subset of cells, and triangles
	// consistuting the face are oriented outwards. This excludes faces shared by two cells in this
	// set.
	std::vector<std::tuple<long long, Eigen::Vector3d, Eigen::Matrix<double, 3, 2>>>
	getCellSetBoundaryFaces(const absl::flat_hash_set<long long>& cells);

	std::vector<Eigen::Vector3f> mesh_color_map_;

	const LinearMesh3DView* mesh_;
	const Grid3DInterface* grid_;
};

}  // namespace sdtf::viewer::logic