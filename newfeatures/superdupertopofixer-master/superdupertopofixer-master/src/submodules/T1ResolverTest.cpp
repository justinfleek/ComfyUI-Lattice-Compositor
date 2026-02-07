#include "datastructures/Grid3DSparseCubical.h"
#include "datastructures/GridMeshIntersection.h"
#include "submodules/T1Resolver.h"
#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include <iostream>

#include "../datastructures/Mesh3DCornerTable.h"
#include "../datastructures/mesh_io/ObjFileHandler.h"
#include "../utilities/doctest/doctest.h"

size_t getNumMaterials(const Mesh3DCornerTable& mesh) {
	size_t max_mats = 0;
	for (Mesh3DVertex* v : mesh.ListVertices()) {
		absl::flat_hash_set<int> mats;
		for (Mesh3DHalfCorner* hfc : mesh.getHalfCornersAtVertex(v)) {
			mats.insert(hfc->getLabel());
		}
		max_mats = std::max(max_mats, mats.size());
	}
	return max_mats;
}

TEST_CASE("T1Resolver resolves the vertices") {
	TopoFixerSettings settings;
	Mesh3DCornerTable mesh(settings);
	ObjFileHandler reader;
	reader.readFromFile(&mesh, "testinputs/degenerate/4_cubes_share_a_vertex.obj");

	Grid3DSparseCubical dummy_grid;

	CHECK_EQ(getNumMaterials(mesh), 5);

	settings.allow_area_increasing_t1 = true;
	T1Resolver resolver(settings);
	resolver.resolveVertices(mesh, dummy_grid, mesh.ListVertices());

	CHECK_EQ(getNumMaterials(mesh), 4);
}
