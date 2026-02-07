/* Mesh3DCornerTableManipulation.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru
 *
 * This is the implementation file for the mesh corner table, containing implementations of
 * functions related to manipulating the mesh.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <algorithm>

#include "Mesh3DCornerTable.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

//------------------------------------------------------------
// construct mesh data structures
//------------------------------------------------------------

// return a map that to each `TriSide` adjacent to `vertex` assigns its local region index
absl::flat_hash_map<Mesh3DInterface::TriSide, size_t>
Mesh3DCornerTable::uniteTrianglesInLocalRegions(
    Mesh3DVertex* vertex, const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
    int& num_regions) const {
	// helper map used to union `TriSide`s within the same manifold neighborhoods
	absl::flat_hash_map<Mesh3DTriangle*, size_t> initial_components;
	int current_index = 0;
	// assign to each pair (triangle,label) adjacent to `vertex` a unique index
	initial_components.reserve(triangles.size());
	for (Mesh3DTriangle* triangle : triangles) {
		initial_components.try_emplace(triangle, current_index);
		current_index += 2;
	}

	// union all (triangle,label) pairs in the same manifold neighborhood of `vertex` (same local
	// region)
	current_index = 0;
	UnionFind union_find(2 * initial_components.size());
	for (Mesh3DTriangle* triangle : triangles) {
		Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
		// iterate over both sides of `triangle`
		for (int i = 0; i < 2; ++i) {
			// iterate over both adjacent half-corners of `hfc` in `triangle`;
			// NOTE: this should also work if the loop is removed and the `getNext` in the line after the
			// loop is changed into `getPrev`, i.e. we always only union one neighbor of `triangle` per
			// side (and always in the same direction on the same side, forming a "circle")
			for (int j = 0; j < 3; ++j, hfc = hfc->getNext()) {
				if (hfc->getVertex() == vertex) {
					continue;
				}
				// retrieve the HC opposite of `hfc`; by construction, it is in the 1-neighborhood of
				// `vertex`
				Mesh3DHalfCorner* neigh_hfc = hfc->getOppos();
				size_t idx1 = current_index + hfc->getLabelSide();
				size_t idx2 = initial_components[neigh_hfc->getTri()] + neigh_hfc->getLabelSide();
				// union the indices of the two neighboring `TriSide`s
				union_find.Union(idx1, idx2);
			}
			hfc = hfc->getNext()->getDual();
		}
		current_index += 2;
	}

	// return map, that assigns a unique index (identifying a manifold neighborhood (local region) of
	// `vertex`), to `TriSide`s within this manifold neighborhood; indices are contiguous, starting
	// from zero
	absl::flat_hash_map<TriSide, size_t> result;
	// conversion map that sends a representative of a set in the Union-Find DS (which are all
	// integers) to its local region index
	absl::flat_hash_map<size_t, size_t> old_to_new_regions;
	// keeps track of the next contiguous local region index to assign
	int current_region = 0;
	// used to iterate over indices of `TriSide`s that are stored in `initial_components`
	current_index = 0;
	// iterate over `triangles`, assign to each `TriSide` a local region index, where the indices are
	// contiguous integers from 0
	result.reserve(triangles.size() * 2);
	for (Mesh3DTriangle* triangle : triangles) {
		// iterate over both sides of `triangle`
		for (int side_idx = 0; side_idx < 2; ++side_idx) {
			// find the integer representative of one of the two `TriSide`s of `triangle`
			size_t union_region = union_find.Find(current_index + side_idx);
			// map the representative to the next available local region index (stored in
			// `current_region`)
			auto [it, is_inserted] = old_to_new_regions.emplace(union_region, current_region);
			// if `union_region` was inserted (this representative hasn't been encountered before),
			// increase the next available local region index number
			current_region += is_inserted;
			// map the current triangle side either to `union_region` (if `union_region` has been
			// inserted, i.e. this is the first time we encountered this representative), or to the local
			// region index already associated with the representative of current triangle side
			result[{triangle, triangle->getLabel(side_idx)}] = it->second;
		}
		current_index += 2;
	}
	num_regions = current_region;
	return result;
}

void Mesh3DCornerTable::orderRegionsByLabels(absl::flat_hash_map<TriSide, size_t>& regions) const {
	// vector that stores pairs (label,local region index); there will be one entry per local region;
	// there can be multiple entries with the same label (if there are multiple local regions with the
	// same label)
	std::vector<std::pair<size_t, size_t>> labels_and_regions;
	// set of regions for which we already stored their (label,region) pair
	absl::flat_hash_set<size_t> processed_regions;
	// fill in the vector `labels_and_regions` using data in the already computed `result`
	for (auto& [side, region] : regions) {
		if (!processed_regions.count(region)) {
			processed_regions.insert(region);
			labels_and_regions.push_back({side.second, region});
		}
	}
	// sort entries in `labels_and_regions` by their labels (which are non-negative, possibly
	// non-consecutive integers)
	std::sort(labels_and_regions.begin(), labels_and_regions.end(),
	          [&](const std::pair<size_t, size_t>& a, const std::pair<size_t, size_t>& b) {
		          return (a.first < b.first);
	          });
	// vector of integers that we fill with values 0,..,labels_and_regions.size()-1; it will store the
	// permutation needed to reassign local region indices in `result`
	std::vector<size_t> permutation;
	permutation.reserve(labels_and_regions.size());
	for (size_t i = 0; i != labels_and_regions.size(); i++) {
		permutation.push_back(i);
	}
	// sort entries in vector `permutation` such that entry `a` is smaller than entry `b` iff in
	// vector `labels_and_regions` the region at index `a` is smaller than the region at index `b`;
	// this results in vector `permutation` holding the permutation needed to go from current local
	// region indices, to local region indices sorted by labels of local regions; for example,
	// `permuation[i]=j` means that local region `i` has `j`-th lowest label among local regions
	// around `vertex`, and therefore would have index `j` if we assigned local region indices in the
	// increasing order of local region labels (i.e. regions with lower labels have lower indices)
	std::sort(permutation.begin(), permutation.end(), [&](const size_t& a, const size_t& b) {
		return (labels_and_regions[a].second < labels_and_regions[b].second);
	});
	// iterate over pairs (`TriSide`,region) in `result`, and apply the calculated permutation to
	// region values
	for (auto& [side, region] : regions) {
		region = permutation[region];
	}
}

// return the adjacency matrix of local regions around center vertex (the vertex common to all
// `triangles`)
std::vector<std::vector<int>> Mesh3DCornerTable::buildRegionsMatrix(
    const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
    const absl::flat_hash_map<Mesh3DInterface::TriSide, size_t>& sides_to_regions,
    const int num_regions) const {
	// construct the adjacency matrix by initializing a zero matrix, then iterating over `triangles`
	// and setting as neighbors the two regions on the two sides of each triangle
	// NOTE: we could just iterate over `sides_to_regions`, and remove `triangles` as input to this
	// function
	std::vector<std::vector<int>> adjacency_matrix(num_regions, std::vector<int>(num_regions, 0));
	for (Mesh3DTriangle* triangle : triangles) {
		size_t region1 = sides_to_regions.at({triangle, triangle->getLabel(false)});
		size_t region2 = sides_to_regions.at({triangle, triangle->getLabel(true)});
		adjacency_matrix[region1][region2] = 1;
		adjacency_matrix[region2][region1] = 1;
	}
	return adjacency_matrix;
}

//------------------------------------------------------------
// mesh operations
//------------------------------------------------------------

absl::flat_hash_set<Mesh3DVertex*> Mesh3DCornerTable::edgeSubdivisionWithUpdatedVerts(
    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d split_coords) {
	std::vector<Mesh3DTriangle*> new_triangles;
	EdgeSubdivisionFixedPoint(triangle, v1, v2, split_coords, new_triangles);
	absl::flat_hash_set<Mesh3DVertex*> updated_verts;
	for (Mesh3DTriangle* tri : new_triangles) {
		for (Mesh3DVertex* vert : tri->getVerts()) {
			updated_verts.insert(vert);
		}
	}
	return updated_verts;
}

absl::flat_hash_set<Mesh3DVertex*> Mesh3DCornerTable::edgeFlipWithUpdatedVerts(
    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2) {
	Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
	while (hfc->getVertex() == v1 || hfc->getVertex() == v2) {
		hfc = hfc->getNext();
	}
	Mesh3DTriangle* oppos_tri = hfc->getOppos()->getTri();

	bool is_flipped = EdgeFlipFast(triangle, v1, v2);
	if (!is_flipped) {
		return {};
	}
	// Triangle pointers for the new triangles are reused from the old ones.
	absl::flat_hash_set<Mesh3DVertex*> updated_verts;
	updated_verts.reserve(4);
	hfc = triangle->getHalfCorner();
	for (int i = 0; i < 3; ++i, hfc = hfc->getNext()) {
		Mesh3DVertex* v = hfc->getVertex();
		updated_verts.insert(v);
	}
	Mesh3DHalfCorner* oppos_hfc = oppos_tri->getHalfCorner();
	for (int i = 0; i < 3; ++i, oppos_hfc = oppos_hfc->getNext()) {
		Mesh3DVertex* v = oppos_hfc->getVertex();
		updated_verts.insert(v);
	}
	return updated_verts;
}

//------------------------------------------------------------
// moving elements
//------------------------------------------------------------

void Mesh3DCornerTable::shiftMeshByConstant(const int coordinate, const double amount) {
	assert(coordinate >= 0 && coordinate <= 2 && "illegal coordinate, mesh shifting cancelled");

	if (coordinate == 0) {
		for (Mesh3DVertex* vertex : mesh_vertices_list) {
			vertex->setXCoord(vertex->getXCoord() + amount);
		}
	} else if (coordinate == 1) {
		for (Mesh3DVertex* vertex : mesh_vertices_list) {
			vertex->setYCoord(vertex->getYCoord() + amount);
		}
	} else if (coordinate == 2) {
		for (Mesh3DVertex* vertex : mesh_vertices_list) {
			vertex->setZCoord(vertex->getZCoord() + amount);
		}
	}
}

void Mesh3DCornerTable::removeInterface(Vec2i interface) {
	if (interface[0] == interface[1]) {
		return;
	}

	if (interface[0] > interface[1]) {
		std::swap(interface[0], interface[1]);
	}

	std::vector<const Mesh3DTriangle*> to_be_deleted;
	absl::flat_hash_set<Mesh3DVertex*> affected_vertices;
	for (const Mesh3DTriangle* tri : mesh_triangles_list) {
		Vec2i labels = tri->getLabels();
		if (labels[0] > labels[1]) {
			std::swap(labels[0], labels[1]);
		}
		// Triangle is not on an interface, do not touch it.
		if (labels[0] != interface[0] || labels[1] != interface[1]) {
			continue;
		}
		for (Mesh3DVertex* v : tri->getVerts()) {
			affected_vertices.insert(v);
		}
		to_be_deleted.emplace_back(tri);
	}

	for (const Mesh3DTriangle* tri : to_be_deleted) {
		Mesh3DHalfCorner* hfc = tri->getHalfCorner();
		for (int i = 0; i < 3; ++i) {
			Mesh3DHalfCorner* dual = hfc->getDual();
			Mesh3DHalfCorner* oppos = hfc->getOppos();
			Mesh3DHalfCorner* dual_oppos = dual->getOppos();
			hfc->setOppos(dual);
			dual->setOppos(hfc);
			oppos->setOppos(dual_oppos);
			dual_oppos->setOppos(oppos);
			hfc = hfc->getNext();
		}
	}

	for (const Mesh3DTriangle* tri : to_be_deleted) {
		deleteTriangle(tri);
	}

	for (Mesh3DVertex* vert : affected_vertices) {
		if (vertex_to_hfc_map.at(vert).empty()) {
			deleteVertex(vert);
		}
	}

	// Now interface[0] is equivalent to interface[1]. Relabel everything to use only interface[0]. As
	// interface[0] is smaller, it naturally biases towards using label `0` which is exactly what we
	// want.
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		Vec2i labels = tri->getLabels();
		bool changed = false;
		for (int i = 0; i < 2; ++i) {
			if (labels[i] == interface[1]) {
				labels[i] = interface[0];
				changed = true;
			}
		}
		if (changed) {
			tri->setLabels(labels);
		}
	}
}

void Mesh3DCornerTable::orderLabelsOnManifoldPatches() const {
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		Vec2i labels = tri->getLabels();
		if (labels[0] <= labels[1]) {
			continue;
		}
		std::swap(labels[0], labels[1]);
		tri->setLabels(labels);
		tri->setHalfCorner(tri->getHalfCorner()->getDual());

		// Revert label sides.
		for (Mesh3DHalfCorner* hfc : tri->getHalfCorners()) {
			hfc->setLabelSide(!hfc->getLabelSide());
		}
	}
};