#pragma once

#include "datastructures/Mesh3DInterface.h"

// A wrapper of the TopoFixer Mesh3DInterface to endow mesh elements with linear indices
// This will be removed once the TopoFixer also uses linear indexing.

namespace sdtf::viewer::logic {
;

class LinearMesh3DView {
public:
	// Copy vertex/triangle/halfcorner pointers into arrays and
	// create data structure to convert from pointers to linear indices
	LinearMesh3DView(const Mesh3DInterface* mesh);

	auto numVertices() const { return v_.size(); }
	auto numTriangles() const { return t_.size(); }
	auto numHalfCorners() const { return h_.size(); }

	// index to pointer
	auto vertex(unsigned int i) const { return v_[i]; }
	auto triangle(unsigned int i) const { return t_[i]; }
	auto halfCorner(unsigned int i) const { return h_[i]; }

	// pointer to index
	auto vertexIndex(const Mesh3DVertex* v) const { return v_map_.find(v)->second; }
	auto triangleIndex(const Mesh3DTriangle* t) const { return t_map_.find(t)->second; }
	auto halfCornerIndex(const Mesh3DHalfCorner* h) const { return h_map_.find(h)->second; }

	// return references to linear arrays of pointers
	auto& vertices() const { return v_; }
	auto& triangles() const { return t_; }
	auto& halfCorners() const { return h_; }
	
	// return pointer to a halfedge starting at the given vertex index
	auto halfEdgeAtVertex(unsigned int vi) const { return v_hc_[vi]; }

private:
	void buildLinearView();

	// helper function for building linear view for one primitive type (e.g. vertex)
	template <typename T>
	void buildLinearElementView(std::vector<const T*>* el_vec,
		absl::flat_hash_map<const T*, unsigned int>* el_map,
		const absl::flat_hash_set<T*>& el_set)
	{
		el_vec->reserve(el_set.size());
		el_map->reserve(el_set.size());

		unsigned int i = 0;
		for (auto el : el_set) {
			el_vec->push_back(el);
			(*el_map)[el] = i;
			i++;
		}
	}

	const Mesh3DInterface* mesh_;

	std::vector<const Mesh3DVertex*> v_;
	absl::flat_hash_map<const Mesh3DVertex*, unsigned int> v_map_;
	std::vector<const Mesh3DHalfCorner*> v_hc_;

	std::vector<const Mesh3DTriangle*> t_;
	absl::flat_hash_map<const Mesh3DTriangle*, unsigned int> t_map_;

	std::vector<const Mesh3DHalfCorner*> h_;
	absl::flat_hash_map<const Mesh3DHalfCorner*, unsigned int> h_map_;
	};

}  // namespace sdtf::viewer::logic