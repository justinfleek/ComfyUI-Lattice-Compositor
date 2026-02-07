
/* Mesh3DCornerTableEdgeCollapse.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru
 *
 * Implements the edge collapse with all its non-manifold technicalities.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Mesh3DCornerTable.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------
absl::flat_hash_set<Mesh3DVertex*> Mesh3DCornerTable::edgeCollapseWithUpdatedVerts(
    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d new_vert_coords) {
	// Get removed triangles.

	Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
	while (hfc->getVertex() == v1 || hfc->getVertex() == v2) {
		hfc = hfc->getNext();
	}
	std::vector<Mesh3DHalfCorner*> around_hfcs;
	walkAroundEdge(hfc, around_hfcs);

	absl::flat_hash_set<Mesh3DVertex*> updated_verts;
	for (Mesh3DHalfCorner* around_hfc : around_hfcs) {
		Mesh3DTriangle* tri = around_hfc->getTri();
		for (Mesh3DVertex* vert : tri->getVerts()) {
			updated_verts.insert(vert);
		}
	}
	EdgeCollapseType has_collapsed = edgeCollapse(triangle, v1, v2, new_vert_coords);
	if (has_collapsed != EdgeCollapseType::kRegular) {
		return {};
	}
	updated_verts.erase(v2);
	return updated_verts;
}

// edge collapse:
Mesh3DCornerTable::EdgeCollapseType Mesh3DCornerTable::edgeCollapse(Mesh3DTriangle* triangle,
                                                                    Mesh3DVertex* v1,
                                                                    Mesh3DVertex* v2,
                                                                    Vec3d new_coords) {
	// if `triangle` was previously deleted and not longer exists in mesh, don't do anything.
	if (!isTriangleInMesh(triangle)) {
		return EdgeCollapseType::kNonValid;
	}
	// if the input edge is a no-collapse edge, cancel the collapse
	if (no_collapse_edges.count(SortedMeshEdge(v1, v2))) {
		addT1RetractionEdgeCollapseCancel();
		return EdgeCollapseType::kNonValid;
	}

	// all connectivity reassignments and all deletions of elements are only done at the end of this
	// function, after it is determined that the edge collapse is valid

	//---------
	// to keep track of how to reassign the opposite halfcorners after collapse:
	absl::flat_hash_map<Mesh3DHalfCorner*, Mesh3DHalfCorner*> opposites_map;
	// keep track of the triangles that are to be deleted:
	std::vector<Mesh3DTriangle*> delete_tris;
	//---------

	// store initial coordinates of input vertices
	Vec3d v1_coords = v1->getCoords();
	Vec3d v2_coords = v2->getCoords();
	bool is_edge_short = mag2(v1_coords - v2_coords) < kShortEdgeThreshold * kShortEdgeThreshold;

	// get all halfcorners around v1, and all halfcorners around v2:
	absl::flat_hash_set<Mesh3DHalfCorner*> hfcs_around_v1 = vertex_to_hfc_map.at(v1);
	absl::flat_hash_set<Mesh3DHalfCorner*> hfcs_around_v2 = vertex_to_hfc_map.at(v2);

	// Get half-corners around the edge.
	Mesh3DHalfCorner* starting_hfc = triangle->getHalfCornerAtVertex(v1);
	if (starting_hfc->getNext()->getVertex() == v2) {
		starting_hfc = starting_hfc->getPrev();
	} else {
		starting_hfc = starting_hfc->getNext();
	}
	std::vector<Mesh3DHalfCorner*> extending_hfcs = hfcsAroundEdge(starting_hfc);

	if (hasHolesAroundEdge(hfcs_around_v1, hfcs_around_v2, extending_hfcs)) {
		addHoppeCriterionEdgeCollapseCancel();
		return EdgeCollapseType::kNonValid;
	}
	// Get holes around an edge. Used to classify and handle special cases.
	// auto holes = findHolesAroundEdge(hfcs_around_v1, hfcs_around_v2, extending_hfcs);

	// Check if edge collapse is topologically valid.
	// If not, cancel the collapse, and return v1 and v2 to their initial coordinates:
	// Edges with holes are currently being rejected above, so we do not need to find and handle holes
	// here.
	EdgeCollapseType collapse_type =
	    getEdgeCollapseType(triangle, v1, v2, new_coords, extending_hfcs, /*holes=*/{});
	if (collapse_type != EdgeCollapseType::kRegular) {
		return EdgeCollapseType::kNonValid;
	}
	// move `v1` and `v2` to `new_coords`
	v1->setCoords(new_coords);
	v2->setCoords(new_coords);

	// check if edge collapse is geometrically valid:
	if (!is_edge_short) {
		if (isCollapseGeometricallyValid(v1, v2, hfcs_around_v1, hfcs_around_v2, v1_coords, v2_coords,
		                                 new_coords) == 0) {
			v1->setCoords(v1_coords);
			v2->setCoords(v2_coords);
			return EdgeCollapseType::kNonValid;
		}
	}

	// loop through all the triangles that share the edge (v1, v2):
	for (Mesh3DHalfCorner* hfc3 : extending_hfcs) {
		triangle = hfc3->getTri();
		Mesh3DVertex* v3 = hfc3->getVertex();

		// The halfcorners extending edges (1,3) and (2,3) will need to have their opposites
		// reassigned: get halfcorner extending edge (1, 3), and extending edge (2, 3):
		Mesh3DHalfCorner *hfc_over13 = triangle->getHalfCornerAtVertex(v2),
		                 *hfc_over23 = triangle->getHalfCornerAtVertex(v1);

		// order on the face of the halfcorner should be 1->3, respectively 2->3
		if (hfc_over13->getNext()->getVertex() == v3) {
			hfc_over13 = hfc_over13->getDual();
		}
		if (hfc_over23->getNext()->getVertex() == v3) {
			hfc_over23 = hfc_over23->getDual();
		}

		// get a list of all hfcs extending (1, 3) and (2, 3):
		std::vector<Mesh3DHalfCorner*> hfcs13 = hfcsAroundEdge(hfc_over13),
		                               hfcs23 = hfcsAroundEdge(hfc_over23);

		// move all hfcs in hfcs vector:
		std::vector<Mesh3DHalfCorner*> hfcs;
		hfcs.reserve(hfcs13.size() + hfcs23.size() - 2);
		for (Mesh3DHalfCorner* hfc13 : hfcs13) {
			// don't add the hfcs in initial triangle:
			if (hfc13 == hfc_over13) {
				continue;
			}
			hfcs.push_back(hfc13);
		}
		for (Mesh3DHalfCorner* hfc23 : hfcs23) {
			if (hfc23 == hfc_over23) {
				continue;
			}
			hfcs.push_back(hfc23);
		}
		// The edges (v3, v2) and (v3, v1) will become one (v3, v1) after the collapse,
		// so we have to reassign the opposites around that edge:
		assignOppositesTopologically(v1, v2, v3, hfcs13, opposites_map);

		// add triangle to the list of triangles to be deleted:
		delete_tris.push_back(triangle);
	}

	// from opposites_map, assign the pairs of opposites extending the new edge (v1, v3):
	for (auto opp_pair : opposites_map) {
		opp_pair.first->setOppos(opp_pair.second);
		opp_pair.second->setOppos(opp_pair.first);
	}

	transferValuesEdgeCollapse(v1, v2, v1_coords, v2_coords, new_coords);

	// mark all the triangles in delete_tris vector as deleted:
	for (Mesh3DTriangle* tri : delete_tris) {
		deleteTriangle(tri);
	}

	// all the non-deleted halfcorners at vertex v2 are reassigned to vertex v1:
	// We need a separate container for the hfcs, because the hash maps will change during the
	// reassignment.
	hfcs_around_v2 = vertex_to_hfc_map.at(v2);
	std::vector<Mesh3DHalfCorner*> hfcs_to_reassign = {hfcs_around_v2.begin(), hfcs_around_v2.end()};
	for (Mesh3DHalfCorner* hfcv2 : hfcs_to_reassign) {
		setHFCVertex(hfcv2, v1);
		setHFCVertex(hfcv2->getDual(), v1);
	}
	// after all tris around edge (v1, v2) are resolved, delete vert v2:
	deleteVertex(v2);
	return collapse_type;
}

bool Mesh3DCornerTable::isCollapseGeometricallyValid(
    Mesh3DVertex* v1, Mesh3DVertex* v2,
    const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v1,
    const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v2, Vec3d v1_coords, Vec3d v2_coords,
    Vec3d new_coords) {
	// if the point of collapsing is not v2:
	if (new_coords != v2_coords &&
	    !isCollapseValidAroundVertex(v2, v1, hfcs_around_v2, hfcs_around_v1, new_coords)) {
		return false;
	}

	// if the point of collapsing is not v1:
	if (new_coords != v1_coords &&
	    !isCollapseValidAroundVertex(v1, v2, hfcs_around_v1, hfcs_around_v2, new_coords)) {
		return false;
	}
	return true;
}

bool Mesh3DCornerTable::isCollapseValidAroundVertex(
    Mesh3DVertex* v1, Mesh3DVertex* v2,
    const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v1,
    const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v2, Vec3d new_coords) {
	for (Mesh3DHalfCorner* hfcv1 : hfcs_around_v1) {
		if (hfcv1->getNext()->getVertex() == v2 || hfcv1->getPrev()->getVertex() == v2) {
			continue;
		}
		// check if in any triangle containing v1, any halfcorners extending the same edge switch
		// places: see collapse_opposite_check.png:
		Vec3d next_coords = hfcv1->getNext()->getVertex()->getCoords();
		Vec3d prev_coords = hfcv1->getPrev()->getVertex()->getCoords();

		std::vector<Mesh3DHalfCorner*> hfcs_over_nextprev = hfcsAroundEdge(hfcv1);
		// checking if the halfcorners extending the edge of hfcv1 switch places after collapse:
		if (!checkOpposAroundEdge(next_coords, prev_coords, hfcs_over_nextprev)) {
			return false;
		}

		// check if next and prev don't overlap with their opposites:
		// use check opposites function for next and previous hfcs:
		Mesh3DHalfCorner *next_hfc = hfcv1->getNext(), *prev_hfc = hfcv1->getPrev();
		// next_hfc and prev_hfc chosen on the face oriented such that their next hfc is v1:
		if (next_hfc->getNext()->getVertex() != v1) {
			next_hfc = next_hfc->getDual();
		}

		if (prev_hfc->getNext()->getVertex() != v1) {
			prev_hfc = prev_hfc->getDual();
		}

		// get halfcorners extending the edge of next_hfc (hfcs_over_v1prev),
		// and proceed only if that edge is not part of a collapsed triangle:
		std::vector<Mesh3DHalfCorner*> hfcs_over_v1prev = hfcsAroundEdge(next_hfc),
		                               hfcs_over_v1next = hfcsAroundEdge(prev_hfc), hfcs_over_newprev,
		                               hfcs_over_newnext;
		int should_check = 1;
		for (Mesh3DHalfCorner* hfc_v1prev : hfcs_over_v1prev) {
			if (hfc_v1prev->getVertex() == v2) {
				should_check = 0;
				break;
			}
		}

		// check if the hfcs extending the edge (new, prev) switch places after collapse:
		if (should_check) {
			if (settings->verbosity >= 3) {
				std::cout << "next check" << std::endl;
			}
			if (!checkOpposAroundEdge(new_coords, prev_coords, hfcs_over_v1prev)) {
				return false;
			}
		}

		// same for prev and its opposite:
		should_check = 1;
		for (Mesh3DHalfCorner* hfc_v1next : hfcs_over_v1next) {
			if (hfc_v1next->getVertex() == v2) {
				should_check = 0;
				break;
			}
		}

		if (should_check) {
			if (settings->verbosity >= 3) {
				std::cout << "prev check" << std::endl;
			}
			if (!checkOpposAroundEdge(new_coords, next_coords, hfcs_over_v1next)) {
				return false;
			}
		}
	}
	return true;
}

void Mesh3DCornerTable::assignOppositesTopologically(
    Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3,
    const std::vector<Mesh3DHalfCorner*>& extending_hfcs,
    absl::flat_hash_map<Mesh3DHalfCorner*, Mesh3DHalfCorner*>& opposite_map) {
	for (Mesh3DHalfCorner* hfc : extending_hfcs) {
		for (int side = 0; side < 2; ++side, hfc = hfc->getDual()) {
			Mesh3DHalfCorner* oppos_hfc = hfc->getOppos();
			// The opposite is not affected by the edge collapse, leave it alone.
			if (oppos_hfc->getVertex() != v2) {
				continue;
			}

			while (oppos_hfc->getVertex() != v1) {
				oppos_hfc = oppos_hfc->getNext();
			}
			// Cross over (v2, v3) edge.
			oppos_hfc = oppos_hfc->getOppos();
			opposite_map[hfc] = oppos_hfc;
			opposite_map[oppos_hfc] = hfc;
		}
	}
}

absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>
Mesh3DCornerTable::findHolesAroundEdge(const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v1,
                                       const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v2,
                                       const std::vector<Mesh3DHalfCorner*>& extending_hfcs) {
	absl::flat_hash_set<Mesh3DVertex*> extending_verts;
	for (Mesh3DHalfCorner* hfc : extending_hfcs) {
		extending_verts.insert(hfc->getVertex());
	}

	// Find all holes.
	absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>> holes;
	for (Mesh3DHalfCorner* hfc1 : hfcs_v1) {
		Mesh3DVertex* prev1 = hfc1->getPrev()->getVertex();
		Mesh3DVertex* next1 = hfc1->getNext()->getVertex();
		for (Mesh3DHalfCorner* hfc2 : hfcs_v2) {
			Mesh3DVertex* prev2 = hfc2->getPrev()->getVertex();
			Mesh3DVertex* next2 = hfc2->getNext()->getVertex();
			if (prev1 == prev2 && !extending_verts.contains(prev1)) {
				holes[prev1] = {hfc1->getNext(), hfc2->getNext()};
			}
			if (prev1 == next2 && !extending_verts.contains(prev1)) {
				holes[prev1] = {hfc1->getNext(), hfc2->getPrev()};
			}
			if (next1 == prev2 && !extending_verts.contains(next1)) {
				holes[next1] = {hfc1->getPrev(), hfc2->getNext()};
			}
			if (next1 == next2 && !extending_verts.contains(next1)) {
				holes[next1] = {hfc1->getPrev(), hfc2->getPrev()};
			}
		}
	}
	return holes;
}
bool Mesh3DCornerTable::hasHolesAroundEdge(const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v1,
                                           const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v2,
                                           const std::vector<Mesh3DHalfCorner*>& extending_hfcs) {
	absl::flat_hash_set<Mesh3DVertex*> extending_verts;
	for (Mesh3DHalfCorner* hfc : extending_hfcs) {
		extending_verts.insert(hfc->getVertex());
	}

	for (Mesh3DHalfCorner* hfc1 : hfcs_v1) {
		Mesh3DVertex* prev1 = hfc1->getPrev()->getVertex();
		Mesh3DVertex* next1 = hfc1->getNext()->getVertex();
		for (Mesh3DHalfCorner* hfc2 : hfcs_v2) {
			Mesh3DVertex* prev2 = hfc2->getPrev()->getVertex();
			Mesh3DVertex* next2 = hfc2->getNext()->getVertex();
			if (prev1 == prev2 && !extending_verts.contains(prev1)) {
				return true;
			}
			if (prev1 == next2 && !extending_verts.contains(prev1)) {
				return true;
			}
			if (next1 == prev2 && !extending_verts.contains(next1)) {
				return true;
			}
			if (next1 == next2 && !extending_verts.contains(next1)) {
				return true;
			}
		}
	}
	return false;
}

Mesh3DCornerTable::EdgeCollapseType Mesh3DCornerTable::checkHoppeCriterion(
    const absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>&
        holes) {
	// Check hole parity.
	for (auto [common_vert, hfc_pair] : holes) {
		std::vector<Mesh3DHalfCorner*> hfcs_e1 = hfcsAroundEdge(hfc_pair.first);
		std::vector<Mesh3DHalfCorner*> hfcs_e2 = hfcsAroundEdge(hfc_pair.second);

		absl::flat_hash_map<int, int> label_to_hfc_count;
		for (Mesh3DHalfCorner* hfc : hfcs_e1) {
			Vec2i labels = hfc->getTri()->getLabels();
			label_to_hfc_count[labels[0]]++;
			label_to_hfc_count[labels[1]]++;
		}
		for (Mesh3DHalfCorner* hfc : hfcs_e2) {
			Vec2i labels = hfc->getTri()->getLabels();
			label_to_hfc_count[labels[0]]++;
			label_to_hfc_count[labels[1]]++;
		}

		int num_ambigious = 0;
		for (auto [label, count] : label_to_hfc_count) {
			num_ambigious += count > 2;
		}
		if (num_ambigious > 1) {
			return EdgeCollapseType::kNonValid;
		}
	}

	if (holes.empty()) {
		return EdgeCollapseType::kRegular;
	}
	addHoppeCriterionEdgeCollapseCancel();
	return EdgeCollapseType::kHoppe;
}

// checks whether triangle flips during edge collapse
int Mesh3DCornerTable::triangleNotFlip(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3,
                                       Vec3d new_c) {
	Vec3d coords1 = v1->getCoords();
	Vec3d coords2 = v2->getCoords();
	Vec3d coords3 = v3->getCoords();
	// Configuration valid if new_coords are not coplanar with triangle (v1, v2, v3).
	if (intersector.orient3d(coords1.v, coords2.v, coords3.v, new_c.v)) {
		return 1;
	}
	Vec3d norm123 = cross((coords3 - coords2), (coords3 - coords1));
	Vec3d normnew23 = cross((coords3 - coords2), (coords3 - new_c));
	// if normals are oriented in the same direction, then the edge collapse is valid
	return dot(norm123, normnew23) > 0;
}

// check edge collapse valid
// (For the topology check, we will forbid tetrahedron edges and will use Hoppe's (siggraph
// 1993) criterion.

// (For the geometry check, we will forbid in plane triangle-flips/overlaps [TriangleFlip.png]
Mesh3DCornerTable::EdgeCollapseType Mesh3DCornerTable::getEdgeCollapseType(
    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d new_coords,
    const std::vector<Mesh3DHalfCorner*>& extending_hfcs,
    const absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>&
        holes) {
	EdgeCollapseType hoppe_check = checkHoppeCriterion(holes);
	if (hoppe_check != EdgeCollapseType::kRegular) {
		return hoppe_check;
	}

	std::set<Mesh3DVertex*> extending_verts;
	for (Mesh3DHalfCorner* extending_hfc : extending_hfcs) {
		extending_verts.insert(extending_hfc->getVertex());

		// detect tetrahedron case:
		if ((extending_hfc->getNext()->getOppos()->getVertex() ==
		     extending_hfc->getPrev()->getOppos()->getVertex()) ||
		    (extending_hfc->getDual()->getNext()->getOppos()->getVertex() ==
		     extending_hfc->getDual()->getPrev()->getOppos()->getVertex())) {
			addTetrahedronEdgeCollapseCancel();
			if (settings->allow_t2_edge_collapse) {
				return EdgeCollapseType::kTetrahedron;
			} else {
				return EdgeCollapseType::kNonValid;
			}
		}

		// check if any in-plane triangles would flip:
		// (could be omitted, since a less restrictive check
		// is included in the opposite switch places check in edgeCollapse()
		if (triangleNotFlip(extending_hfc->getNext()->getVertex(), extending_hfc->getVertex(),
		                    extending_hfc->getPrev()->getOppos()->getVertex(), new_coords) == 0 ||
		    triangleNotFlip(extending_hfc->getPrev()->getVertex(), extending_hfc->getVertex(),
		                    extending_hfc->getNext()->getOppos()->getVertex(), new_coords) == 0) {
			addInPlaneFlipEdgeCollapseCancel();
			return EdgeCollapseType::kNonValid;
		}
	}
	return EdgeCollapseType::kRegular;

	// local adjacency check: check if performing the edge collapse would create a T1 configuration
	// local adjacency check: check if performing the edge collapse would change the local region
	// adjacency around `v1` and `v2`

	// retrieve triangles adjacent to `v1` and `v2`
	absl::flat_hash_set<Mesh3DTriangle*> tris_around_v1 = getTrianglesAroundVertex(v1);
	absl::flat_hash_set<Mesh3DTriangle*> tris_around_v2 = getTrianglesAroundVertex(v2);
	// set of labels around `v1` and `v2`
	absl::flat_hash_set<int> labels_around_v1_set;
	absl::flat_hash_set<int> labels_around_v2_set;
	// fill in `labels_around_v1` and `labels_around_v2`
	for (Mesh3DTriangle* triangle : tris_around_v1) {
		labels_around_v1_set.insert(triangle->getLabel(0));
		labels_around_v1_set.insert(triangle->getLabel(1));
	}
	for (Mesh3DTriangle* triangle : tris_around_v2) {
		labels_around_v2_set.insert(triangle->getLabel(0));
		labels_around_v2_set.insert(triangle->getLabel(1));
	}
	// check if both `v1` and `v2` are adjacent to 4 local regions, if yes, cancel the edge collapse
	if (labels_around_v1_set.size() == 4 && labels_around_v2_set.size() == 4) {
		addDoubleFourValenceEdgeCollapseCancel();
		return EdgeCollapseType::kNonValid;
	}

	// check if local region valence around `v1` and `v2` is either 4-3 or 3-3, i.e. one of the
	// configurations for which we have to perform a topological edge collapse safety test
	if ((labels_around_v1_set.size() == 4 && labels_around_v2_set.size() == 3) ||
	    (labels_around_v1_set.size() == 3 && labels_around_v2_set.size() == 4) ||
	    (labels_around_v1_set.size() == 3 && labels_around_v2_set.size() == 3)) {
		// perform the topological edge collapse safety test - given edge collapse candidate E, for both
		// endpoints of E check if there exists a local region L adjacent to this endpoint, such that no
		// triangle of L contains E (we say L doesn't cover E); if such L exists for both endpoints of
		// E, cancel the edge collapse

		// store the candidate edge as a `SortedMeshEdge`; this representation works well for comparing
		// mesh edges
		SortedMeshEdge e_cand(v1, v2);

		// set of labels (and therefore local regions, as there exists a 1-1 correspondence between
		// labels and local regions around every vertex in mesh upkeeper), for which there exists a
		// triangle adjacent to `v1` that contains `e_cand`
		absl::flat_hash_set<int> v1_regions_covering_candidate;
		// iterate over triangles adjacent to `v1`
		for (Mesh3DTriangle* triangle : tris_around_v1) {
			// if both regions corresponding to the two labels on `triangle` cover `e_cand`, there is no
			// need to continue processing `triangle`; if at least one of the two regions hasn't so far
			// been observed to cover `e_cand`, we continue processing `triangle`
			if (!v1_regions_covering_candidate.count(triangle->getLabel(0)) ||
			    !v1_regions_covering_candidate.count(triangle->getLabel(1))) {
				Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
				// iterate over the three edges of `triangle`, if any equal `e_cand`, save both labels on
				// `triangle` into `v1_regions_covering_candidate`
				for (int i = 0; i < 3; ++i, hfc->getNext()) {
					SortedMeshEdge e_tri(hfc->getVertex(), hfc->getNext()->getVertex());
					if (e_cand == e_tri) {
						v1_regions_covering_candidate.insert(triangle->getLabel(0));
						v1_regions_covering_candidate.insert(triangle->getLabel(0));
						break;
					}
				}
			}
		}

		// perform the same process for triangles touching `v2`

		// set of labels (and therefore local regions, as there exists a 1-1 correspondence between
		// labels and local regions around every vertex in mesh upkeeper), for which there exists a
		// triangle adjacent to `v2` that contains `e_cand`
		absl::flat_hash_set<int> v2_regions_covering_candidate;
		// iterate over triangles adjacent to `v2`
		for (Mesh3DTriangle* triangle : tris_around_v2) {
			// if both regions corresponding to the two labels on `triangle` cover `e_cand`, there is no
			// need to continue processing `triangle`; if at least one of the two regions hasn't so far
			// been observed to cover `e_cand`, we continue processing `triangle`
			if (!v2_regions_covering_candidate.count(triangle->getLabel(0)) ||
			    !v2_regions_covering_candidate.count(triangle->getLabel(1))) {
				Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
				// iterate over the three edges of `triangle`, if any equal `e_cand`, save both labels on
				// `triangle` into `v2_regions_covering_candidate`
				for (int i = 0; i < 3; ++i, hfc->getNext()) {
					SortedMeshEdge e_tri(hfc->getVertex(), hfc->getNext()->getVertex());
					if (e_cand == e_tri) {
						v2_regions_covering_candidate.insert(triangle->getLabel(0));
						v2_regions_covering_candidate.insert(triangle->getLabel(0));
						break;
					}
				}
			}
		}

		// check if these exist labels present on triangles around both `v1` and `v2`, such that the
		// regions associated with these lables don't cover `e_cand`
		if (labels_around_v1_set.size() != v1_regions_covering_candidate.size() &&
		    labels_around_v2_set.size() != v2_regions_covering_candidate.size()) {
			addCandidateCoveringEdgeCollapseCancel();
			return EdgeCollapseType::kNonValid;
		}
	}

	// check if there are the same number of labels on triangles around `v1` and `v2` (and therefore
	// the same number of local regions around `v1` and `v2`), if not, cancel edge collapse
	/*if (labels_around_v1_set.size() != labels_around_v2_set.size()) {
	  addUnequalValenceEdgeCollapseCancel();
	  return 0;
	}
	// cast the sets of labels around `v1` and `v2` into vectors
	std::vector<int> labels_around_v1_vec(labels_around_v1_set.begin(), labels_around_v1_set.end());
	std::vector<int> labels_around_v2_vec(labels_around_v2_set.begin(), labels_around_v2_set.end());
	// sort the vectors of labels around `v1` and `v2`
	std::sort(labels_around_v1_vec.begin(), labels_around_v1_vec.end());
	std::sort(labels_around_v1_vec.begin(), labels_around_v1_vec.end());
	// check if the vectors of labels around `v1` and `v2` are the same, if not, cancel edge collapse
	for (int i = 0; i < labels_around_v1_vec.size(); ++i) {
	  if (labels_around_v1_vec[i] != labels_around_v2_vec[i]) {
	    addUnequalAdjacencyEdgeCollapseCancel();
	    return 0;
	  }
	}*/

	// compare the adjacency of labels (i.e. local regions) around `v1` and `v2`; assuming there are
	// no T1 vertices at this point in the algorithm, this check is equivalent to just checking if the
	// vector of labels around `v1` is the same as the vector of labels around `v2` (checked above)

	// retrieve a map that to each `TriSide` adjacent to `v1` and `v2` assigns its local region index,
	// such that the local region indices are ordered by local region labels
	/*absl::flat_hash_map<TriSide, size_t> sides_to_regions_v1 =
	    uniteTrianglesInLocalRegions(v1, tris_around_v1, true);
	absl::flat_hash_map<TriSide, size_t> sides_to_regions_v2 =
	    uniteTrianglesInLocalRegions(v2, tris_around_v2, true);
	// calculate the adjacency matrix of local regions around `v1` and `v2`
	std::vector<std::vector<int>> regions_matrix_for_v1 =
	    buildRegionsMatrix(tris_around_v1, sides_to_regions_v1);
	std::vector<std::vector<int>> regions_matrix_for_v2 =
	    buildRegionsMatrix(tris_around_v2, sides_to_regions_v2);
	// check if adjacency matrices around `v1` and `v2` have the same size, if not, cancel edge
	// collapse
	if (regions_matrix_for_v1.size() != regions_matrix_for_v2.size()) {
	  addUnequalValenceEdgeCollapseCancel();
	  return 0;
	}
	// compare the adjacency matrices of `v1` and `v2`, if they are not the same, cancel edge collapse
	for (int i = 0; i < regions_matrix_for_v1.size(); ++i) {
	  for (int j = 0; j < i; ++j) {
	    if (regions_matrix_for_v1[i][j] != regions_matrix_for_v2[i][j]) {
	      addUnequalAdjacencyEdgeCollapseCancel();
	      return 0;
	    }
	  }
	}*/

	return EdgeCollapseType::kRegular;
}

// verifies whether the opposites around an edge are ordered properly.
// extending_hfc should be on the face oriented (edgev1->edgev2->extending_hfc):
bool Mesh3DCornerTable::checkOpposAroundEdge(Vec3d edgev1_coords, Vec3d edgev2_coords,
                                             const std::vector<Mesh3DHalfCorner*>& extending_hfcs) {
	Mesh3DHalfCorner* current_opposite = nullptr;
	Mesh3DVertex *current_vertex = nullptr, *current_oppos_vertex = nullptr;

	// for each hfc, check there's nothing between it and its opposite:
	for (Mesh3DHalfCorner* current_hfc : extending_hfcs) {
		current_opposite = current_hfc->getOppos();
		current_vertex = current_hfc->getVertex();
		current_oppos_vertex = current_opposite->getVertex();
		Vec3d current_coords = current_vertex->getCoords();
		Vec3d opp_coords = current_oppos_vertex->getCoords();
		// if current overlaps with opposite:
		if (intersector.orient3d(edgev1_coords.v, edgev2_coords.v, current_coords.v, opp_coords.v) ==
		        0 &&
		    sameSemiplane(current_coords, opp_coords, edgev1_coords, edgev2_coords)) {
			return 0;
		}
		//  if only two hfcs extend edge, and they don't overlap, then the configuration is valid:
		if (extending_hfcs.size() == 2) {
			return 1;
		}

		// if current and oppos form an angle <= 180:
		if (intersector.orient3d(edgev1_coords.v, edgev2_coords.v, current_coords.v, opp_coords.v) <=
		    0) {
			for (Mesh3DHalfCorner* other_hfc : extending_hfcs) {
				if (other_hfc == current_hfc || other_hfc->getVertex() == current_oppos_vertex) {
					continue;
				}
				Vec3d other_coords = other_hfc->getVertex()->getCoords();
				if (intersector.orient3d(edgev1_coords.v, edgev2_coords.v, current_coords.v,
				                         other_coords.v) == 0 &&
				    intersector.orient3d(edgev2_coords.v, edgev1_coords.v, opp_coords.v, other_coords.v) ==
				        0) {
					return 0;
				}
				// if hfc is between opp and current_hfc, then invalid configuration
				else if (intersector.orient3d(edgev1_coords.v, edgev2_coords.v, current_coords.v,
				                              other_coords.v) < 0 &&
				         intersector.orient3d(edgev2_coords.v, edgev1_coords.v, opp_coords.v,
				                              other_coords.v) < 0) {
					return 0;
				}
			}
		}
		// if current an oppos form an angle > 180:
		else {
			for (Mesh3DHalfCorner* other_hfc : extending_hfcs) {
				if (other_hfc == current_hfc || other_hfc->getVertex() == current_oppos_vertex) {
					continue;
				}
				Vec3d other_coords = other_hfc->getVertex()->getCoords();
				// if hfc is between opp and current_hfc, then invalid configuration
				if (intersector.orient3d(edgev1_coords.v, edgev2_coords.v, current_coords.v,
				                         other_coords.v) <= 0 ||
				    intersector.orient3d(edgev2_coords.v, edgev1_coords.v, opp_coords.v, other_coords.v) <=
				        0) {
					return 0;
				}
			}
		}
	}
	return 1;
}

// returns 1 if p1, p2 on the same side of line AB
int Mesh3DCornerTable::sameSemiplane(Vec3d p1, Vec3d p2, Vec3d a, Vec3d b) const {
	Vec3d cross_abp1, cross_abp2;
	cross_abp1 = cross(a - b, a - p1);
	cross_abp2 = cross(a - b, a - p2);
	return dot(cross_abp1, cross_abp2) >= 0;
}

void Mesh3DCornerTable::transferValuesEdgeCollapse(Mesh3DVertex* v1, Mesh3DVertex* v2,
                                                   Vec3d v1_coords, Vec3d v2_coords,
                                                   Vec3d new_coords) const {
	Vec3d diff = v2_coords - v1_coords;
	double diff_sq = mag2(diff);
	// Interpolate linearly if points are a bit apart. Otherwise, just take the average to avoid
	// numerical problems.
	double alpha = 0.5;
	if (diff_sq > 1e-200) {
		alpha = dot(new_coords - v1_coords, diff) / diff_sq;
	}
	v1->setProperties(
		VertexProperties::linearInterpolation(v1->getProperties(), v2->getProperties(), alpha));
}