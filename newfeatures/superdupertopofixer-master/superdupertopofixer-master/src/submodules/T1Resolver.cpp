/* T1Resolver.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include "T1Resolver.h"

#include <sys/types.h>

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../utilities/vec.h"

//------------------------------------------------------------
// functions that resolve T1 degenerate configurations
//------------------------------------------------------------

// main function guiding the resolution of configurations where a vertex is adjacent to 3+ local
// regions, and there exists a pair of regions that are not adjacent via a triangle face
void T1Resolver::resolveVertices(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                 const absl::flat_hash_set<Mesh3DVertex*>& candidates) const {
	// counter for how many vertices are T1 resolved despite this resolution locally increasing
	// surface area
	int area_increasing_resolutions_counter = 0;
	// push vertices  into the queue `vertices_to_check`, which we will iterate
	// over for the resolution; we do this in every step, vertices in
	// mesh change after T1 resolutions.
	// TODO: we can smartly select which vertices need to be processed, e.g. assuming there are no
	// mesh vertices on algorithm input that need a T1 resolution, we can instead only iterate over
	// vertices in regions of the mesh where changes occured
	std::queue<Mesh3DVertex*> vertices_to_check;
	for (Mesh3DVertex* vertex : candidates) {
		vertices_to_check.push(vertex);
	}

	// coutner for the number of successful T1 resolutions within the current iteration of the outer
	// loop; if there's more than 1, the outer loop will proceed to another iteration, otherwise it
	// will stop after the current iteration
	int successes = 0;
	// process vertices in the queue
	while (!vertices_to_check.empty()) {
		// pop the front element of the queue
		Mesh3DVertex* vertex = vertices_to_check.front();
		vertices_to_check.pop();

		// retrieve triangles adjacent to `vertex`
		absl::flat_hash_set<Mesh3DTriangle*> tris = mesh.getTrianglesAroundVertex(vertex);
		// retrieve a map that to each `TriSide` adjacent to `vertex` assigns its local region index
		int num_regions;
		absl::flat_hash_map<TriSide, size_t> sides_to_regions =
		    mesh.uniteTrianglesInLocalRegions(vertex, tris, num_regions);
		// Manifold case, nothing to resolve.
		if (num_regions == 2) {
			continue;
		}

		// calculate the adjacency matrix of local regions around `vertex`
		std::vector<std::vector<int>> regions_matrix =
		    mesh.buildRegionsMatrix(tris, sides_to_regions, num_regions);
		// compute a vector of pairs of local regions that are suitable candidates for pulling apart
		std::vector<PullApartCandidate> candidates =
		    findPullApartCandidates(regions_matrix, vertex, sides_to_regions);

		// if there are no candidate pairs of local regions for pulling apart, no T1 resolution is
		// performed; this can only happen if all pairs of local regions are adjacent via a triangle
		// face - the case of "locked" configuration, where there exists a disconnected pair of local
		// regions around `vertex`, but all candidate pairs would cause local surface area to increase
		// if pulled apart, is asserted not to exist in function `findPullApartCandidates`
		if (candidates.empty()) {
			continue;
		}
		// sort `PullApartCandidate`s according to pull apart strength, from largest to smallest
		std::sort(candidates.rbegin(), candidates.rend());
		// take the `PullApartCandidate` with largest pull apart strength
		const PullApartCandidate& candidate = candidates[0];
		// note when the candidate with the highest pull apart strength still causes a local area
		// increase
		if (candidate.strength <= 0) {
			area_increasing_resolutions_counter++;
		}

		Mesh3DVertex* r1_vertex = pullVertexApart(mesh, grid, vertex, candidate, sides_to_regions);
		// These vertices might still have more regions to separate, so add them back.
		vertices_to_check.push(vertex);
		vertices_to_check.push(r1_vertex);
		successes += 1;
	}
	std::cout << "-number of T1 resolved vertices: " << successes << std::endl;
	std::cout << "-number of area increasing T1 resolutions: " << area_increasing_resolutions_counter
	          << '\n';
}

// candidate region 0 == static region
Mesh3DVertex* T1Resolver::pullVertexApart(
    Mesh3DInterface& mesh, Grid3DInterface& grid, Mesh3DVertex* r0_vertex,
    const PullApartCandidate& candidate,
    const absl::flat_hash_map<TriSide, size_t>& sides_to_regions) const {
	// offset coordinates of `r0_vertex` in positive and negative pull direction (stored in
	// `candidate.offset`), corresponding to coordinates of static split center and pulled split
	// center respectively
	Vec3d original_coords = r0_vertex->getCoords();
	Vec3d r0_new_pos = original_coords + candidate.offset;
	Vec3d r1_new_pos = original_coords - candidate.offset;
	// set coordinates of `r0_vertex` to be `r0_new_pos`, i.e. at original center + the small offset =
	// static center; r0_vertex will be the split center of candidate region 0 (static center)
	r0_vertex->setCoords(r0_new_pos);
	// generate a new mesh vertex at `r1_new_pos` to be the split center of candidate region 1 (pulled
	// center)
	Mesh3DVertex* r1_vertex = mesh.makeNewVertexAtCoords(r1_new_pos, r0_vertex->getProperties());
	// store the new mesh vertex as T1 vertex on the grid
	// TODO: evaluate whether this information should be saved as is
	grid.insertNewMeshVertexIntoT1Set(r1_vertex);

	// RETURN
	// maps each HC on a triangle of candidate region 0 that is at a link vertex of `r1_vertex` to its
	// opposite HC
	absl::flat_hash_map<uintptr_t, uintptr_t> ref_hfc_to_oppos;
	//
	// Maps a referernce half-corner to an actual half-corner. It could be an old half-corner if the
	// triangle did not change or a new one if the triangle was recreated.
	absl::flat_hash_map<uintptr_t, Mesh3DHalfCorner*> ref_hfc_to_new;
	// fill in maps `ref_hc_to_oppos` and `ref_hc_to_new` for the existing mesh
	for (const auto& [side, region] : sides_to_regions) {
		Mesh3DTriangle* tri = side.first;
		Mesh3DHalfCorner* hfc = tri->getHalfCorner();
		// iterate over the 4 HCs of `tri` that are at link vertices of `r0_vertex`
		for (int hfc_side = 0; hfc_side < 2; ++hfc_side, hfc = hfc->getDual()) {
			for (int corner = 0; corner < 3; ++corner, hfc = hfc->getNext()) {
				// skip HCs at `r0_vertex`
				if (hfc->getVertex() == r0_vertex) {
					continue;
				}
				// fill in the two HC matching maps
				ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(hfc)] =
				    reinterpret_cast<uintptr_t>(hfc->getOppos());
				ref_hfc_to_new[reinterpret_cast<uintptr_t>(hfc)] = hfc;
			}
		}
	}
	// RETURN END

	// vector of HCs at a link vertex of a hole-filling triangle.
	std::vector<Mesh3DHalfCorner*> around_r0_r1_hfcs;

	// collect `SplittingEdge`s in candidate region 0 (the static region)
	std::vector<SplittingEdge> splitting_edges =
	    findSplittingEdges(r0_vertex, sides_to_regions, candidate.regions);

	// assign two integer indices to each splitting edge in candidate region 0 (the static region),
	// one per each of its orientations, in a rotational order around this region; this data has to be
	// calculated before any change to the mesh is executed, but will only be used later
	absl::flat_hash_map<OrderedEdge, size_t> splitting_edge_to_id =
	    orderSplittingEdges(r0_vertex, splitting_edges);

	// iterate over splitting edges in candidate region 0, perform the splitting, so that `r0_vertex`
	// is the new split center for candidate region 0 (static center), and `r1_vertex` is the new
	// split center for candidate region 1 (pulled center) and all other static regions; split regions
	// will be adjacent to both `r0_vertex` and `r1_vertex`; if necessary, insert new triangles to
	// fill in holes to close off volumes that become connected by the pull apart process, and find
	// opposites of those HCs, for which it is possible (store them in `ref_hfc_to_oppos`); for HCs
	// for which it is not possible to determine their opposites (HCs at link vertices of newly
	// generated hole-filling triangles), assign to them the index of the local region they lie in
	// (store in `around_r0_r1_hfcs`)
	for (const SplittingEdge& edge_hfcs : splitting_edges) {
		// retrieve labels of the two exiting HCs of the current splitting edge
		Vec2i labels = {edge_hfcs[0]->getLabel(), edge_hfcs[1]->getLabel()};
		// compare the labels of the two exiting HCs of the current splitting edge
		if (labels[0] == labels[1]) {
			// if the two regions that become connected after splitting off the current splitting edge
			// have the same labels, no triangles are generated to separate them; reassign the HC
			// opposites - exiting HCs of the splitting edge become opposites of each other, the opposites
			// of the two exiting HCs become opposites of each other
			ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(edge_hfcs[0])] =
			    reinterpret_cast<uintptr_t>(edge_hfcs[1]);
			ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(edge_hfcs[1])] =
			    reinterpret_cast<uintptr_t>(edge_hfcs[0]);
			ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(edge_hfcs[0]->getOppos())] =
			    reinterpret_cast<uintptr_t>(edge_hfcs[1]->getOppos());
			ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(edge_hfcs[1]->getOppos())] =
			    reinterpret_cast<uintptr_t>(edge_hfcs[0]->getOppos());
		} else {
			// if the two regions that become joined after splitting off the current splitting edge have
			// different labels, a triangle is generated to separate them using the two endpoints of the
			// splitting edge and the pulled center `r1_vertex`; orientations and labels are correctly
			// matched to those on the triangles of exiting HCs; this is because the order of vertices on
			// the new triangle is chosen so that the orientation compatible with the orientation induced
			// by `edge_hfcs[0]` is associated with the same label as `edge_hfcs[0]`
			Mesh3DTriangle* new_triangle =
			    mesh.makeNewTriangle(edge_hfcs[0]->getPrev()->getVertex(),
			                         edge_hfcs[0]->getNext()->getVertex(), r1_vertex, labels);
			// store `new_triangle` inside the corner table as a T1 triangle; this information will be
			// used for building an adjacency map for smoothing in mesh upkeeper
			mesh.addT1HFTriangle(new_triangle);
			// save the edge (r0_vertex,r1_vertex) as a no-collapse edge; these edges are forbidden to be
			// collapsed during mesh upkeep, despite being short; had we not done this, collapsing this
			// edge would revert back to the unresolved T1 state
			mesh.addNoCollapseEdge(r0_vertex, r1_vertex);

			// retrieve the reference HC of `new_triangle`
			Mesh3DHalfCorner* hfc = new_triangle->getHalfCorner();
			// iterate over the 6 HCs of `new_triangle`, every HC is either at `r0_vertex` (static
			// center), at `r1_vertex` (pulled center), or at a vertex in the link of these two vertices
			// (link vertex); find opposites for the two split center vertices, and store them in
			// `ref_hfc_to_oppos`; assign to the link HC its local region index in `around_r0_r1_hfcs`
			for (int side = 0; side < 2; ++side, hfc = hfc->getDual()) {
				for (int i = 0; i < 3; ++i, hfc = hfc->getNext()) {
					// associate each HC of `new_triangle` with itself in `ref_hfc_to_new`
					ref_hfc_to_new[reinterpret_cast<uintptr_t>(hfc)] = hfc;
					// check if the vertex at `hfc` is a center or link vertex
					if (hfc->getVertex() != r0_vertex && hfc->getVertex() != r1_vertex) {
						// if `hfc` is a link vertex, add to `around_r0_r1_hfcs` the pair (`hfc`, local region
						// index of `hfc`)
						around_r0_r1_hfcs.push_back(hfc);
					} else {
						// if `hfc` is at a split center vertex (i.e. at `r0_vertex` or `r1_vertex`), find its
						// new opposite, that is, its opposite in the mesh after the pull apart (which contains
						// the newly generated `new_triangle`); at this point, the pull apart has yet to happen,
						// therefore we can use the pre-pull apart mesh to find the correct matching of HC
						// opposites, and only afterwards actually change the mesh; there are two possibilities:
						// -`hfc` is at the pulled center `r1_vertex`, its opposite will be `edge_hfcs[side]`
						// -`hfc` is at the static center `r0_vertex`, its opposite will be the opposite of
						// `edge_hfcs[side]`
						Mesh3DHalfCorner* target_oppos = edge_hfcs[side];
						if (hfc->getVertex() == r0_vertex) {
							target_oppos = target_oppos->getOppos();
						}
						// save `hfc` and `target_oppos` as opposites of each other in `ref_hfc_to_oppos`
						ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(target_oppos)] =
						    reinterpret_cast<uintptr_t>(hfc);
						ref_hfc_to_oppos[reinterpret_cast<uintptr_t>(hfc)] =
						    reinterpret_cast<uintptr_t>(target_oppos);
					}
				}
			}
		}
	}

	moveTrianglesToNewVertex(sides_to_regions, mesh, r0_vertex, r1_vertex, candidate.regions,
	                         ref_hfc_to_new);

	// assign HC opposites based on information stored in `ref_hfc_to_oppos` and in `ref_hfc_to_new`;
	// `ref_hfc_to_oppos` maps HCs to their correct opposites which contains: -for HC on static
	// triangles, each HC is associated with its correct opposite -for HC on pulled triangles, each HC
	// is associated with the HC
	for (auto& [ref, oppos] : ref_hfc_to_oppos) {
		Mesh3DHalfCorner* new_hfc = ref_hfc_to_new.at(ref);
		Mesh3DHalfCorner* new_oppos_hfc = ref_hfc_to_new.at(oppos);
		new_hfc->setOppos(new_oppos_hfc);
		new_oppos_hfc->setOppos(new_hfc);
	}

	// Assign opposites around (r1-r2).
	assignOpposAroundNewEdge(r0_vertex, around_r0_r1_hfcs, splitting_edge_to_id);

	return r1_vertex;
}

//------------------------------------------------------------
// utility functions
//------------------------------------------------------------

// return a vector of `PullApartCandidate`s around `vertex`, for which it holds that pulling them
// apart would locally decrease surface area
std::vector<T1Resolver::PullApartCandidate> T1Resolver::findPullApartCandidates(
    const std::vector<std::vector<int>>& regions_graph, Mesh3DVertex* vertex,
    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions) const {
	// precompute the sum of surface areas of all local regions around `vertex` (i.e. the sum of areas
	// of all triangles containing `vertex`)
	double original_area = 0;
	double av_edge_len = 0;
	size_t num_edges = 0;
	for (const auto& [side, region] : sides_to_regions) {
		original_area += side.first->getArea();
		std::vector<Mesh3DVertex*> verts = side.first->getVerts();
		for (size_t i = 0; i < verts.size(); ++i) {
			av_edge_len += dist(verts[i]->getCoords(), verts[(i + 1) % verts.size()]->getCoords());
			++num_edges;
		}
	}
	// we counted the area of each triangle twice (once per side), we therefore divide by 2 to avoid
	// double counting
	original_area /= 2;
	av_edge_len /= num_edges;

	// return vector that stores `PullApartCandidate`s
	std::vector<PullApartCandidate> candidates;
	// iterate over all pairs of local regions
	for (size_t i = 0; i < regions_graph.size(); ++i) {
		for (size_t j = i + 1; j < regions_graph.size(); ++j) {
			// we only check if regions should be pulled apart, if they are not connected via a triangle
			// face
			if (regions_graph[i][j] != 0) {
				continue;
			}

			// number of mesh vertices in the link of `vertex` that lie in local regions `i` and `j`
			// respectively (i.e. i-link vertices and j-link vertices)
			size_t r0_count = 0;
			size_t r1_count = 0;
			// coordinates of the average of i- and j-link vertices respectively
			Vec3d r0_center(0.0);
			Vec3d r1_center(0.0);

			// for both regions `i` and `j`, find the number and coordinate sum of their link vertices;
			// each such vertex is contained in exactly two triangles that are adjacent to `vertex`,
			// therefore we technically double count; however, this doesn't matter, since in the next step
			// we divide the coordinate sum of i- and j-link vertices by their numbers - both are double
			// counted, therefore this operation gives us the correct average coordinate position of i-
			// and j-link vertices respectively
			for (const auto& [side, region] : sides_to_regions) {
				// only consider `TriSide`s that are in local region `i` or `j`
				if (region != i && region != j) {
					continue;
				}
				// retrieve reference HC of the triangle of `side`
				Mesh3DHalfCorner* hfc = side.first->getHalfCorner();
				// iterate over the 3 vertices of this traingle
				for (int edge_id = 0; edge_id < 3; edge_id++, hfc = hfc->getNext()) {
					const Mesh3DVertex* current_vert = hfc->getVertex();
					// skip `vertex`, add the coordiantes and number of link vertices
					if (current_vert != vertex) {
						if (region == i) {
							r0_center += current_vert->getCoords();
							r0_count++;
						} else {
							r1_center += current_vert->getCoords();
							r1_count++;
						}
					}
				}
			}

			// ASSERT: there should be at least 3 i-link vertices and at least another 3 j-link vertices;
			// note that `r1_count` and `r2_count` are equal to double the number of link vertices in
			// regions `i` and `j` respectively, due to double counting
			assert(r0_count > 5 && r1_count > 5);

			// magnitude and direction of the pull is determined by the difference of the link vertex
			// average positions in local region `i` and local region `j`
			Vec3d offset = 0.5 * av_edge_len *
			               normalized(r0_center / static_cast<double>(r0_count) -
			                          r1_center / static_cast<double>(r1_count));
			// strength of the pull is determined by the difference between the local surface area before
			// and after a small constant pull
			double pull_away_strength =
			    original_area - getAreaAfterPullAway(vertex, offset, {i, j}, sides_to_regions);

			// if `pull_away_strength` is positive, add a `PullApartCandidate` consisting of local regions
			// `i` and `j`, `direction`, and `pull_away_strength` to the return vector
			// ASK: can it happen that `pull_away_strength` is <0?
			// NOTE: we add candidates even if `pull_away_strength` is not positive; this will ensure that
			// all vertices are T1 resolved
			if (pull_away_strength > 0 || settings->allow_area_increasing_t1) {
				candidates.push_back({{i, j}, offset, pull_away_strength});
			}
		}
	}

	// return the vector of `PullApartCandidate`s
	return candidates;
}

// calculate total surface area of triangles touching the two split center vertices originating from
// original center `vertex`, were the pull apart process between `regions` in `direction` to happen
double T1Resolver::getAreaAfterPullAway(
    Mesh3DVertex* vertex, const Vec3d offset, const Vec2st regions,
    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions) const {
	// store current coordinates of `vertex`, so that they can be reset back to this value later
	Vec3d original_coords = vertex->getCoords();
	// coordinates of original center `vertex`, were it to be offset by positive and negative
	// `offset`; we use these augmented coordinates to determine how much would pulling `regions`
	// apart by a small amount decrease local surface area; `direction` is defined in
	// `findPullApartCandidates` as a vector from `r1center` to `r0_center`
	Vec3d r0_new_pos = original_coords + offset;
	Vec3d r1_new_pos = original_coords - offset;

	// sum of areas of local triangles, i.e. triangles that touch at least one of the two vertices
	// that `vertex` would split into were the pull apart process to happen
	double new_area = 0.0;
	// iterate over pairs (TriSide,local region) adjacent to `vertex`, for each associated triangle,
	// calculate its area after pulling apart, and add it to `new_area`; there are several cases to
	// consider:
	// 1. static triangles - existing triangles that have one side in static region `regions[0]` will
	// use `r0_new_pos` as position of their split vertex
	// 2. pulled triangles - all other existing triangles (those that have neither side in the static
	// region `regions[0]`) will use `r1_new_pos` as position of their split vertex
	// 3. hole-filling triangles - new triangles, generated to fill the holes created by the pull
	// apart process; these will be handled later
	// ASK: we pull `regions[1]` away from `regions[0]`, and together with it a potentially high
	// number of other local regions; would we get the same result if we pulled `regions[0]` away from
	// `regions[1]`, so that all the other local regions would use `r0_new_pos` just like `regions[0]?
	for (const auto& [side, region] : sides_to_regions) {
		Mesh3DTriangle* tri = side.first;
		if (sides_to_regions.at({tri, tri->getLabel(false)}) == regions[0] ||
		    sides_to_regions.at({tri, tri->getLabel(true)}) == regions[0]) {
			// case 1.
			vertex->setCoords(r0_new_pos);
		} else {
			// case 2.
			vertex->setCoords(r1_new_pos);
		}
		// add area of `tri` with the augmented `vertex` coordinates
		new_area += tri->getArea();
	}
	// reset coordinates of `vertex` to their original value
	vertex->setCoords(original_coords);
	// divide `new_area` by 2, because we added each triangle's area twice (once per each of its
	// `TriFace`s)
	new_area /= 2;

	// add to `new_area` areas of triangles falling under case 3. above
	for (const auto& new_triplets :
	     generateHoleFillingTris(vertex, vertex, sides_to_regions, regions)) {
		// retrieve the hole filling triangles needed to close the mesh after the pull apart process;
		// they are represented as triplets of mesh vertices: the two vertices that `vertex` is split
		// into (split centers), and one vertex in the link of `vertex`; in this call of the function
		// `generateHoleFillingTris`, we are only interested in getting the position of the vertex in
		// the link of `vertex`, because for the purposes of calculating the area of the hole filling
		// triangle we already know the positions of the two vertices that `vertex` is split into
		// (`r0_new_pos`, and `r1_new_pos`); as such, we can just send `vertex` into function
		// generateHoleFillingTris twice, in place of the actual two split center vertices; this will no
		// longer be the case later when we actually want to generate the hole filling triangles and
		// add them to the mesh corner table

		// retrieve coordinates of the vertex of the current hole filling triangle, which lies in the
		// link of `vertex`
		Vec3d non_edge_pos(0.0);
		for (const Mesh3DVertex* v : new_triplets) {
			// we sent `vertex` to function `generateHoleFillingTris` twice, therefore there will be
			// exactly one vertex `v` that is different than `vertex` - a vertex in the link of `vertex`
			if (v != vertex) {
				non_edge_pos = v->getCoords();
				break;
			}
		}
		// add the area of the hole filling triangle
		new_area += mag(cross(r0_new_pos - non_edge_pos, r1_new_pos - non_edge_pos)) / 2;
	}

	return new_area;
}

// generate a vector of triplets of vertices representing hole-filling triangles
std::vector<std::vector<Mesh3DVertex*>> T1Resolver::generateHoleFillingTris(
    Mesh3DVertex* r0_vertex, Mesh3DVertex* r1_vertex,
    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions,
    Vec2st regions) const {
	// return vector of hole-filling triangles; they are represented as triplets of mesh vertices,
	// rather than `Mesh3DTriangle` objects; this is because some calls of this function (from
	// function `getAreaAfterPullAway`) aim to retrieve the triangles only for the purpose of
	// calculating their surface area, not to actually generate them and add them to the mesh corner
	// table
	std::vector<std::vector<Mesh3DVertex*>> triangles_as_triplets;
	// iterate over `SplittingEdge`s adjacent to the static region `regions[0]`, for each one check
	// whether the regions that would get connected by the pull apart process have different labels -
	// if yes, generate a hole filling triangle triplet
	for (const SplittingEdge& hfcs : findSplittingEdges(r0_vertex, sides_to_regions, regions)) {
		// ASSERT: there have to be exactly two exiting HCs saved on a `SplittingEdge` (exactly two
		// triangles extending the `SplittingEdge` that are adjacent to the static region `regions[0]`
		assert(hfcs.size() == 2);
		// if the labels on both exiting HCs match, the pull apart process creates a tunnel between
		// regions with the same material - a hole-filling triangle will not be generated
		if (hfcs[0]->getLabel() == hfcs[1]->getLabel()) {
			continue;
		}
		// add a triangle triplet representing the hole-filling triangle to `triangles_as_triplets`
		triangles_as_triplets.push_back(
		    {hfcs[0]->getPrev()->getVertex(), hfcs[0]->getNext()->getVertex(), r1_vertex});
	}

	return triangles_as_triplets;
}

// return a vector of `SplittingEdge`s of static region `regions[0]` around the static center
// `r0_vertex`
std::vector<T1Resolver::SplittingEdge> T1Resolver::findSplittingEdges(
    Mesh3DVertex* r0_vertex,
    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions,
    Vec2st regions) const {
	// region index of the local region that is not moved, i.e. the static region as explained in the
	// function header
	size_t static_region = regions[0];
	// map that to each split mesh edge assigns its exiting HCs and adjacent split region indices
	// (explained in function header); edges are stored in a sorted way to avoid having to query for
	// orientation
	absl::flat_hash_map<SortedMeshEdge, std::vector<Mesh3DHalfCorner*>> region_hfcs_across_edge;

	absl::flat_hash_set<Mesh3DTriangle*> adjacent_tris;

	// iterate over pairs (`TriSide`, local region index), in order to fill in the map
	// `region_hfcs_across_edge` that stores all `SortedMeshEdge`s that are to be split, and assignes
	// to each a vector of pairs (HC of triangle in `Triside` that is opposite this edge and in a
	// split region (this defines it uniquely, call it "exiting HC"), local region index of this split
	// region)
	for (const auto& [side, side_region] : sides_to_regions) {
		// split edges can only be adjacent to `static_region`; if the region of the current `TriSide`
		// (`side_region`) is different (i.e. a split region), skip to next TriSide
		if (side_region != static_region) {
			continue;
		}

		// store the triangle and its reference HC of the current `TriSide`
		Mesh3DTriangle* tri = side.first;
		Mesh3DHalfCorner* hfc = tri->getHalfCorner();

		adjacent_tris.insert(tri);

		// if `hfc` (0-orientation HC of `tri`) lies inside `static_region` (i.e. has the same label as
		// `side`), take its dual (so that it lies in the adjacent split region)
		if (hfc->getLabel() == side.second) {
			hfc = hfc->getDual();
		}

		// for each of the two mesh edges of `tri` that touch the center vertex, if it is a split edge,
		// i.e. if it is non-manifold, add a new entry for this mesh edge into
		// `region_hfcs_across_edge`.
		for (int i = 0; i < 3; ++i, hfc = hfc->getNext()) {
			// skip checks across the edge not adjacent to the center vertex
			if (hfc->getVertex() == r0_vertex) {
				continue;
			}
			// check if the edge that the current HC extends is a splitting edge by checking whether the
			// dual of the HC opposite the current HC lies in `static_region`; if yes, the edge won't be
			// split; if not, the edge will be split
			Mesh3DHalfCorner* trial_hfc = hfc->getOppos()->getDual();
			if (sides_to_regions.at({trial_hfc->getTri(), trial_hfc->getLabel()}) == static_region) {
				continue;
			}
			// add a new entry into `region_hfcs_across_edge` for the split edge
			region_hfcs_across_edge[{hfc->getNext()->getVertex(), hfc->getPrev()->getVertex()}].push_back(
			    hfc);
		}
	}

	// cast values from `region_hfcs_across_edge` into objects of type `SplittingEdge` and push them
	// into the return vector `splitting_edges`
	std::vector<SplittingEdge> splitting_edges;
	splitting_edges.reserve(region_hfcs_across_edge.size());
	// iterate over the map `region_hfcs_across_edge`, `bounding_hfcs` is a vector of pairs (exiting
	// HC, adjacent split region index)
	for (const auto& [edge, bounding_hfcs] : region_hfcs_across_edge) {
		// ASSERT: there should be exactly two exiting HCs per split edge
		assert(bounding_hfcs.size() == 2);
		// store the split edge in an object of type `SplittingEdge` as:
		// -a vector of exiting HCs
		// -a pair of adjacent split region indices
		splitting_edges.push_back({{bounding_hfcs[0], bounding_hfcs[1]}});
	}
	// return the vector of `SplittingEdge`s around the pulled region
	return splitting_edges;
}

// returns a map that to each splitting edge that touches `r0_vertex` in an implicitly defined local
// region r0 (the static region) assigns two integer ids (one per each of its orientations) in
// rotational order around r0
absl::flat_hash_map<T1Resolver::OrderedEdge, size_t> T1Resolver::orderSplittingEdges(
    Mesh3DVertex* r0_vertex, const std::vector<SplittingEdge>& splitting_edges) const {
	// if there are no input splitting edges, return an empty map
	if (splitting_edges.empty()) {
		return {};
	}

	// return map that to a splitting edge in r0 assigns two integer indices, one per each of its
	// orientations, in a rotational order around r0
	absl::flat_hash_map<T1Resolver::OrderedEdge, size_t> edge_to_id;
	// indexing variable
	size_t current_id = 0;
	// HCs used for traversal around r0
	// Take dual, so that we end up in the static region.
	Mesh3DHalfCorner* starting_hfc = splitting_edges[0][0]->getDual();
	Mesh3DHalfCorner* current_hfc = starting_hfc;
	// traverse rotationally around limiting HCs of r0 until arriving back at `starting_hfc`
	do {
		Mesh3DHalfCorner* oppos_hfc = current_hfc->getOppos();

		// assign two integer indices to the edge between `current_hfc` and `oppos_hfc`, one per each of
		// its orientations
		edge_to_id[{current_hfc->getNext()->getVertex(), current_hfc->getPrev()->getVertex()}] =
		    current_id;
		edge_to_id[{oppos_hfc->getNext()->getVertex(), oppos_hfc->getPrev()->getVertex()}] =
		    current_id + 1;
		current_id += 2;

		// set `current_hfc` to be the other limiting HC of r0 in the same triangle as `oppos_hfc`
		current_hfc = oppos_hfc->getNext();
		if (current_hfc->getVertex() == r0_vertex) {
			current_hfc = oppos_hfc->getPrev();
		}
	} while (starting_hfc != current_hfc);

	return edge_to_id;
}

// sides_to_regions, mesh, r0_vertex, r1_vertex, candidate.regions, ref_hfc_to_new, vert_to_tris
void T1Resolver::moveTrianglesToNewVertex(
    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions, Mesh3DInterface& mesh,
    Mesh3DVertex* r0_vertex, Mesh3DVertex* r1_vertex, Vec2st regions,
    absl::flat_hash_map<uintptr_t, Mesh3DHalfCorner*>& ref_hfc_to_new) const {
	// helper set to track which triangles have already been processed in order to avoid double
	// processing
	absl::flat_hash_set<Mesh3DTriangle*> processed_tris;
	// vector of triangles that are to be deleted; at the end of the function, they are marked for
	// deletion, and finally deleted at the end of each main loop iteration in `resolveVertices`
	std::vector<Mesh3DTriangle*> tobedeleted_triangles;

	// iterate over the map with entries (`TriSide`, local region index), in order to process all
	// triangles (stored in `TriSide`s) that were adjacent to the original center before the pull
	// apart process started; there are two cases to consider:
	// -triangle of `TriSide` is a static triangle: it won't change in any way, and so the only thing
	// we do is use one of its HCs as the reference HC of the static center `r0_vertex`; we have to do
	// this, because it could have happened that the reference HC of `r0_vertex` was a HC on one of
	// the pulled triangles, which used to be adjacent to `r0_vertex` before the pull apart process
	// started, but is no longer adjacent to `r0_vertex` after the pull apart is completed
	// -triangle of `TriSide` is a pulled triangle:
	for (const auto& [side, region] : sides_to_regions) {
		// store the existing mesh triangle of `side` as `ori_tri`; this is the triangle in the
		// pre-pull apart state; if it is a pulled triangle, it will be set to be deleted, and a new
		// triangle will replace it; if it is a static triangle, it won't be changed or deleted
		Mesh3DTriangle* ori_tri = side.first;

		// check if `ori_tri` was already processed (i.e. via its other `side`); if yes, continue to the
		// next (triangle side, local region index) pair; if not, insert it in `processed_tris`
		auto [it, is_inserted] = processed_tris.insert(ori_tri);
		if (!is_inserted) {
			continue;
		}

		// collect the local region index on the other side of `side`
		size_t other_region = sides_to_regions.at({ori_tri, ori_tri->getLabel(false)});
		if (other_region == region) {
			other_region = sides_to_regions.at({ori_tri, ori_tri->getLabel(true)});
		}

		// check if `ori_tri` is not a static triangle
		if (region != regions[0] && other_region != regions[0]) {
			// if not, i.e. `ori_tri` is not adjacent to candidate region 0, and therefore is a pulled
			// triangle, we proceed to generate a new triangle to replace `ori_tri`, which will instead of
			// `r0_vertex` (previously the original center, now the static center) touch `r1_vertex` (the
			// pulled center)

			// collect vertices of `ori_tri`, they will be used to generate a triangle to replace
			// `ori_tri`
			std::vector<Mesh3DVertex*> verts = ori_tri->getVerts();
			// switch the center vertex in `verts` from `r0_vertex` to `r1_vertex`
			for (auto& tri_vert : verts) {
				if (tri_vert == r0_vertex) {
					tri_vert = r1_vertex;
				}
			}

			// generate a triangle to replace `ori_tri`, using the modified `verts` (`r0_vertex` is
			// replaced with `r1_vertex`), in the same 0-orientation, and the same pair of labels as
			// `ori_tri`
			Mesh3DTriangle* new_tri =
			    mesh.makeNewTriangle(verts[0], verts[1], verts[2], ori_tri->getLabels());
			// save it as a T1 triangle in the corner table
			mesh.addT1Triangle(new_tri);

			// set the opposites of the two HCs of `new_tri` at `r1_vertex` - they are the same as the
			// opposites of HCs of `ori_tri` at `r0_vertex`; additionally, `ori_tri` and `new_tri` have
			// their 0-orientation in the same region, therefore we match primal to primal and dual to
			// dual
			Mesh3DHalfCorner* ori_tri_center_hfc = ori_tri->getHalfCornerAtVertex(r0_vertex);
			Mesh3DHalfCorner* new_tri_center_hfc = new_tri->getHalfCornerAtVertex(r1_vertex);
			Mesh3DHalfCorner* center_oppos_hfc = ori_tri_center_hfc->getOppos();
			Mesh3DHalfCorner* dual_center_oppos_hfc = ori_tri_center_hfc->getDual()->getOppos();
			new_tri_center_hfc->setOppos(center_oppos_hfc);
			new_tri_center_hfc->getDual()->setOppos(dual_center_oppos_hfc);
			center_oppos_hfc->setOppos(new_tri_center_hfc);
			dual_center_oppos_hfc->setOppos(new_tri_center_hfc->getDual());

			// HCs for iteration over `ori_tri` and `new_tri`
			Mesh3DHalfCorner* new_tri_hfc = new_tri_center_hfc;
			Mesh3DHalfCorner* ori_tri_hfc = ori_tri_center_hfc;
			// iterate over the 6 pairs of corresponding HCs of `ori_tri` and `new_tri`, for the 4 HCs at
			// link vertices, store into `ref_hfc_to_new` the pair (`ori_tri` HC, corresponding `new_tri`
			// HC), WHY?
			for (int hfc_side = 0; hfc_side < 2;
			     ++hfc_side, new_tri_hfc = new_tri_hfc->getDual(), ori_tri_hfc = ori_tri_hfc->getDual()) {
				for (int i = 0; i < 3;
				     ++i, new_tri_hfc = new_tri_hfc->getNext(), ori_tri_hfc = ori_tri_hfc->getNext()) {
					// skip over HCs at the pulled center `r1_vertex`
					if (new_tri_hfc->getVertex() == r1_vertex) {
						continue;
					}
					ref_hfc_to_new[reinterpret_cast<uintptr_t>(ori_tri_hfc)] = new_tri_hfc;
				}
			}
			// push `ori_tri` to be deleted
			tobedeleted_triangles.push_back(ori_tri);
		}
	}

	// remove these triangles from mesh and marching cubes triangle sets (stored in the corner table)
	for (Mesh3DTriangle* del_tri : tobedeleted_triangles) {
		mesh.deleteTriangle(del_tri);
		mesh.getMCTriangles().erase(del_tri);
		mesh.getT1Triangles().erase(del_tri);
		mesh.getT1HFTriangles().erase(del_tri);
	}
}

//------------------------------------------------------------
// to be checked functions
//------------------------------------------------------------

void T1Resolver::assignOpposAroundNewEdge(
    Mesh3DVertex* r1_vertex, const std::vector<Mesh3DHalfCorner*>& around_r1_r2_hfcs,
    const absl::flat_hash_map<OrderedEdge, size_t>& splitting_edge_to_id) const {
	std::vector<std::pair<Mesh3DHalfCorner*, size_t>> hfc_with_id;
	for (Mesh3DHalfCorner* hfc : around_r1_r2_hfcs) {
		size_t id = -1;
		if (hfc->getNext()->getVertex() == r1_vertex) {
			id = splitting_edge_to_id.at({hfc->getVertex(), r1_vertex});
		} else {
			id = splitting_edge_to_id.at({r1_vertex, hfc->getVertex()});
		}
		hfc_with_id.push_back({hfc, id});
	}

	std::sort(hfc_with_id.begin(), hfc_with_id.end(),
	          [](auto& left, auto& right) { return left.second < right.second; });

	for (size_t i = 0, n = hfc_with_id.size(); i < n; ++i) {
		Mesh3DHalfCorner* first = hfc_with_id[i].first;
		Mesh3DHalfCorner* second = hfc_with_id[(i + 1) % n].first;
		// If half-corners are from the same triangle, don't make them opposites.
		if (first->getTri() == second->getTri()) {
			continue;
		}
		first->setOppos(second);
		second->setOppos(first);
	}
}
