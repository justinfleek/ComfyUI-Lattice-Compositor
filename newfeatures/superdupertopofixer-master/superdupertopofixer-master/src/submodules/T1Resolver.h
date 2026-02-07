/* T1Resolver.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * Submodule that finds and resolves vertices that don't have fully connected manifold regions,
 * similar to Los Topos [Da et al., 2014].
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

class T1Resolver {
 public:
	T1Resolver(const TopoFixerSettings& settings) : settings(&settings) {}
	// Main function guiding the resolution of T1 degeneracies, i.e. configurations where a vertex is
	// adjacent to 3+ local regions, and there exists a pair of local regions that are not adjacent
	// via a triangle face.
	void resolveVertices(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                     const absl::flat_hash_set<Mesh3DVertex*>& candidates) const;

 private:
	const TopoFixerSettings* settings;

	// pair (triangle,label on triangle); each triangle has 2 labels, and therefore 2 possible
	// `TriSide`s
	using TriSide = Mesh3DInterface::TriSide;
	// ordered pair of mesh vertices that defines the endpoints of a mesh edge, thus implicitly also
	// storing the edge's orientation
	using OrderedEdge = std::pair<Mesh3DVertex*, Mesh3DVertex*>;

	// Pairs of `regions` around a vertex that are not adjacent via a triangle face, and could
	// therefore be pulled apart (`regions[0]` is the static region, `regions[1]` is a pulled region).
	// If that were to happen, they should be pulled apart with plus-minus `offset`. Eventually, we
	// will want to pull apart the `PullApartCandidte` that causes the largest local area decrease.
	// The amount by which the local area would decrease upon pulling apart is stored in `strength`.
	// `PullApartCandidate`s are stored per mesh vertex, and therefore the center vertex
	// itself is not stored.
	struct PullApartCandidate {
		Vec2st regions;
		Vec3d offset;
		double strength;

		// the smaller `PullApartCandidate` is the one with the lower strength
		bool operator<(const PullApartCandidate& other) const { return strength < other.strength; }
	};

	// Represents a mesh edge connecting the central vertex to a link vertex, and is adjacent to two
	// triangles that will no longer share an edge once the pull apart process happens (a static and a
	// pulled triangle). As such, the edge will be duplicated into two edges, each connecting the link
	// vertex to one of the new split center vertices that replace the original center vertex. This
	// creates a triangular hole between link vertex and the two split center vertices, which connects
	// two local regions. If these two local regions have the same label, the gap is left empty.
	// Otherwise a new triangle is generated to fill it.
	// Stored as HCs extending the splitting edge, lying on static triangles, on the side of the split
	// regions. Note that the edge itself is identified as the edge that both `half_corners` extend.
	using SplittingEdge = std::array<Mesh3DHalfCorner*, 2>;

	// ---------------- functions that resolve T1 degenerate configurations

	// Returns a new vertex that was created as a part of a pull apart process performed with
	// candidate regions. The gist of it is that triangles whose sides belong to region
	// candidates.regions[0] keep the same vertices, other triangles have an original vertex replaced
	// by the newly created one. If there are holes between regions, they will be filled in by newly
	// created triangles. The most complex part is reassigning opposites for new half-corners. Here we
	// rely on several criteria. Firstly, if only two half-corners extend the same edge at the same
	// region, then we match them. Otherwise, we reuse old connectivity to match as many half-corners
	// as possible. For newly created triangles we know exactly the connect to the old mesh, so we
	// connect those as well. The only half-corners remaining will be those around edge connecting the
	// old and the newly pulled apart vertex. But for those we can use the order of edges to figure
	// the opposites.
	Mesh3DVertex* pullVertexApart(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                              Mesh3DVertex* r1_vertex, const PullApartCandidate& candidate,
	                              const absl::flat_hash_map<TriSide, size_t>& sides_to_regions) const;

	// ---------------- utility functions

	// Returns a vector of `PullApartCandidates`, which contains all pairs of local regions around
	// `vertex` that do not share a triangle, and for which it holds that pulling them apart would
	// locally decrease surface area. Along with the pair of local region indices are stored the
	// direction of the pull (defined as the vector connecting the average link vertex position of the
	// two local regions), and the strength of the pull (defined as the local surace area decrease
	// were the pull to happen). `regions_graph` is an adjacency matrix of local regions around
	// `vertex` (computed in `buildRegionsGraph`), and `sides_to_regions` maps `TriSide`s around
	// `vertex` to the index of the local region they lie in (computed in `uniteTrianglesInRegions`).
	std::vector<PullApartCandidate> findPullApartCandidates(
	    const std::vector<std::vector<int>>& regions_graph, Mesh3DVertex* vertex,
	    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions) const;

	// We define several terms to make the exposition clearer. There are several mesh vertices
	// associated to the pulling apart process:
	// I. original center - vertex that is adjacent to at least one pair of local legions that do not
	// share a triangle, thus warranting a pulling apart attempt
	// II. split centers - two vertices that replace original center, both offset from its position by
	// a miniscule amount; they are:
	// II.I static (split) center - the split center into which original center turns
	// II.II pulled (split) center - a newly generated split center
	// III. link vertices - all vertices that are in the link of original center before pulling apart,
	// and in the link of at least one of the split centers after pulling apart. For local region i we
	// also use the expression i-link vertices, to refer to link vertices in local region i.
	//
	// There are three types of local regions associated to the pulling apart process:
	// 1. static region - this is the one region that remains unchanged as all the other regions are
	// pulled away from it; all triangles in such region touch static center, none touch pulled center
	// 2. pulled regions - one or more regions that are pulled away from static region in order to
	// decrease complexity of the adjacency graph at original center; all triangles in pulled regions
	// touch pulled center, none touch static center
	// 3. split regions - one or more regions between static region and pulled regions. These regions
	// are the ones whose adjacency to other regions changes as a consequence of the pull apart
	// process; each such region has triangles that touch static center, as well as triangles that
	// touch pull center; if it is necessary to generate hole-filling triangles (because the newly
	// adjacent regions have different material labels), then these are exactly the triangles that
	// touch both static and pulled center.
	//
	// There are three types of triangles associated to the pulling apart process:
	// a) static triangles - triangles that have one side in the static region; they always deliminate
	// the static region and one split region; they touch static center, and don't touch pulled center
	// b) pulled triangles - triangles that have at least one side in a pulled region; they deliminate
	// either two pulled regions, or one pulled region and one split region; they touch pulled center
	// and don't touch static center
	// c) hole-filling triangles - these are newly generated triangles that close the hole between
	// regions that become connected as a consequence of the pull apart process, but which have
	// matching material labels; they deliminate two split regions, and touch both split centers

	// Compute the local sum of triangle areas, that is, the sum of surface areas of triangles that
	// touch one of the two split center vertices, were the pull apart process to happen with vertices
	// moving by `offset` magnitude and direction. We assume `regions[0]` would be the static region,
	// while `regions[1]` would be a pulled region. We use this information as a metric to decide
	// which pair of non-adjacent local regions around `vertex` to split - we choose the pair that
	// causes the largest decrease in the local sum of triangle areas. There are 3 types of local
	// triangles to consider:
	// 1. static triangles that have a side lying in `regions[0]`, these will use a version of
	// `vertex` that is moved slightly towards the center of `regions[0]` (static center),
	// 2. pulled triangles, that is, remaining existing triangles, these will use a version of
	// `vertex` that is moved slightly towards the center of `regions[1]` (pulled center),
	// 3. hole-filling triangles, that is, new triangles that might be necessary to be generated, in
	// order to fill the hole created by the pull apart process.
	// No vertex positions are actually changed, and no new triangles are actually generated in this
	// function, all calculations are done in theory only.
	double getAreaAfterPullAway(
	    Mesh3DVertex* vertex, const Vec3d offset, const Vec2st regions,
	    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions) const;

	// Generate and return a vector of triplets of vertices representing hole-filling triangles that
	// close off volumes that become connected as `regions[1]` is pulled away from `regions[0]`. To
	// achieve this, we retrieve a vector of `SplittingEdge`s via function `findSplittingEdges`. Each
	// `SplittingEdge` corresponds to a hole created by the pull apart process between a pair of
	// previously locally non-adjacent (via a triangle face) local regions. A hole-filling triangle
	// triplet is generated if the labels on this pair of local regions are different. A triangle
	// generated from such a triplet then ensures that regions with different material labels remain
	// separated after the pull apart process. The triplet consists of the two split centers
	// `r0_vertex` and `r1_vertex`, and one link vertex.
	std::vector<std::vector<Mesh3DVertex*>> generateHoleFillingTris(
	    Mesh3DVertex* r0_vertex, Mesh3DVertex* r1_vertex,
	    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions,
	    Vec2st regions) const;

	// Returns a vector of `SplittingEdge`s of the static region `regions[0]` around the original
	// center vertex `r0_vertex`. NOTE: some data structures used could be defined as eg. pairs
	// instead of vectors
	std::vector<SplittingEdge> findSplittingEdges(
	    Mesh3DVertex* r0_vertex,
	    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions,
	    Vec2st regions) const;

	// Returns a map that to each splitting edge touching `r0_vertex` in a specific region r0 (being
	// the region for which the splitting edges are calculated, and therefore implicitly defined by
	// the input data, in practice the static region) assigns two integer ids (one per each of its
	// orientations), starting from zero. Every triangle that deliminates r0 has exactly two HCs that
	// don't touch `r0_vertex`, and that are not on the r0 side of the triangle. We call such HCs the
	// "limiting HCs" of local region r0. In particular, the exiting HCs of all splitting edges
	// touching local region r0 are also limiting HCs of r0. The indexing is achieved by traversing
	// along limiting HCs in a rotational order, either by jumping between the two exiting HCs of a
	// `SplittingEdge`, or by taking HC opposites, if there is no `SplittingEdge` between a HC and its
	// opposite (and therefore after taking the opposite, the HC we arrive at is still a limiting HC
	// of r0). Consequently, the indexing of splitting edges is done in a rotational order around r0.
	absl::flat_hash_map<T1Resolver::OrderedEdge, size_t> orderSplittingEdges(
	    Mesh3DVertex* r0_vertex, const std::vector<SplittingEdge>& splitting_edges) const;

	// iterate over all triangles adjacent to r0_vertex and r1_vertex
	// ASK: why is the triangle deleted and not just its HCs reassigned?
	void moveTrianglesToNewVertex(
	    const absl::flat_hash_map<T1Resolver::TriSide, size_t>& sides_to_regions,
	    Mesh3DInterface& mesh, Mesh3DVertex* r1_vertex, Mesh3DVertex* r2_vertex, Vec2st regions,
	    absl::flat_hash_map<uintptr_t, Mesh3DHalfCorner*>& ref_hfc_to_new) const;

	// ---------------- to be checked functions

	void assignOpposAroundNewEdge(
	    Mesh3DVertex* r1_vertex, const std::vector<Mesh3DHalfCorner*>& around_r1_r2_hfcs,
	    const absl::flat_hash_map<OrderedEdge, size_t>& splitting_edge_to_id) const;
};