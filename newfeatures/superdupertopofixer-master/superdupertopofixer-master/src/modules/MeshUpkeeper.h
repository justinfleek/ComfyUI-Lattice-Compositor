/* MeshUpkeeper.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the module that performs mesh upkeep.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <tuple>

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../schemes/TopoFixerSettings.h"
#include "../submodules/Smoother.h"
#include "../submodules/T1Resolver.h"
#include "ModuleInterface.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the mesh upkeeper module
class MeshUpkeeper : public ModuleInterface {
 public:
	// constructors
	MeshUpkeeper(const TopoFixerSettings& settings);
	virtual ~MeshUpkeeper() = default;

	// functions
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersection,
	                int orientation) override;
	int runPreprocess(Mesh3DInterface& mesh, Grid3DInterface& grid) const;

	// Constructs adjacency map for vertices that are newly created by MarchingCuber and T1Resolver.
	// The boundary vertices lying on the complex front faces are added as neighbours of new vertices
	// but are not included as keys of the result. This allows to run smoothing directly on this
	// adjacency map.
	absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>>
	buildComplexRegionMeshVertexAdjacency(Mesh3DInterface& mesh, Grid3DInterface& grid) const;

	// Collapses edges around valence 3 vertices to make mesh have more valence.
	absl::flat_hash_set<Mesh3DVertex*> removeValenceThreeVerts(
	    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const;

	// Removes triangles whose shortest edge is shorter than the longest edge by a factor of
	// `kSlimTriangleTolerance`.
	absl::flat_hash_set<Mesh3DVertex*> collapseSlimTriangles(
	    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const;

	// Splits long edges into shorter ones based on the surrounding neighbourhood of edges.
	absl::flat_hash_set<Mesh3DVertex*> splitEdges(
	    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const;

	// Performs iterations of edges flips until no flip can be done anymore.
	absl::flat_hash_set<Mesh3DVertex*> flipEdges(
	    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const;
	// Checks non-manilodness of an edge and delaunay criterion of sum of opposing angles across edge
	// being greater than 180 degrees.
	bool shouldBeFlipped(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const;

	void setMinEdgeLength(double min_edge_length) { min_edge_length_ = min_edge_length; }
	void setMaxEdgeLength(double max_edge_length) { max_edge_length_ = max_edge_length; }

	T1Resolver* getT1Resolver() { return &t1_resolver_; }

	void clearState();

 private:
	bool shouldSplitEdge(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const;
	bool shouldBeCollapsed(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const;
	Vec3d getCollapseCoords(Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2) const;

	void removeNonexistentVertices(Mesh3DInterface& mesh,
	                               absl::flat_hash_set<Mesh3DVertex*>& vertices) const;

	// Returns a set of triangles created by MarchingCuber and T1 Resolver.
	absl::flat_hash_set<Mesh3DTriangle*> createdTriangles(Mesh3DInterface& mesh) const;

	// Detect and save triangles that are bordering `mc_tris`.
	void setMCImprovementBoundary(Mesh3DInterface& mesh,
	                              const absl::flat_hash_set<Mesh3DTriangle*>& mc_tris);
	// Returns false if any triangle adjacent to `hfc` edge is in `tris_to_avoid_`.
	bool isEdgeAllowed(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const;

	// Generate a set of edges to be processed from the set of adjacent `candidate_vertices`.
	absl::flat_hash_map<SortedMeshEdge, Mesh3DHalfCorner*> candidateEdges(
	    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidate_vertices) const;

	const TopoFixerSettings* settings;
	T1Resolver t1_resolver_;

	// Parameter determening if only MC triangles should be improved.
	bool improve_only_mcs_;
	// Triangles on the boundary of improvement region, restricting the edges that will be added to
	// processing queue.
	absl::flat_hash_set<Mesh3DTriangle*> tris_to_avoid_;

	// Defines length below which edges cannot be created.
	double min_edge_length_;
	// Defines length above which edges will be split.
	double max_edge_length_;
	// Controls which proportion of shortest / longest edge in a triangle is acceptable.
	const double kSlimTriangleTolerance;
	// Defines the size of the triangles angles above which the edges will be split to create
	// triangles with smaller angles.
	const double kMaxAngleSizeRad;
	const double kCosMaxAngleSize;

	// utilities for mesh smoothing
	JacobiSmoother smoother_;
	MeanCurveSmoother nc_smoother_;
	const int kNumSmoothingIters = 20;
};

class ImprovementMeshEdge {
 public:
	ImprovementMeshEdge(SortedMeshEdge edge, Mesh3DHalfCorner* hfc, double length);
	void fixHalfCorner(Mesh3DInterface& mesh);

	bool operator<(const ImprovementMeshEdge& other) const { return length_ < other.length_; }
	bool operator>(const ImprovementMeshEdge& other) const { return length_ > other.length_; }

	SortedMeshEdge getEdge() const { return edge_; };
	Mesh3DHalfCorner* getHalfCorner() const { return hfc_; };
	double getLength() const { return length_; };

 private:
	SortedMeshEdge edge_;
	Mesh3DHalfCorner* hfc_;
	double length_;
};