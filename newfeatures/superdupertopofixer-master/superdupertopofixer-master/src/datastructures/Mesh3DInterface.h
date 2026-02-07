/* Mesh3DInterface.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the mesh interface. It lists the virtual functions which are accessed by
 * modules and implemented in a child mesh class.
 *
 * TODO:
 * - add access and utility functions that will be implemented in child classes
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <algorithm>
#include <iostream>
#include <list>
#include <map>
#include <set>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "../utilities/UnionFind.h"
#include "../utilities/intersection/ExactnessPredicates.h"
#include "../utilities/vec.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DSaveState.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

class Mesh3DHalfCorner;
//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this interface defines functions that modules use to access the 3D mesh data structure
class Mesh3DInterface {
 public:
	// Enums
	enum class EdgeCollapseType { kNonValid, kRegular, kTetrahedron, kHoppe, kNumOfTypes };

	// constructors
	Mesh3DInterface();
	virtual ~Mesh3DInterface();

	// pair (triangle,label on triangle); each triangle has 2 labels, and therefore 2 possible
	// `TriSide`s
	using TriSide = std::pair<Mesh3DTriangle*, int>;

	// functions
	int intersectTriSegment(Mesh3DTriangle* triangle, Vec3d s0, Vec3d s1);
	int intersectTriSegmentNoVerts(Mesh3DTriangle* triangle, Mesh3DVertex* v0, Mesh3DVertex* v1);

	// retrieve mesh information
	virtual int getNumberLabels() const = 0;
	virtual double getAverageEdgeLength() const = 0;
	virtual double getMinEdgeLength() const = 0;
	virtual double getMaxEdgeLength() const = 0;

	virtual const absl::flat_hash_set<Mesh3DTriangle*>& ListTriangles() const = 0;
	virtual const absl::flat_hash_set<Mesh3DVertex*>& ListVertices() const = 0;
	virtual const absl::flat_hash_set<Mesh3DHalfCorner*>& ListHalfCorners() const = 0;

	virtual void clearEdgeCollapseCounters() = 0;
	virtual void addT1RetractionEdgeCollapseCancel() = 0;
	virtual void addTetrahedronEdgeCollapseCancel() = 0;
	virtual void addInPlaneFlipEdgeCollapseCancel() = 0;
	virtual void addHoppeCriterionEdgeCollapseCancel() = 0;
	virtual void addDoubleFourValenceEdgeCollapseCancel() = 0;
	virtual void addCandidateCoveringEdgeCollapseCancel() = 0;
	virtual int getT1RetractionEdgeCollapseCancel() = 0;
	virtual int getTetrahedronEdgeCollapseCancel() = 0;
	virtual int getInPlaneFlipEdgeCollapseCancel() = 0;
	virtual int getHoppeCriterionEdgeCollapseCancel() = 0;
	virtual int getDoubleFourValenceEdgeCollapseCancel() = 0;
	virtual int getCandidateCoveringEdgeCollapseCancel() = 0;

	virtual absl::flat_hash_set<Mesh3DTriangle*>& getMCTriangles() = 0;
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getMCTriangles() const = 0;
	virtual void addMCTriangle(Mesh3DTriangle* triangle) = 0;
	virtual absl::flat_hash_set<Mesh3DTriangle*>& getT1Triangles() = 0;
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getT1Triangles() const = 0;
	virtual void addT1Triangle(Mesh3DTriangle* triangle) = 0;
	virtual absl::flat_hash_set<SortedMeshEdge>& getNoCollapseEdges() = 0;
	virtual const absl::flat_hash_set<SortedMeshEdge>& getNoCollapseEdges() const = 0;
	virtual void addNoCollapseEdge(Mesh3DVertex* v0, Mesh3DVertex* v1) = 0;
	virtual absl::flat_hash_set<Mesh3DTriangle*>& getT1HFTriangles() = 0;
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getT1HFTriangles() const = 0;
	virtual void addT1HFTriangle(Mesh3DTriangle* triangle) = 0;

	// other functions for getting to mesh elements
	// virtual void get_halfcorner_opp_edge(Mesh3DHalfCorner* opp_halfcorner, int& v1, int& v2) = 0;

	// Functions to traverse the mesh.
	virtual void walkManifoldLoop(Mesh3DVertex* center, Mesh3DHalfCorner* start_halfcorner,
	                              std::vector<Mesh3DHalfCorner*>& output_corners) = 0;

	// retrieve data for drawing
	virtual void getVertexPositions(std::vector<Vec3d>& vertex_positions) = 0;
	virtual Vec3d getMeshCenter() = 0;

	// mesh operations:

	virtual Mesh3DVertex* triangleSubdivFixedPoint(Mesh3DTriangle*& main_triangle,
	                                               Mesh3DTriangle*& second_triangle,
	                                               Mesh3DTriangle*& third_triangle,
	                                               Vec3d vert_coords) = 0;
	virtual Mesh3DVertex* EdgeSubdivisionFixedPoint(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d vert_coords,
	    std::vector<Mesh3DTriangle*>& created_triangles) = 0;
	virtual void transferValuesEdgeSubdivision(Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                           Mesh3DVertex* new_vertex) = 0;

	virtual bool EdgeFlipFast(Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2) = 0;

	virtual EdgeCollapseType edgeCollapse(Mesh3DTriangle* triangle, Mesh3DVertex* v1,
	                                      Mesh3DVertex* v2, Vec3d new_coords) = 0;

	virtual Vec3d pVertCoords(Mesh3DVertex* v1, Mesh3DVertex* v2, double p) = 0;

	//--------------------------MESH INFORMATION----------------------------------
	virtual int getNumberTris() const = 0;
	virtual int getNumberVerts() const = 0;
	virtual void walkAroundEdge(Mesh3DHalfCorner* start_halfcorner,
	                            std::vector<Mesh3DHalfCorner*>& output_corners,
	                            bool include_start_halfcorner = true) = 0;
	virtual void getMeshBounds(Vec3d& mesh_min, Vec3d& mesh_max) = 0;
	virtual bool isEdgeNonmanifold(Mesh3DHalfCorner* hfc) const = 0;
	virtual double getAngle(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const = 0;
	virtual double getAngle(Mesh3DHalfCorner* hfc) const = 0;
	virtual double getAngleCos(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const = 0;
	virtual double getAngleCos(Mesh3DHalfCorner* hfc) const = 0;
	virtual Mesh3DTriangle* getCommonTriangle(Mesh3DVertex* v1, Mesh3DVertex* v2) const = 0;
	virtual absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DTriangle*>>
	buildVertexTriangleAdjacency() const = 0;
	virtual int edgeValence(Mesh3DHalfCorner* opp_edge_corner) = 0;
	virtual absl::flat_hash_set<Mesh3DHalfCorner*> getEdgesAroundVertex(
	    const Mesh3DVertex* center_vertex) const = 0;
	virtual absl::flat_hash_set<Mesh3DTriangle*> getTrianglesAroundVertex(
	    Mesh3DVertex* vertex) const = 0;
	virtual std::vector<Mesh3DTriangle*> getTriangleVectorAroundVertex(
	    Mesh3DVertex* vertex) const = 0;
	virtual const absl::flat_hash_set<Mesh3DHalfCorner*>& getHalfCornersAtVertex(
	    Mesh3DVertex* vertex) const = 0;

	// Around edge queries.
	virtual std::vector<Mesh3DHalfCorner*> getHalfCornersAroundEdge(Mesh3DVertex* v1,
	                                                                Mesh3DVertex* v2) const = 0;
	virtual std::vector<Mesh3DTriangle*> getTrianglesAroundEdge(Mesh3DVertex* v1,
	                                                            Mesh3DVertex* v2) const = 0;
	virtual void printTriangleVertexIndices(Mesh3DTriangle* triangle) const = 0;

	virtual bool isVertexInMesh(Mesh3DVertex* v) const = 0;
	virtual bool isHalfCornerInMesh(Mesh3DHalfCorner* h) const = 0;
	virtual bool isTriangleInMesh(const Mesh3DTriangle* t) const = 0;
	virtual bool areEdgesAroundManifold(const Mesh3DVertex* v) const = 0;

	virtual double getTotalArea() const = 0;
	virtual double getTotalKineticEnergy() const = 0;
	virtual absl::flat_hash_map<Mesh3DVertex*, double> getVertexAreas() const = 0;

	//--------------------------MESH MANIPULATION---------------------------------

	virtual absl::flat_hash_map<TriSide, size_t> uniteTrianglesInLocalRegions(
	    Mesh3DVertex* vertex, const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	    int& num_regions) const = 0;

	virtual void orderRegionsByLabels(absl::flat_hash_map<TriSide, size_t>& regions) const = 0;

	virtual std::vector<std::vector<int>> buildRegionsMatrix(
	    const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	    const absl::flat_hash_map<TriSide, size_t>& sides_to_regions,
	    const int num_regions) const = 0;

	virtual void shiftMeshByConstant(const int coordinate, const double amount) = 0;

	virtual absl::flat_hash_set<Mesh3DVertex*> edgeSubdivisionWithUpdatedVerts(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d split_coords) = 0;

	virtual absl::flat_hash_set<Mesh3DVertex*> edgeFlipWithUpdatedVerts(Mesh3DTriangle* triangle,
	                                                                    Mesh3DVertex* v1,
	                                                                    Mesh3DVertex* v2) = 0;

	virtual absl::flat_hash_set<Mesh3DVertex*> edgeCollapseWithUpdatedVerts(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d new_vert_coords) = 0;

	virtual void removeInterface(Vec2i interface) = 0;

	//--------------------------MESH MAINTENANCE----------------------------------
	//----------- add vertices
	virtual Mesh3DVertex* makeNewVertex() = 0;
	virtual Mesh3DVertex* makeNewVertexAtCoords(Vec3d vert_coords, VertexProperties vert_props) = 0;
	virtual Mesh3DVertex* makeNewVertexAtCoords(Vec3d vert_coords) = 0;
	virtual Mesh3DVertex* makeNewVertexAtTriangleMassCenter(Mesh3DTriangle* triangle) = 0;
	virtual Mesh3DVertex* makeNewVertexAtEdgeMidpoint(Mesh3DVertex* v1, Mesh3DVertex* v2) = 0;
	virtual Mesh3DHalfCorner* makeNewHalfCorner(Mesh3DVertex* v, Mesh3DTriangle* t,
	                                            bool label_side) = 0;
	//----------- add triangles
	virtual Mesh3DTriangle* makeNewTriangle(Mesh3DVertex* v0, Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                        Vec2i labels) = 0;
	//----------- update HFC info
	virtual void setHFCVertex(Mesh3DHalfCorner* hfc, Mesh3DVertex* v) = 0;
	//----------- delete elements
	virtual void clear() = 0;
	//----------- delete triangles
	virtual void deleteTriangle(const Mesh3DTriangle* triangle) = 0;
	//----------- delete vertices
	virtual void deleteVertex(Mesh3DVertex* vertex) = 0;
	//----------- delete half-corners
	virtual void deleteHalfCorner(Mesh3DHalfCorner* hfc) = 0;
	//----------- integer indices for deterministic intersections
	virtual void assignVertexIndexMap() = 0;
	virtual int getVertexIndex(Mesh3DVertex* vertex) const = 0;
	//----------- mesh test functions
	virtual int runMeshConsistencyChecks() = 0;
	//----------- state cleaning between simulation runs
	virtual void clearNonPersistentState() = 0;
	//----------- renew internal datastructures, so they don't take as much space.
	virtual void defragmentMesh() = 0;
	//----------- Make triangles 0-orientation have smaller label without changing handness.
	virtual void orderLabelsOnManifoldPatches() const = 0;

	//--------------------------MESH INPUT/OUTPUT---------------------------------
	virtual int loadBinary(std::string_view) = 0;
	virtual void writeInBin(const std::string& output_file) = 0;
	virtual void writeInText(const std::string& output_file) = 0;

	virtual Mesh3DSaveState getCurrentSaveState() = 0;
	virtual Mesh3DSaveState restoreFromSaveState(const Mesh3DSaveState& save_state) = 0;
	virtual Mesh3DSaveState appendFromSaveState(const Mesh3DSaveState& save_state) = 0;

	virtual int restoreFromGeometry(const std::vector<Vec3i>& triangle_vertices,
	                                const std::vector<Vec3d>& vertex_positions,
	                                const std::vector<VertexProperties>& vertex_properties,
	                                const std::vector<Vec2i>& material_labels,
	                                const int add_to_existing, const int offset_materials) = 0;

 protected:
	ExactnessPredicates intersector;
};
