/* Grid3DCubical.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the cubical grid implementation. Modules should only access it through its
 * parent interface class (Grid3DInterface).
 *
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "Grid3DInterface.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the mesh data structure
class Grid3DCubical : public Grid3DInterface {
 public:
	// constructors
	Grid3DCubical();
	virtual ~Grid3DCubical();

	// functions
	virtual void setVertexMaterial(const long long vertex_id, SparseVector<int> material) override{};
	virtual SparseVector<int> getVertexMaterial(const long long vertex_id) override { return {}; };
	virtual void setVertexMaterialVectors(
	    absl::flat_hash_map<long long, SparseVector<int>> per_vertex_materials) override{};
	virtual Vec3d getRayDirection(long long orientation) override { return Vec3d(); };
	virtual Vec2i convertMeshLabelsToGridLabels(Vec2i mesh_labels) override { return Vec2i(); };
	virtual void constructMaterialDecoder() override{};
	virtual int convertGridLabelToMeshLabel(int grid_label) override { return 0; };
	virtual Vec2i convertGridLabelToMeshLabel(Vec2i grid_labels) override { return Vec2i(); };
	virtual void addTriangleToCell(const long long cell_id, Mesh3DTriangle* triangle_id) override{};
	virtual void addTriangleToCellWithoutFlaggingRays(const long long cell_id,
	                                                  Mesh3DTriangle* triangle_id) override{};
	virtual void remove_triangle_from_cell(const long long cell_id,
	                                       Mesh3DTriangle* triangle_id) override{};
	virtual std::vector<Mesh3DTriangle*> getCellTriangles(const long long cell_id) const override {
		return {};
	};
	virtual std::vector<long long> getCellsWithTriangles() override { return {}; };
	virtual void addIntersectionToEdge(GridEdgeMeshFaceIntersection intersection) override {
		return;
	};
	virtual std::vector<GridEdgeMeshFaceIntersection> get_intersections_on_edge(
	    const long long edge_id) override {
		return {};
	};
	virtual const SparseRaysContainer& getSparseRays(long long orientation) override {
		return sparse_rays_;
	};
	virtual bool isVertexMarkedComplex(const long long vertex_id) override { return false; };
	virtual void markVertexAsComplex(const long long vertex_id) override { return; };
	virtual bool isEdgeMarkedTopoComplex(const long long edge_id) override { return false; };
	virtual void markEdgeAsTopoComplex(const long long edge_id) override { return; };
	virtual bool isEdgeMarkedGeomComplex(const long long edge_id) override { return false; };
	virtual void markEdgeAsGeomComplex(const long long edge_id) override { return; };
	virtual bool doesEdgeHaveFixedComplexNeighbors(const long long edge_id) override {
		return false;
	};
	virtual bool isFrontEdge(const long long edge_id) override { return false; };
	virtual absl::flat_hash_set<long long> getTopoComplexGeomSimpleEdges() override { return {}; };
	virtual absl::flat_hash_set<long long> getGeomComplexEdges() override { return {}; }

	//---------------- manipulating complex cells
	virtual bool isCellMarkedComplex(const long long cell_id,
	                                 const ComplexCellType type) const override {
		return false;
	};
	virtual void markCellAsComplex(const long long cell_id, const ComplexCellType type) override {
		return;
	};
	virtual void unmarkCellAsComplex(const long long cell_id, const ComplexCellType type) override {
		return;
	};
	virtual void markCellAsEdgeDeep(const long long cell_id) override{};
	virtual void markCellAsEdgeShallow(const long long cell_id) override{};
	virtual std::vector<long long> getComplexCellsVector(const ComplexCellType type) const override {
		return {};
	};
	virtual absl::flat_hash_set<long long> getComplexCellsSet(
	    const ComplexCellType type) const override {
		return {};
	};
	virtual absl::flat_hash_set<long long> getEdgeDeepCells() const override { return {}; };
	virtual absl::flat_hash_set<long long> getEdgeShallowCells() const override { return {}; };
	virtual std::vector<long long> getFrontFacesVector() const override { return {}; };
	virtual absl::flat_hash_set<long long> getFrontFacesSet() const override { return {}; };
	virtual std::vector<long long> getComplexRegionFrontCellsVector() const override { return {}; };
	virtual absl::flat_hash_set<long long> getComplexRegionFrontCellsSet() const override {
		return {};
	};
	virtual std::vector<long long> getSimpleRegionFrontCellsVector() const override { return {}; };
	virtual absl::flat_hash_set<long long> getSimpleRegionFrontCellsSet() const override {
		return {};
	};

	virtual void addInterpolatedVertPropsOnVertex(long long vertex_id,
	                                              VertexProperties vert_props) override{};
	virtual VertexProperties getInterpolatedVertPropsFromVertex(long long vertex_id) override {
		return VertexProperties();
	};
	virtual bool isMeshVertexInGridCellNaive(Mesh3DVertex* mesh_vertex, long long cell_id) override {
		return false;
	};

	virtual void setRaysUpdatedValue(bool value) override{};
	virtual int getLabelFromUniqueMaterialVector(long long grid_vertex) override { return 0; };
	virtual bool isVertexInComplexRegion(long long grid_vertex) override { return false; };

	virtual void addUniqueLabeling(long long grid_vertex, int label) override{};
	virtual absl::flat_hash_map<long long, int>::iterator getUniqueLabeling(
	    long long grid_vertex) override {
		return absl::flat_hash_map<long long, int>::iterator();
	};
	virtual bool hasUniqueLabeling(long long grid_vertex) override { return true; };
	virtual absl::flat_hash_map<long long, int>& getUniqueLabelingMap() override {
		return unique_labeling;
	};
	virtual void addOptimizedMCEdgePoint(long long grid_edge, Vec3d optimized_point) override{};
	virtual absl::flat_hash_map<long long, Vec3d>::iterator getOptimizedMCEdgePoint(
	    long long grid_edge) override {
		return absl::flat_hash_map<long long, Vec3d>::iterator();
	}
	virtual bool hasOptimizedMCEdgePoint(long long grid_edge) override { return true; };

 private:
	std::vector<std::vector<int>> per_vertex_material_labels;  // each vertex

	// list of complex grid primitives (vertices, edges, faces, cells),
	//	each associated with a unique grid ID given by the [TODO] functions
	std::vector<long long> complex_vertices;
	std::vector<long long> complex_edges;
	std::vector<long long> complex_faces;
	std::vector<long long> complex_cells;
	GridLattice<long long, long long> sparse_rays_;
	absl::flat_hash_map<long long, int> unique_labeling;
};