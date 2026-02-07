#ifndef DATASTRUCTURES_GRIDMESHINTERSECTION
#define DATASTRUCTURES_GRIDMESHINTERSECTION
/* GridMeshIntersection.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * This is the header for structures representing intersection between mesh and grid.
 * It keeps track information about location on the grid and mesh triangle that are involved in the
 * intersection.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include "../utilities/vec.h"
#include "Mesh3DInterface.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

// Forward declaration
class Grid3DInterface;

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// Information about grid edge <-> triangle face intersection.
class GridEdgeMeshFaceIntersection {
 public:
	// Initializes intersection between a mesh triangle `triangle` and a grid edge with index
	// `edge_id` at a position `pos`.
	GridEdgeMeshFaceIntersection(Mesh3DTriangle* triangle, const long long edge_id, const Vec3d pos,
	                             const Vec3d bary, const bool is_tri_norm_edge_aligned);
	~GridEdgeMeshFaceIntersection() = default;

	// Accessor functions
	Mesh3DTriangle* getTriangle() const { return triangle_; };
	long long getEdgeId() const { return edge_id_; };
	Vec3d getPosition() const { return pos_; };
	Vec3d getBary() const { return bary_; }
	bool isTriNormalEdgeAligned() const { return is_normal_aligned_; };
	Mesh3DVertex* getVertex() const { return vertex_; }
	void setVertex(Mesh3DVertex* vertex);
	void setBary(Vec3d bary);

 private:
	Mesh3DTriangle* triangle_;
	Mesh3DVertex* vertex_;
	long long edge_id_;
	Vec3d pos_;
	Vec3d bary_;
	bool is_normal_aligned_;
};

// Information about grid face <-> triangle edge intersection.
class GridFaceMeshEdgeIntersection {
 public:
	// Initializes intersection between grid face with `face_id` and mesh edge defined by two vertices
	// `first` and `second`. The intersection is registered at normalized coordinate `bary_coord` on
	// the (first, second) segment. The position of the intersection can be computed as (1 -
	// bary_coord) * first.pos  + bary_coord * second.pos. `is_first_inside` and `is_second_inside`
	// are used to indicate if first and second vertex are inside a region of interest, e.g. complex
	// cell region. `vertex` is the new mesh vertex, created at the intersection point.
	GridFaceMeshEdgeIntersection(const long long face_id, Mesh3DVertex* first,
	                             const bool is_first_inside, Mesh3DVertex* second,
	                             const bool is_second_inside, const double bary_coord,
	                             Mesh3DVertex* vertex);
	~GridFaceMeshEdgeIntersection() = default;

	// Move and copy semantics. These are needed to be able to reassign intersections in
	// vectors and other containers.
	GridFaceMeshEdgeIntersection& operator=(const GridFaceMeshEdgeIntersection& other) = default;
	GridFaceMeshEdgeIntersection& operator=(GridFaceMeshEdgeIntersection&& other);
	GridFaceMeshEdgeIntersection(GridFaceMeshEdgeIntersection&& other);
	GridFaceMeshEdgeIntersection(const GridFaceMeshEdgeIntersection& other) = default;

	// Value accessors defined inline for performance reasons.
	long long getFaceId() const { return face_id_; };
	Mesh3DVertex* getEdgeFirst() const { return first_; };
	Mesh3DVertex* getEdgeSecond() const { return second_; };
	double getBaryCoord() const { return bary_coord_; };
	Vec3d getPosition() const;
	bool isFirstInside() const { return is_first_inside_; };
	bool isSecondInside() const { return is_second_inside_; };
	Mesh3DVertex* getVertex() const { return vertex_; }
	void setVertex(Mesh3DVertex* vertex);
	void setBaryCoord(double bary);

 private:
	long long face_id_;
	Mesh3DVertex* first_;
	Mesh3DVertex* second_;
	double bary_coord_;
	bool is_first_inside_;
	bool is_second_inside_;
	// This can be null pointer, meaning that we only computed the point of intersection but did not
	// create any geometry yet.
	Mesh3DVertex* vertex_;
};

class GridFaceMeshEdgeCmp {
 public:
	GridFaceMeshEdgeCmp(Grid3DInterface& grid, Mesh3DVertex* first, Mesh3DVertex* second);
	bool operator()(const GridFaceMeshEdgeIntersection& first,
	                const GridFaceMeshEdgeIntersection& second);

 private:
	// Three-way comparison between faces with coords `first` and `second` in the direction
	// `orientation`. +1 means first comes earlier, -1 second comes earlier, 0 -- same position along
	// this orientaiton.
	int cmpGridFaces(Vec4ll first, Vec4ll second, int orientation);

	Grid3DInterface& grid_;
	// Specifies if each coordinate of mesh edge decreases (-1), stays the same (0), or increases
	// (+1).
	std::array<char, 3> direction_;
};

// Class to represent possible degeneracies during grid-mesh intersection process.
// Mostly contains data about grid elements and mesh elements. Provides no guarantees about what
// information will be available for each degeneracy type. Clients have to ensure themselves that
// appropriate fields are provided.
class GridMeshDegeneracy {
 public:
	enum Type {
		// Degeneracy of grid elements being close to triangle elements.
		kGridNearTriangleBorder,
		// Two intersections are nearly in the same place.
		kTwoCloseIntersections,
		// Counter to keep track of the size of enum.
		kNumberOfTypes,
	};

	Type type;

	struct GridInfo {
		enum ObjectType {
			kVertex,
			kEdge,
		};
		ObjectType type;
		long long edge_id = -1;
		long long vertex_id = -1;
	};

	struct TriInfo {
		enum ObjectType {
			kVertex,
			kEdge,
		};
		ObjectType type;
		Mesh3DVertex* tri_vertex = nullptr;
		std::vector<Mesh3DVertex*> tri_edge = {nullptr, nullptr};
	};

	GridInfo grid_info;
	TriInfo tri_info;
	std::vector<GridEdgeMeshFaceIntersection> intersection_pair;
};
#endif  // DATASTRUCTURES_GRIDMESHINTERSECTION
