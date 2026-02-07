/* Mesh3DInterface.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the mesh interface. Functions that are uniform over all
 * implementations of the mesh should be implemented here.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Mesh3DInterface.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Mesh3DInterface::Mesh3DInterface() { intersector.exactinit(); }

// default destructor
Mesh3DInterface::~Mesh3DInterface() {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

static bool same_sign(double a, double b) { return (a <= 0 && b <= 0) || (a >= 0 && b >= 0); }

// tri_index is the index of a triangle, x0 and x1 are arrays of 3 doubles each, defining the
// endpoints of a line segment returns 0 if given triangle and line segment don't intersect, 1 if
// they do
int Mesh3DInterface::intersectTriSegment(Mesh3DTriangle* triangle, Vec3d s0_, Vec3d s1_) {
	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	Vec3d v0 = tri_verts[0]->getCoords();
	Vec3d v1 = tri_verts[1]->getCoords();
	Vec3d v2 = tri_verts[2]->getCoords();

	double test0, test1;
	test0 = intersector.orient3d(v0.v, v1.v, v2.v, s0_.v);
	test1 = intersector.orient3d(v0.v, v1.v, v2.v, s1_.v);
	if (same_sign(test0, test1))
		return 0;
	test0 = intersector.orient3d(s0_.v, s1_.v, v0.v, v1.v);
	test1 = intersector.orient3d(s0_.v, s1_.v, v0.v, v2.v);
	if (same_sign(test0, test1))
		return 0;
	test0 = intersector.orient3d(s0_.v, s1_.v, v1.v, v0.v);
	test1 = intersector.orient3d(s0_.v, s1_.v, v1.v, v2.v);
	if (same_sign(test0, test1))
		return 0;
	test0 = intersector.orient3d(s0_.v, s1_.v, v2.v, v0.v);
	test1 = intersector.orient3d(s0_.v, s1_.v, v2.v, v1.v);
	if (same_sign(test0, test1))
		return 0;

	return 1;
}

int Mesh3DInterface::intersectTriSegmentNoVerts(Mesh3DTriangle* triangle, Mesh3DVertex* vert0,
                                                Mesh3DVertex* vert1) {
	Vec3d s0 = vert0->getCoords();
	Vec3d s1 = vert1->getCoords();

	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	Vec3d v0 = tri_verts[0]->getCoords();
	Vec3d v1 = tri_verts[1]->getCoords();
	Vec3d v2 = tri_verts[2]->getCoords();

	// if triangle contains one of the vertices, intersection is considered only if all points are
	// coplanar and vert1 and vert2 are in different semiplanes as defined by the other 2 points:
	if (triangle->getHalfCornerAtVertex(vert0) != nullptr ||
	    triangle->getHalfCornerAtVertex(vert1) != nullptr) {
		printf("This triangle has vertex from v3, v4!\n");
		if (intersector.orient3d(v0.v, v1.v, v2.v, s0.v) == 0 &&
		    intersector.orient3d(v0.v, v1.v, v2.v, s1.v) == 0) {
			printf("they are coplanar!\n");
			// if the other two points in different semiplanes relative to the line of s0, s1:
			// printf(
			//     "coords:\n v0: %f, %f, %f\n v1: %f, %f, %f\n v2: %f, %f, %f\n s0: %f, %f, %f\n s1: %f,
			//     "
			//     "%f, %f\n",
			//     v0[0], v0[1], v0[2], v1[0], v1[1], v1[2], v2[0], v2[1], v2[2], s0[0], s0[1], s0[2],
			//     s1[0], s1[1], s1[2]);

			// printf("Intersectors --------------\n %f * %f; %f * %f; %f * %f;\n",
			// intersector.orient2dfast(s0, s1, v0),
			//        intersector.orient2dfast(s0, s1, v1), intersector.orient2dfast(s0, s1, v1),
			//        intersector.orient2dfast(s0, s1, v2), intersector.orient2dfast(s0, s1, v2),
			//        intersector.orient2dfast(s0, s1, v0));

			// if (intersector.orient2dfast(s0, s1, v0) * intersector.orient2dfast(s0, s1, v1) < 0 ||
			//     intersector.orient2dfast(s0, s1, v1) * intersector.orient2dfast(s0, s1, v2) < 0 ||
			//     intersector.orient2dfast(s0, s1, v2) * intersector.orient2dfast(s0, s1, v0) < 0) {
			//	printf("interect!!!!!!\n");
			Vec3d normal = cross(v0 - v1, v0 - v2);
			Vec3d point_on_normal = v0 + 0.1 * normal;
			// if s0, s1, are colinear with any of the triangle verts, it means they're intersecting:
			if (intersector.orient3d(s0.v, s1.v, point_on_normal.v, v0.v) == 0 ||
			    intersector.orient3d(s0.v, s1.v, point_on_normal.v, v1.v) == 0 ||
			    intersector.orient3d(s0.v, s1.v, point_on_normal.v, v2.v) == 0) {
				return 1;
			}

			if ((intersector.orient3d(s0.v, s1.v, point_on_normal.v, v0.v) *
			             intersector.orient3d(s0.v, s1.v, point_on_normal.v, v1.v) <
			         0 &&
			     (intersector.orient3d(v2.v, v1.v, point_on_normal.v, s0.v) *
			              intersector.orient3d(v2.v, v1.v, point_on_normal.v, v0.v) <
			          0 ||
			      intersector.orient3d(v2.v, v1.v, point_on_normal.v, s1.v) *
			              intersector.orient3d(v2.v, v1.v, point_on_normal.v, v0.v) <
			          0)) ||
			    (intersector.orient3d(s0.v, s1.v, point_on_normal.v, v1.v) *
			             intersector.orient3d(s0.v, s1.v, point_on_normal.v, v2.v) <
			         0 &&
			     (intersector.orient3d(v0.v, v1.v, point_on_normal.v, s0.v) *
			              intersector.orient3d(v0.v, v1.v, point_on_normal.v, v2.v) <
			          0 ||
			      intersector.orient3d(v0.v, v1.v, point_on_normal.v, s1.v) *
			              intersector.orient3d(v0.v, v1.v, point_on_normal.v, v2.v) <
			          0)) ||
			    (intersector.orient3d(s0.v, s1.v, point_on_normal.v, v2.v) *
			             intersector.orient3d(s0.v, s1.v, point_on_normal.v, v0.v) <
			         0 &&
			     (intersector.orient3d(v1.v, v2.v, point_on_normal.v, s0.v) *
			              intersector.orient3d(v1.v, v2.v, point_on_normal.v, v0.v) <
			          0 ||
			      intersector.orient3d(v1.v, v2.v, point_on_normal.v, s1.v) *
			              intersector.orient3d(v1.v, v2.v, point_on_normal.v, v0.v) <
			          0))) {
				return 1;

			} else {
				printf("not intersect!!!!!!\n");
				return 0;
			}
		} else
			return 0;
	}
	return intersectTriSegment(triangle, s0, s1);
}