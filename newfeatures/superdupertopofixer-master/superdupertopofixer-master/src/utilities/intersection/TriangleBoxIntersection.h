// Borrowed from https://gist.github.com/jflipts/fc68d4eeacfcc04fbdb2bf38e0911850
// Need to check for licenses more carefully.
#pragma once

#include <cmath>

#include "../vec.h"

inline void findMinMax(float x0, float x1, float x2, float& min, float& max) {
	min = max = x0;
	if (x1 < min)
		min = x1;
	if (x1 > max)
		max = x1;
	if (x2 < min)
		min = x2;
	if (x2 > max)
		max = x2;
}

inline bool planeBoxOverlap(Vec3d normal, Vec3d vert, Vec3d maxbox) {
	Vec3d vmin, vmax;
	float v;
	for (size_t q = 0; q < 3; q++) {
		v = vert[q];
		if (normal[q] > 0.0) {
			vmin[q] = -maxbox[q] - v;
			vmax[q] = maxbox[q] - v;
		} else {
			vmin[q] = maxbox[q] - v;
			vmax[q] = -maxbox[q] - v;
		}
	}
	if (dot(normal, vmin) > 0.0)
		return false;
	if (dot(normal, vmax) >= 0.0)
		return true;

	return false;
}

/*======================== X-tests ========================*/

inline bool axisTestX(float a, float b, float fa, float fb, const Vec3d& v0, const Vec3d& v1,
                      const Vec3d& boxhalfsize, float& rad, float& min, float& max, float& p0,
                      float& p1) {
	p0 = a * v0[1] - b * v0[2];
	p1 = a * v1[1] - b * v1[2];
	if (p0 < p1) {
		min = p0;
		max = p1;
	} else {
		min = p1;
		max = p0;
	}
	rad = fa * boxhalfsize[1] + fb * boxhalfsize[2];
	if (min > rad || max < -rad)
		return false;
	return true;
}

/*======================== Y-tests ========================*/

inline bool axisTestY(float a, float b, float fa, float fb, const Vec3d& v0, const Vec3d& v1,
                      const Vec3d& boxhalfsize, float& rad, float& min, float& max, float& p0,
                      float& p1) {
	p0 = -a * v0[0] + b * v0[2];
	p1 = -a * v1[0] + b * v1[2];
	if (p0 < p1) {
		min = p0;
		max = p1;
	} else {
		min = p1;
		max = p0;
	}
	rad = fa * boxhalfsize[0] + fb * boxhalfsize[2];
	if (min > rad || max < -rad)
		return false;
	return true;
}

/*======================== Z-tests ========================*/

inline bool axisTestZ(float a, float b, float fa, float fb, const Vec3d& v0, const Vec3d& v1,
                      const Vec3d& boxhalfsize, float& rad, float& min, float& max, float& p0,
                      float& p1) {
	p0 = a * v0[0] - b * v0[1];
	p1 = a * v1[0] - b * v1[1];
	if (p0 < p1) {
		min = p0;
		max = p1;
	} else {
		min = p1;
		max = p0;
	}
	rad = fa * boxhalfsize[0] + fb * boxhalfsize[1];
	if (min > rad || max < -rad)
		return false;
	return true;
}

bool triBoxOverlap(Vec3d boxcenter, Vec3d boxhalfsize, Vec3d tv0, Vec3d tv1, Vec3d tv2) {
	/*    use separating axis theorem to test overlap between triangle and box */
	/*    need to test for overlap in these directions: */
	/*    1) the {x,y,z}-directions (actually, since we use the AABB of the triangle */
	/*       we do not even need to test these) */
	/*    2) normal of the triangle */
	/*    3) crossproduct(edge from tri, {x,y,z}-direction) */
	/*       this gives 3x3=9 more tests */
	Vec3d v0, v1, v2;
	float min, max, p0, p1, p2, rad, fex, fey, fez;
	Vec3d normal, e0, e1, e2;

	/* This is the fastest branch on Sun */
	/* move everything so that the boxcenter is in (0,0,0) */
	v0 = tv0 - boxcenter;
	v1 = tv1 - boxcenter;
	v2 = tv2 - boxcenter;

	/* compute triangle edges */
	e0 = v1 - v0;
	e1 = v2 - v1;
	e2 = v0 - v2;

	/* Bullet 3:  */
	/*  test the 9 tests first (this was faster) */
	fex = std::abs(e0[0]);
	fey = std::abs(e0[1]);
	fez = std::abs(e0[2]);

	if (!axisTestX(e0[2], e0[1], fez, fey, v0, v2, boxhalfsize, rad, min, max, p0, p2))
		return false;
	if (!axisTestY(e0[2], e0[0], fez, fex, v0, v2, boxhalfsize, rad, min, max, p0, p2))
		return false;
	if (!axisTestZ(e0[1], e0[0], fey, fex, v1, v2, boxhalfsize, rad, min, max, p1, p2))
		return false;

	fex = std::abs(e1[0]);
	fey = std::abs(e1[1]);
	fez = std::abs(e1[2]);

	if (!axisTestX(e1[2], e1[1], fez, fey, v0, v2, boxhalfsize, rad, min, max, p0, p2))
		return false;
	if (!axisTestY(e1[2], e1[0], fez, fex, v0, v2, boxhalfsize, rad, min, max, p0, p2))
		return false;
	if (!axisTestZ(e1[1], e1[0], fey, fex, v0, v1, boxhalfsize, rad, min, max, p0, p1))
		return false;

	fex = std::abs(e2[0]);
	fey = std::abs(e2[1]);
	fez = std::abs(e2[2]);
	if (!axisTestX(e2[2], e2[1], fez, fey, v0, v1, boxhalfsize, rad, min, max, p0, p1))
		return false;
	if (!axisTestY(e2[2], e2[0], fez, fex, v0, v1, boxhalfsize, rad, min, max, p0, p1))
		return false;
	if (!axisTestZ(e2[1], e2[0], fey, fex, v1, v2, boxhalfsize, rad, min, max, p1, p2))
		return false;

	/* Bullet 1: */
	/*  first test overlap in the {x,y,z}-directions */
	/*  find min, max of the triangle each direction, and test for overlap in */
	/*  that direction -- this is equivalent to testing a minimal AABB around */
	/*  the triangle against the AABB */

	/* test in X-direction */
	findMinMax(v0[0], v1[0], v2[0], min, max);
	if (min > boxhalfsize[0] || max < -boxhalfsize[0])
		return false;

	/* test in Y-direction */
	findMinMax(v0[1], v1[1], v2[1], min, max);
	if (min > boxhalfsize[1] || max < -boxhalfsize[1])
		return false;

	/* test in Z-direction */
	findMinMax(v0[2], v1[2], v2[2], min, max);
	if (min > boxhalfsize[2] || max < -boxhalfsize[2])
		return false;

	/* Bullet 2: */
	/*  test if the box intersects the plane of the triangle */
	/*  compute plane equation of triangle: normal*x+d=0 */
	normal = cross(e0, e1);
	if (!planeBoxOverlap(normal, v0, boxhalfsize))
		return false;

	return true; /* box and triangle overlaps */
}