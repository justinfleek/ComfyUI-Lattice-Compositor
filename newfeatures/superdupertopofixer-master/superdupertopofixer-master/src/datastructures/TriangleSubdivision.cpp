
/* TriangleSubdivision.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2023
 *
 * A data structure to create and manage memory for internal Triangle data structures.
 * To follow RAII principle, memory is allocated in constructor and released in destructor.
 */
#include "TriangleSubdivision.h"

TriangleSubdivision::TriangleSubdivision(const std::vector<Vec2d>& points,
                                         const std::vector<Vec2i>& segments) {
	in_.numberofpoints = points.size();
	in_.pointlist = (REAL*)malloc(2 * in_.numberofpoints * sizeof(REAL));
	for (int i = 0; i < in_.numberofpoints; i++) {
		in_.pointlist[2 * i] = points[i][0];
		in_.pointlist[2 * i + 1] = points[i][1];
	}

	in_.numberofpointattributes = 0;
	in_.pointattributelist = nullptr;
	in_.pointmarkerlist = nullptr;

	in_.numberofsegments = segments.size();
	in_.segmentlist = (int*)malloc(2 * in_.numberofsegments * sizeof(int));
	for (int i = 0; i < in_.numberofsegments; i++) {
		in_.segmentlist[2 * i] = segments[i][0];
		in_.segmentlist[2 * i + 1] = segments[i][1];
	}

	in_.segmentmarkerlist = nullptr;
	in_.numberofholes = 0;
	in_.numberofregions = 0;

	out_.pointlist = nullptr;
	out_.pointmarkerlist = nullptr;
	out_.trianglelist = nullptr;
	out_.segmentlist = nullptr;
	out_.segmentmarkerlist = nullptr;
}

TriangleSubdivision::~TriangleSubdivision() {
	free(in_.pointlist);
	free(in_.segmentlist);

	if (out_.pointlist) {
		free(out_.pointlist);
	}

	if (out_.pointmarkerlist) {
		free(out_.pointmarkerlist);
	}

	if (out_.trianglelist) {
		free(out_.trianglelist);
	}
	if (out_.segmentlist) {
		free(out_.segmentlist);
	}
	if (out_.segmentmarkerlist) {
		free(out_.segmentmarkerlist);
	}
}

void TriangleSubdivision::subdivide() {
	char mode[] = "pzQ";
	triangulate(mode, &in_, &out_, nullptr);
}

std::vector<Vec3i> TriangleSubdivision::getSubdivTriangles() const {
	std::vector<Vec3i> result;
	result.reserve(out_.numberoftriangles);
	for (int i = 0; i < out_.numberoftriangles; i++) {
		result.emplace_back(out_.trianglelist[3 * i], out_.trianglelist[3 * i + 1],
		                    out_.trianglelist[3 * i + 2]);
	}
	return result;
}

std::vector<Vec2d> TriangleSubdivision::getSubdivPoints() const {
	std::vector<Vec2d> points;
	points.reserve(out_.numberofpoints);
	for (int i = 0; i < out_.numberofpoints; i++) {
		points.emplace_back(out_.pointlist[2 * i], out_.pointlist[2 * i + 1]);
	}
	return points;
}

std::vector<Vec2i> TriangleSubdivision::getSubdivEdges() const {
	std::vector<Vec2i> segments;
	segments.reserve(out_.numberofsegments);
	for (int i = 0; i < out_.numberofsegments; i++) {
		segments.emplace_back(out_.segmentlist[2 * i], out_.segmentlist[2 * i + 1]);
	}
	return segments;
}
