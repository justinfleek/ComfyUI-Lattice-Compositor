
/* TriangleSubdivision.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2023
 *
 * A data structure to create and manage memory for internal Triangle data structures.
 * To follow RAII principle, memory is allocated in constructor and released in destructor.
 */

#pragma once

extern "C" {
#include "../src/utilities/triangle/triangle.h"
}
#include "../src/utilities/vec.h"

class TriangleSubdivision {
 public:
	TriangleSubdivision(const std::vector<Vec2d>& points, const std::vector<Vec2i>& segments);
	~TriangleSubdivision();
	void subdivide();
	std::vector<Vec3i> getSubdivTriangles() const;
	std::vector<Vec2d> getSubdivPoints() const;
	std::vector<Vec2i> getSubdivEdges() const;

 private:
	triangulateio in_;
	triangulateio out_;
};