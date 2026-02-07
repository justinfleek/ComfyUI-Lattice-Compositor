/* RenderingPrimitives.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header for the class that performs rendering of basic mesh primitives.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <vector>

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include "../datastructures/Mesh3DTriangle.h"
#include "../rendering/Colorizer.h"
#include "../utilities/vec.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

class RenderingPrimitives {
 public:
	RenderingPrimitives() = default;
	~RenderingPrimitives();

	// Renders input `triangles` in wireframe mode, drawn with the input colors, either one
	// color for all triangles, or one color per triangle. Does not check for the consistency of the
	// input vector `triangles`.
	static void renderTrianglesEdges(const std::vector<std::vector<Vec3d>>& triangles,
	                                 const std::vector<Vec4d>& outline_colors, float line_width);

	// Renders input `triangles`, both front and back faces, drawn with the input colors, either one
	// color for all triangles, or one color per triangle. Based on `proprortion_to_remove` triangles
	// are scaled down around their barycenters. Slightly shrinking a triangle is useful for clearer
	// visualization, as it allows triangle edges and triangle face to not overlap and therefore be
	// visible more clearly. Shrinking is done purely for the visual effect, actual triangle vertex
	// positions aren't changed. Does not check for the consistency of the input vector `triangles`.
	static void renderTrianglesFaces(const std::vector<std::vector<Vec3d>>& triangles,
	                                 const std::vector<Vec4d>& front_colors,
	                                 const std::vector<Vec4d>& back_colors,
	                                 float proprortion_to_remove);

	// Renders input `triangles`, front and back faces, and triangle edges, by calling
	// `renderTriangleFaces` (with `proprortion_to_remove` 0.025) and `renderTriangleEdges`.
	static void renderTrianglesEdgesAndFaces(const std::vector<std::vector<Vec3d>>& triangles,
	                                         const std::vector<Vec4d> front_colors,
	                                         const std::vector<Vec4d> back_colors,
	                                         const std::vector<Vec4d> outline_colors);
	void init(size_t num_triangles);

	void moveMeshToGPU(const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	                   Colorizer* final_colorizer);

	void renderMeshFaces(bool is_shrunk);
	void renderMeshEdges(float line_width);

 private:
	// Calculates the triangle's barycenter, and shifts the positions of triangle vertices towards the
	// barycenter by a factor given by `proprortion_to_remove` (0 means no shift, 1 means move all
	// vertices to the barycenter).
	void static shrinkTriangle(Vec3d& v0, Vec3d& v1, Vec3d& v2, double proprortion_to_remove);

	size_t num_vertices_;
	size_t num_normals_;
	size_t num_colors_;

	// O: vertices, 1: normals, 2: colors;
	GLuint mesh_buffers_[3];
	// 0: vertices. Borrow normals and colors from above.
	GLuint shrunk_mesh_buffers_[1];
	bool initialized_ = false;
};