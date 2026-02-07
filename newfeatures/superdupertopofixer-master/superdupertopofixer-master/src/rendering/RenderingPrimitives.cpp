/* RenderingPrimitives.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for class that performs rendering of basic mesh primitives.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "RenderingPrimitives.h"

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

void RenderingPrimitives::init(size_t num_triangles) {
	num_vertices_ = 3 * num_triangles;
	num_normals_ = 2 * num_vertices_;
	num_colors_ = 3 * num_vertices_;
	glGenBuffers(3, mesh_buffers_);
	glGenBuffers(1, shrunk_mesh_buffers_);
	initialized_ = true;
}

RenderingPrimitives::~RenderingPrimitives() {
	if (initialized_) {
		glDeleteBuffers(3, mesh_buffers_);
		glDeleteBuffers(1, shrunk_mesh_buffers_);
	}
}

// renders input `triangles` in wireframe mode, drawn with input colors, and input `line_width`
void RenderingPrimitives::renderTrianglesEdges(const std::vector<std::vector<Vec3d>>& triangles,
                                               const std::vector<Vec4d>& outline_colors,
                                               float line_width) {
	// if there is no color to draw to triangles, quit
	if (outline_colors.size() == 0) {
		return;
	}

	// save current glLineWidth, and set it to the input value
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(line_width);

	// triangle vertex positions
	Vec3d v0, v1, v2;
	// triangle edge colors, initialized to the first color in the vector
	Vec4d color = outline_colors.at(0);

	glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
	glBegin(GL_TRIANGLES);
	for (size_t it = 0; it < triangles.size(); ++it) {
		v0 = triangles[it][0];
		v1 = triangles[it][1];
		v2 = triangles[it][2];

		// set drawing color
		if (outline_colors.size() > it) {
			color = outline_colors.at(it);
		}
		glColor4f(color[0], color[1], color[2], color[3]);

		glVertex3f(v0[0], v0[1], v0[2]);
		glVertex3f(v1[0], v1[1], v1[2]);
		glVertex3f(v2[0], v2[1], v2[2]);
	}
	glEnd();

	// restore glLineWidth to the value it had before drawing
	glLineWidth(width);
}

// renders input `triangles`, front and back faces, drawn with input colors, scaled by
// `shrink_factor`
void RenderingPrimitives::renderTrianglesFaces(const std::vector<std::vector<Vec3d>>& triangles,
                                               const std::vector<Vec4d>& front_colors,
                                               const std::vector<Vec4d>& back_colors,
                                               float proprortion_to_remove) {
	// if there is no color to draw to triangles, quit
	if (front_colors.size() == 0) {
		return;
	}
	if (back_colors.size() == 0) {
		return;
	}

	// non-normalized triangle normal
	Vec3d normal;
	// triangle vertex positions
	Vec3d v0, v1, v2;
	// front and back side triangle colors, initialized to the first colors in the two vectors
	Vec4d front_color = front_colors.at(0);
	Vec4d back_color = back_colors.at(0);

	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glEnable(GL_COLOR_MATERIAL);
	glEnable(GL_CULL_FACE);
	glCullFace(GL_BACK);
	glFrontFace(GL_CCW);
	glBegin(GL_TRIANGLES);
	for (size_t it = 0; it < triangles.size(); ++it) {
		v0 = triangles[it][0];
		v1 = triangles[it][1];
		v2 = triangles[it][2];

		// render front side of the current triangle
		// calculate non-normalized triangle normal
		normal = cross(v1 - v0, v2 - v0);
		glNormal3f(normal[0], normal[1], normal[2]);

		// if `shrink_factor` is less than 1, calculate vertex positions of a shrunk triangle; this is
		// done after shrinking, in order to make the calculation more robust
		if (proprortion_to_remove > 0) {
			shrinkTriangle(v0, v1, v2, proprortion_to_remove);
		}

		// set drawing color
		if (front_colors.size() > it) {
			front_color = front_colors.at(it);
		}
		glColor4f(front_color[0], front_color[1], front_color[2], front_color[3]);

		glVertex3f(v0[0], v0[1], v0[2]);
		glVertex3f(v1[0], v1[1], v1[2]);
		glVertex3f(v2[0], v2[1], v2[2]);

		// render back side of current triangle
		// invert the non-normalized triangle normal
		normal *= -1;
		glNormal3f(normal[0], normal[1], normal[2]);

		// set drawing color
		if (back_colors.size() > it) {
			back_color = back_colors.at(it);
		}
		glColor4f(back_color[0], back_color[1], back_color[2], back_color[3]);

		glVertex3f(v0[0], v0[1], v0[2]);
		glVertex3f(v2[0], v2[1], v2[2]);
		glVertex3f(v1[0], v1[1], v1[2]);
	}

	glEnd();
	glDisable(GL_CULL_FACE);
}

// renders input `triangles`, by calling `renderTrianglesFaces` and `renderTrianglesEdges`
void RenderingPrimitives::renderTrianglesEdgesAndFaces(
    const std::vector<std::vector<Vec3d>>& triangles, const std::vector<Vec4d> front_colors,
    const std::vector<Vec4d> back_colors, const std::vector<Vec4d> outline_colors) {
	renderTrianglesFaces(triangles, front_colors, back_colors, 0.025);
	renderTrianglesEdges(triangles, outline_colors, 3);
}

void RenderingPrimitives::moveMeshToGPU(const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
                                        Colorizer* final_colorizer) {
	std::vector<float> vertex_data(3 * num_vertices_);
	std::vector<float> normal_data(3 * num_normals_);
	std::vector<float> color_data(4 * num_colors_);
	std::vector<float> shrunk_vertex_data(3 * num_vertices_);

	size_t vertex_idx = 0;
	size_t normal_idx = 0;
	size_t color_idx = 0;
	size_t shrunk_vertex_idx = 0;
	for (Mesh3DTriangle* tri : triangles) {
		Vec3d normal = normalized(tri->getNaiveNormal());
		Vec4d front_color = final_colorizer->getFrontColor(tri);
		Vec4d back_color = final_colorizer->getBackColor(tri);
		Vec4d outline_color = final_colorizer->getOutlineColor(tri);

		std::vector<Vec3d> verts;
		verts.reserve(3);
		for (Mesh3DVertex* vert : tri->getVerts()) {
			Vec3d coords = vert->getCoords();
			verts.push_back(coords);
			vertex_data[vertex_idx + 0] = coords[0];
			vertex_data[vertex_idx + 1] = coords[1];
			vertex_data[vertex_idx + 2] = coords[2];
			vertex_idx += 3;

			for (int i = 0; i < 3; ++i) {
				normal_data[normal_idx + i] = normal[i];
				normal_data[3 * num_vertices_ + normal_idx + i] = -normal[i];
			}
			normal_idx += 3;

			color_data[color_idx + 0] = front_color[0];
			color_data[color_idx + 1] = front_color[1];
			color_data[color_idx + 2] = front_color[2];
			color_data[color_idx + 3] = front_color[3];

			color_data[4 * num_vertices_ + color_idx + 0] = back_color[0];
			color_data[4 * num_vertices_ + color_idx + 1] = back_color[1];
			color_data[4 * num_vertices_ + color_idx + 2] = back_color[2];
			color_data[4 * num_vertices_ + color_idx + 3] = back_color[3];

			color_data[8 * num_vertices_ + color_idx + 0] = outline_color[0];
			color_data[8 * num_vertices_ + color_idx + 1] = outline_color[1];
			color_data[8 * num_vertices_ + color_idx + 2] = outline_color[2];
			color_data[8 * num_vertices_ + color_idx + 3] = outline_color[3];
			color_idx += 4;
		}
		shrinkTriangle(verts[0], verts[1], verts[2], 0.025);
		for (int i = 0; i < 3; ++i) {
			Vec3d coords = verts[i];
			shrunk_vertex_data[shrunk_vertex_idx + 0] = coords[0];
			shrunk_vertex_data[shrunk_vertex_idx + 1] = coords[1];
			shrunk_vertex_data[shrunk_vertex_idx + 2] = coords[2];
			shrunk_vertex_idx += 3;
		}
	}

	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[0]);
	glBufferData(GL_ARRAY_BUFFER, vertex_data.size() * sizeof(float), vertex_data.data(),
	             GL_STATIC_DRAW);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[1]);
	glBufferData(GL_ARRAY_BUFFER, normal_data.size() * sizeof(float), normal_data.data(),
	             GL_STATIC_DRAW);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[2]);
	glBufferData(GL_ARRAY_BUFFER, color_data.size() * sizeof(float), color_data.data(),
	             GL_STATIC_DRAW);
	glBindBuffer(GL_ARRAY_BUFFER, shrunk_mesh_buffers_[0]);
	glBufferData(GL_ARRAY_BUFFER, shrunk_vertex_data.size() * sizeof(float),
	             shrunk_vertex_data.data(), GL_STATIC_DRAW);
	glBindBuffer(GL_ARRAY_BUFFER, 0);
}

void RenderingPrimitives::renderMeshFaces(bool is_shrunk) {
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glEnable(GL_COLOR_MATERIAL);
	glEnable(GL_CULL_FACE);
	glCullFace(GL_BACK);
	glFrontFace(GL_CCW);

	glEnableClientState(GL_VERTEX_ARRAY);
	glEnableClientState(GL_NORMAL_ARRAY);
	glEnableClientState(GL_COLOR_ARRAY);

	if (is_shrunk) {
		glBindBuffer(GL_ARRAY_BUFFER, shrunk_mesh_buffers_[0]);
	} else {
		glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[0]);
	}
	glVertexPointer(3, GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[1]);
	glNormalPointer(GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[2]);
	glColorPointer(4, GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, 0);

	glDrawArrays(GL_TRIANGLES, 0, num_vertices_);

	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[1]);
	glNormalPointer(GL_FLOAT, 0, reinterpret_cast<void*>(3 * num_vertices_ * sizeof(float)));
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[2]);
	glColorPointer(4, GL_FLOAT, 0, reinterpret_cast<void*>(4 * num_vertices_ * sizeof(float)));
	glBindBuffer(GL_ARRAY_BUFFER, 0);
	glFrontFace(GL_CW);

	glDrawArrays(GL_TRIANGLES, 0, num_vertices_);

	glDisableClientState(GL_VERTEX_ARRAY);
	glDisableClientState(GL_NORMAL_ARRAY);
	glDisableClientState(GL_COLOR_ARRAY);

	glFrontFace(GL_CCW);
	glDisable(GL_CULL_FACE);
}

void RenderingPrimitives::renderMeshEdges(float line_width) {
	// save current glLineWidth, and set it to the input value
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(line_width);

	glPolygonMode(GL_FRONT_AND_BACK, GL_LINE);
	glEnable(GL_COLOR_MATERIAL);

	glEnableClientState(GL_VERTEX_ARRAY);
	glEnableClientState(GL_NORMAL_ARRAY);
	glEnableClientState(GL_COLOR_ARRAY);

	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[0]);
	glVertexPointer(3, GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[1]);
	glNormalPointer(GL_FLOAT, 0, 0);
	glBindBuffer(GL_ARRAY_BUFFER, mesh_buffers_[2]);
	glColorPointer(4, GL_FLOAT, 0, reinterpret_cast<void*>(8 * num_vertices_ * sizeof(float)));
	glBindBuffer(GL_ARRAY_BUFFER, 0);

	glDrawArrays(GL_TRIANGLES, 0, num_vertices_);

	glDisableClientState(GL_VERTEX_ARRAY);
	glDisableClientState(GL_NORMAL_ARRAY);
	glDisableClientState(GL_COLOR_ARRAY);

	glLineWidth(width);
}

// shifts the positions of triangle vertices towards triangle barycenter by `shrink_factor`
void RenderingPrimitives::shrinkTriangle(Vec3d& v0, Vec3d& v1, Vec3d& v2,
                                         double proprortion_to_remove) {
	Vec3d barycenter = (v0 + v1 + v2) / 3;
	v0 = v0 + (barycenter - v0) * proprortion_to_remove;
	v1 = v1 + (barycenter - v1) * proprortion_to_remove;
	v2 = v2 + (barycenter - v2) * proprortion_to_remove;
}
