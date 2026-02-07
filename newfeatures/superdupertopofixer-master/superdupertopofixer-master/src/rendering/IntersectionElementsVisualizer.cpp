#include "IntersectionElementsVisualizer.h"

void IntersectionElementsVisualizer::init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) {
	topofixer_ = topofixer;
	assert(colors.size() >= 5);

	intersection_point_color_ = colors[0];
	edge_color_ = colors[1];
	inner_mesh_edge_color_ = colors[3];
	outer_mesh_edge_color_ = colors[4];

	// Grid edge - mesh face intersections
	grid_edge_mesh_face_inters_.insert(grid_edge_mesh_face_inters_.end(), 3, {});
	Grid3DInterface* grid = topofixer->getGrid3DCubical();
	absl::flat_hash_set<long long> processed_edges;
	for (const long long cell_id : grid->getCellsWithTriangles()) {
		for (const long long edge_id : grid->get_edges_neighboring_cell(cell_id)) {
			auto [it, is_inserted] = processed_edges.insert(edge_id);
			if (is_inserted) {
				continue;
			}

			long long dummy_i, dummy_j, dummy_k, orientation;
			grid->get_edge_coords(edge_id, dummy_i, dummy_j, dummy_k, orientation);
			std::vector<GridEdgeMeshFaceIntersection> intersections =
			    grid->get_intersections_on_edge(edge_id);
			grid_edge_mesh_face_inters_[orientation].insert(
			    grid_edge_mesh_face_inters_[orientation].end(), intersections.begin(),
			    intersections.end());
		}
	}

	// Grid face - mesh edge intersections
	grid_face_mesh_edge_inters_.insert(grid_face_mesh_edge_inters_.end(), 3, {});
	for (const long long face_id : grid->getFrontFacesVector()) {
		long long dummy_i, dummy_j, dummy_k, orientation;
		grid->get_face_coords(face_id, dummy_i, dummy_j, dummy_k, orientation);
		std::vector<GridFaceMeshEdgeIntersection> intersections =
		    grid->get_mesh_edge_intersections_on_face(face_id);
		grid_face_mesh_edge_inters_[orientation].insert(grid_face_mesh_edge_inters_[orientation].end(),
		                                                intersections.begin(), intersections.end());
	}
}

void IntersectionElementsVisualizer::display() {
	switch (current_state_) {
		case 0:
			break;
		case 1:
			renderGridEdgeMeshFaceIntersections(current_direction_);
			break;
		case 2:
			renderGridFaceMeshEdgeIntersections(current_direction_);
			break;
	}
}

void IntersectionElementsVisualizer::nextState() {
	current_state_ = (current_state_ + 1) % kMaxStates;
	printDescription();
}

void IntersectionElementsVisualizer::nextDirection() {
	current_direction_ = (current_direction_ + 1) % kMaxDirections;
}

void IntersectionElementsVisualizer::printDescription() const {
	switch (current_state_) {
		case 0:
			std::cout << "-no grid-mesh intersections rendered" << std::endl;
			break;
		case 1:
			std::cout << "-draw grid edge - mesh face intersections stored on grid" << std::endl;
			break;
		case 2:
			std::cout << "-draw grid face - mesh edge intersections stored on grid" << std::endl;
			break;
	}
}

void IntersectionElementsVisualizer::renderGridEdgeMeshFaceIntersections(unsigned int direction) {
	// Intersection points
	GLfloat point_size;
	glGetFloatv(GL_POINT_SIZE, &point_size);
	glPointSize(10.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glBegin(GL_POINTS);
	glColor3f(intersection_point_color_[0], intersection_point_color_[1],
	          intersection_point_color_[2]);
	for (int dir = 0; dir < kMaxDirections - 1; ++dir) {
		if (direction != dir && direction != kMaxDirections - 1) {
			continue;
		}

		for (const auto& intersection : grid_edge_mesh_face_inters_[dir]) {
			auto point = intersection.getPosition();
			glVertex3f(point[0], point[1], point[2]);
		}
	}
	glEnd();
	glPointSize(point_size);

	// Render grid edges.
	const Grid3DInterface* grid = topofixer_->getGrid3DCubical();
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(3.0);
	glBegin(GL_LINES);
	glColor3f(0, 0, 0);
	double x, y, z;
	for (int dir = 0; dir < kMaxDirections - 1; ++dir) {
		if (current_direction_ != dir && current_direction_ != kMaxDirections - 1) {
			continue;
		}

		for (const auto& intersection : grid_edge_mesh_face_inters_[dir]) {
			std::vector<long long> vertices = grid->get_verts_neighboring_edge(intersection.getEdgeId());
			grid->getVertexPosition(vertices[0], x, y, z);
			glVertex3f(x, y, z);
			grid->getVertexPosition(vertices[1], x, y, z);
			glVertex3f(x, y, z);
		}
	}
	glEnd();

	glLineWidth(width);
}

void IntersectionElementsVisualizer::renderGridFaceMeshEdgeIntersections(unsigned int direction) {
	// Intersection points
	GLfloat point_size;
	glGetFloatv(GL_POINT_SIZE, &point_size);
	glPointSize(10.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glBegin(GL_POINTS);
	glColor3f(intersection_point_color_[0], intersection_point_color_[1],
	          intersection_point_color_[2]);
	for (int dir = 0; dir < kMaxDirections - 1; ++dir) {
		if (direction != dir && direction != kMaxDirections - 1) {
			continue;
		}

		for (const auto& intersection : grid_face_mesh_edge_inters_[dir]) {
			auto point = intersection.getPosition();
			glVertex3f(point[0], point[1], point[2]);
		}
	}
	glEnd();
	glPointSize(point_size);

	// Render mesh edges.
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(3.0);
	glBegin(GL_LINES);
	for (int dir = 0; dir < kMaxDirections - 1; ++dir) {
		if (direction != dir && direction != kMaxDirections - 1) {
			continue;
		}

		for (const auto& intersection : grid_face_mesh_edge_inters_[dir]) {
			Vec3d v0 = intersection.getEdgeFirst()->getCoords();
			Vec3d v1 = intersection.getEdgeSecond()->getCoords();
			Vec3d point = intersection.getPosition();
			glColor3f(inner_mesh_edge_color_[0], inner_mesh_edge_color_[1], inner_mesh_edge_color_[2]);
			glVertex3f(v0[0], v0[1], v0[2]);
			glVertex3f(point[0], point[1], point[2]);

			glColor3f(outer_mesh_edge_color_[0], outer_mesh_edge_color_[1], outer_mesh_edge_color_[2]);
			glVertex3f(point[0], point[1], point[2]);
			glVertex3f(v1[0], v1[1], v1[2]);
		}
	}
	glEnd();
}

/*void OpenGLRenderer::renderGridEdgeTriangleIntersection(GridMeshIntersection intersection) {
  // Render point of intersection.
  auto point = intersection.getPosition();
  glBegin(GL_POINTS);
  glColor3f(0.0, 0.0, 1.0);
  glVertex3f(point[0], point[1], point[2]);
  glEnd();

  // Render intersected triangle.
  glEnable(GL_DEPTH_TEST);
  glDepthFunc(GL_LEQUAL);
  glDepthRange(0.0f, 1.0f);
  glClearDepth(1.0f);

  glEnable(GL_NORMALIZE);
  glEnable(GL_LIGHTING);
  glEnable(GL_LIGHT0);

  GLfloat mat_diffuse[] = {1.0, 1.0, 1.0, 1.0};
  glMaterialfv(GL_FRONT, GL_DIFFUSE, mat_diffuse);
  // GLfloat mat_specular[] = { 1.0, 1.0, 1.0, 1.0 };
  GLfloat mat_specular[] = {0.0, 0.0, 0.0, 0.0};
  glMaterialfv(GL_FRONT, GL_SPECULAR, mat_specular);
  // GLfloat mat_shininess[] = { 50.0 };
  // GLfloat mat_shininess[] = { 10.0 };
  GLfloat mat_shininess[] = {20.0};
  glMaterialfv(GL_FRONT, GL_SHININESS, mat_shininess);

  GLfloat light_ambient[] = {0.3, 0.3, 0.3, 1.0};
  glLightfv(GL_LIGHT0, GL_AMBIENT, light_ambient);
  GLfloat light_direction[] = {1.0, 1.0, 1.0, 0.0};
  glLightfv(GL_LIGHT0, GL_SPOT_DIRECTION, light_direction);

  glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
  glEnable(GL_COLOR_MATERIAL);

  Mesh3DTriangle* triangle = intersection.getTriangle();

  std::vector<Mesh3DVertex*> verts(3, nullptr);
  triangle->getVerts(&verts[0], &verts[1], &verts[2]);
  Vec3d norm = cross(mesh->getVertCoords(verts[1]) - mesh->getVertCoords(verts[0]),
                     mesh->getVertCoords(verts[2]) - mesh->getVertCoords(verts[0]));

  glBegin(GL_TRIANGLES);
  glNormal3f(norm[0], norm[1], norm[2]);
  glColor3f(1.0, 0.0, 0.0);
  for (Mesh3DVertex* vert : verts) {
    Vec3d coords = mesh->getVertCoords(vert);
    glVertex3f(coords[0], coords[1], coords[2]);
  }
  glEnd();


}
*/