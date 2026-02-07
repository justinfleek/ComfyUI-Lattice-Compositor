/* MultiLabelMarchingCuber.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the implementation file for the module that executes the multi-label marching cubes
 * algorithm.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "MultiLabelMarchingCuber.h"

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DVertex.h"

//------------------------------------------------------------
// coordinating functions
//------------------------------------------------------------

// function that coordinates the run of the multi-label marching cuber module
int MultiLabelMarchingCuber::run(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                 GridMeshIntersector& intersector_, int orientation) {
	int return_value = 0;

	// initialize the numerical predicate, serves to determine opposite assignment for HCs around
	// internal non-manifold edges
	intersector.exactinit();

	// retrieve the set of front faces; we need to keep track of it due to the fact that reconstructed
	// triangles in complex front cells have to be generated in a way that allows connecting them to
	// the existing mesh
	absl::flat_hash_set<long long> front_faces = grid.getFrontFacesSet();
	// retrieve the map that assigns to each grid vertex in the complex region a unique material
	// label; the map was filled with data during the run of the LabelResolver module
	absl::flat_hash_map<long long, int>& unique_labeling = grid.getUniqueLabelingMap();

	// make labels on complex grid vertices unique via a BFS flood fill
	// generateUniqueLabelsOnGridVerticesNaiveFloodFill(grid, vertices_to_process);
	generateMeshVerticesOnGridEdges(mesh, grid, front_faces, unique_labeling);

	// initialize cell reconstruxction statistics
	number_of_reconstructed_cells = 0;
	number_of_cells_with_only_1_material = 0;
	number_of_cells_with_exactly_2_materials = 0;
	number_of_cells_with_unambiguous_faces = 0;
	number_of_reconstructed_cells_with_corner_configuration = 0;
	number_of_reconstructed_cells_with_two_corners_configuration = 0;
	number_of_reconstructed_cells_with_edge_configuration = 0;

	// reconstruct mesh surface in complex cells, assign opposites of HCs across front faces, and
	// store extending half-corners of new mesh edges for the assignemnt of remaining HC opposites
	generateComplexCellIsosurfaces(mesh, grid, front_faces, unique_labeling);

	// print cell reconstruction statistics
	if (settings->verbosity >= 2) {
		std::cout << "-marching cubes reconstruction statistics:\n";
		std::cout << "--complex cells: "
		          << grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed).size() << '\n';
		std::cout << "--reconstructed cells: " << number_of_reconstructed_cells << '\n';
		std::cout << "--cell with only 1 material: " << number_of_cells_with_only_1_material << '\n';
		if (settings->marching_cubes_method ==
		    TopoFixerSettings::MarchingCubesMethod::EightOctantMethodPlusOptimizedTwoMat) {
			std::cout << "--cells with exactly 2 materials: " << number_of_cells_with_exactly_2_materials
			          << '\n';
			std::cout << "--2 material cells with unambiguous faces: "
			          << number_of_cells_with_unambiguous_faces << '\n';
			std::cout << "--reconstructed cells with corner configuration: "
			          << number_of_reconstructed_cells_with_corner_configuration << '\n';
			std::cout << "--reconstructed cells with two corners configuration: "
			          << number_of_reconstructed_cells_with_two_corners_configuration << '\n';
			std::cout << "--reconstructed cells with edge configuration: "
			          << number_of_reconstructed_cells_with_edge_configuration << '\n';
		}
	}

	// assign HC opposites across the remaining various types of edges
	moveVertsToNaiveLocations(mesh, grid);
	assignHalfCornerOpposites(mesh, grid);
	moveVertsToOptimizedLocations(mesh);

	// check that the mesh is consistent
	auto consistency_check_type = settings->run_input_mesh_consistency_tests;
	if (consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::All ||
	    consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::Critical) {
		mesh.runMeshConsistencyChecks();
	}

	if (settings->verbosity >= 1) {
		std::cout << "-multi-label marching cuber finished with return value " << return_value
		          << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// clear marching cubes data structures
void MultiLabelMarchingCuber::clearState() {
	grid_edge_mesh_vertex_map.clear();
	grid_face_mesh_vertex_map.clear();
	optimized_grid_faces.clear();
	internal_extending_corners.clear();
	front_extending_corners.clear();
	transition_extending_corners.clear();

	optimized_cells.clear();
	cell_verts.clear();
	edge_verts.clear();
	face_verts.clear();
	triangle_to_cell.clear();
	cell_to_triangles.clear();
	edges_with_suggested_point.clear();
	internal_extending_corners.clear();
	front_extending_corners.clear();
	transition_extending_corners.clear();

	optimized_triangles.clear();
}

//------------------------------------------------------------
// functions for generating unique labeling
//------------------------------------------------------------

void MultiLabelMarchingCuber::generateMeshVerticesOnGridEdges(
    Mesh3DInterface& mesh, Grid3DInterface& grid, const absl::flat_hash_set<long long>& front_faces,
    const absl::flat_hash_map<long long, int>& unique_labeling) {
	// go over all non-front grid edges in the complex region, if the
	for (long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
		for (long long edge : grid.get_edges_neighboring_cell(ccell)) {
			std::vector<Mesh3DVertex*> mesh_verts_on_edge = grid.get_mesh_vertices_on_edge(edge);
			if (!mesh_verts_on_edge.empty()) {
				assert(mesh_verts_on_edge.size() == 1);
				assert(grid.isFrontEdge(edge));
				grid_edge_mesh_vertex_map[edge] = mesh_verts_on_edge[0];
			} else {
				/*if (grid.hasOptimizedMCEdgePoint(edge)) {
				  obtainGridEdgeCenterVertex(mesh, grid, edge);
				}*/

				if (!grid.isFrontEdge(edge)) {
					std::vector<long long> edge_endpoints = grid.get_verts_neighboring_edge(edge);
					int mat_v0 = unique_labeling.at(edge_endpoints[0]);
					int mat_v1 = unique_labeling.at(edge_endpoints[1]);
					if (mat_v0 != mat_v1) {
						obtainGridEdgeCenterVertex(mesh, grid, edge);
					}
				}
			}
		}
	}

	for (long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
		for (long long face : grid.get_faces_neighboring_cell(ccell)) {
			if (!grid.isFaceInComplexFront(face)) {
				int vertices_on_edges = 0;
				for (long long edge : grid.get_edges_neighboring_face(face)) {
					auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
					if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
						vertices_on_edges++;
					}
				}
				assert(vertices_on_edges != 1);
				if (vertices_on_edges > 1) {
					obtainGridFaceAverageVertex(mesh, grid, face);
				}
			}
		}
	}

	/*for (int ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
	  for (int face : grid.get_faces_neighboring_cell(ccell)) {
	    if (!grid.isFaceInComplexFront(face)) {
	      int vertices_on_edges = 0;
	      for (int edge : grid.get_edges_neighboring_face(face)) {
	        auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
	        if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
	          vertices_on_edges++;
	        }
	      }
	      assert(vertices_on_edges != 1);
	      if (vertices_on_edges > 1) {
	        obtainGridFaceAverageVertex(mesh, grid, face);
	      }
	    }
	  }
	}*/

	/*for (int ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
	  if (!allCellVerticesEqual(grid, ccell)) {
	    obtainGridCellAverageVertex(mesh, grid, ccell);
	  }


	    for (int face : grid.get_faces_neighboring_cell(ccell)) {
	    if (!grid.isFaceInComplexFront(face)) {
	      int vertices_on_edges = 0;
	      for (int edge : grid.get_edges_neighboring_face(face)) {
	        auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
	        if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
	          vertices_on_edges++;
	        }
	      }
	      assert(vertices_on_edges != 1);
	      if (vertices_on_edges > 1) {
	        obtainGridFaceAverageVertex(mesh, grid, face);
	      }
	    }
	  }
	}*/

	// iterate over front edges, if there exists a mesh vertex on a front edge (there can be at most
	// one), assign it to the edge id in `grid_edge_mesh_vertex_map`; these vertices will later be
	// used for constructing marching cubes triangles
	/*for (int front_face : front_faces) {
	  for (int front_edge : grid.get_edges_neighboring_face(front_face)) {
	    std::vector<Mesh3DVertex*> mesh_verts_on_edge = grid.get_mesh_vertices_on_edge(front_edge);
	    if (!mesh_verts_on_edge.empty()) {
	      assert(mesh_verts_on_edge.size() == 1);
	      grid_edge_mesh_vertex_map[front_edge] = mesh_verts_on_edge[0];
	    }
	  }
	}
	*/
}

//------------------------------------------------------------
// functions for reconstructing mesh surface
//------------------------------------------------------------

// function for generating isosurafces in complex cells from sparse grid labels
void MultiLabelMarchingCuber::generateComplexCellIsosurfaces(
    Mesh3DInterface& mesh, Grid3DInterface& grid, const absl::flat_hash_set<long long>& front_faces,
    const absl::flat_hash_map<long long, int>& unique_labeling) {
	// ASSERT: there should be no flexible complex cells at this point
	assert(grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFlexible).size() == 0);

	// iterate over complex cells, for each one reconstruct the surface mesh inside it using a
	// variant of the marching cubes algorithm
	if (settings->marching_cubes_method ==
	    TopoFixerSettings::MarchingCubesMethod::EightOctantMethod) {
		for (const long long ccell :
		     grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
			// skip over cells where all vertices have the same label
			if (!allCellVerticesEqual(grid, unique_labeling, ccell)) {
				// use the 8-octant marching cubes reconstruction method on `ccell`
				reconstructMeshInCell8Octant(mesh, grid, front_faces, unique_labeling, ccell);
				number_of_reconstructed_cells++;
			} else {
				number_of_cells_with_only_1_material++;
			}
		}
	} else if (settings->marching_cubes_method ==
	           TopoFixerSettings::MarchingCubesMethod::EightOctantMethodPlusOptimizedTwoMat) {
		// labels present in a complex cell with exactly 2 different materials on its vertices, saved in
		// the order (less frequent, more frequent)
		Vec2i labels;
		// set of cells to be reconstructed using the 8-octant method (can't be reconstructed in an
		// optimized way)
		absl::flat_hash_set<long long> cells_to_reconstruct_with_8_octant_method;
		// determine the configuration of labels in `ccell`, if there are exactly two labels in a
		// non-ambiguous configuration,	and an optimized reconstruction wouldn't touch a front face,
		// reconstruct mesh in `ccell` in an optimized way; otherwise use the 8-octant method
		for (const long long ccell :
		     grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
			// determine the label configuration on vertices of `ccell`, cases are:
			// == 0 ... all vertices have the same label
			// > 0 ... two labels are present in a non-ambiguous configuration, suitable for optimized
			// reconstruction
			// == -1 ... either three or more lables are present, or two labels are present in an
			// ambiguous configuration, or any unambiguous reconstruction would happen at a	front face
			int cell_configuration =
			    retrieveVertexLabelConfigurationOnCell(grid, unique_labeling, ccell, labels);
			if (cell_configuration > 0) {
				// if two labels are present on vertices in a non-ambiguous configuration and an optimized
				// reconstruction wouldn't touch a front face, resolve marching cubes in an optimized
				// case-by-case manner
				reconstructMeshInCell2Material(mesh, grid, ccell, cell_configuration, labels);
				// store `ccell` as an optimized cell
				optimized_cells.insert(ccell);
				number_of_reconstructed_cells++;
				continue;
			} else if (cell_configuration < 0) {
				// label configuration on `ccell` is -1, save the cell to be reconstructed using 8-octant
				// method
				cells_to_reconstruct_with_8_octant_method.insert(ccell);
				continue;
			}
			// if label configuration in `ccell` is 0 (all vertices have the same label), no
			// reconstruction is done
			number_of_cells_with_only_1_material++;
		}
		for (const long long ccell : cells_to_reconstruct_with_8_octant_method) {
			// reconstruct remaining cells using the 8-octant marching cubes reconstruction method
			reconstructMeshInCell8Octant(mesh, grid, front_faces, unique_labeling, ccell);
			number_of_reconstructed_cells++;
		}
	}
}

// reconstruct mesh surface inside input `ccell` using the 8-octant method
void MultiLabelMarchingCuber::reconstructMeshInCell8Octant(
    Mesh3DInterface& mesh, Grid3DInterface& grid,
    const absl::flat_hash_set<long long>& front_faces_set,
    const absl::flat_hash_map<long long, int>& unique_labeling, const long long& ccell) {
	// set of front faces that have been reconstructed (have had adjacent triangles generated), used
	// to prevent reconstructing the same front face multiple times; inner grid faces can only ever be
	// reconstructed once, there is therefore no need to store them
	absl::flat_hash_set<long long> visited_front_faces;

	// generate a mesh vertex at the center of the cell
	// make a special procedure for front cells
	// Vec3d cell_center = grid.getCellCenter(ccell);
	Vec3d cell_vertex_pos = Vec3d(0.0);
	/*int num_faces_with_verts = 0;
	for (int face : grid.get_faces_neighboring_cell(ccell)) {
	  auto face_vertex_pair_it = grid_face_mesh_vertex_map.find(face);
	  if (face_vertex_pair_it != grid_face_mesh_vertex_map.end()) {
	    cell_vertex_pos += face_vertex_pair_it->second->getCoords();
	    num_faces_with_verts++;
	  }
	}
	cell_vertex_pos /= double(num_faces_with_verts);*/
	int num_edges_with_verts = 0;
	for (long long edge : grid.get_edges_neighboring_cell(ccell)) {
		auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
		if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
			cell_vertex_pos += edge_vertex_pair_it->second->getCoords();
			num_edges_with_verts++;
		}
	}
	cell_vertex_pos /= double(num_edges_with_verts);
	Mesh3DVertex* cell_vert = mesh.makeNewVertexAtCoords(cell_vertex_pos);
	grid.insertNewMeshVertexIntoCellSet(cell_vert, ccell);
	cell_verts[cell_vert] = ccell;

	// stores labels of grid vertices adjacent to a grid edge
	Vec2i edge_vertex_labels;
	// retrieve the 12 grid edges adjacent to `ccell`
	std::vector<long long> cell_edges = grid.get_edges_neighboring_cell(ccell);

	// iterate over the 12 grid edges of `ccell`; for each edge, whenever labels on its vertices don't
	// match, iterate over its 2 neighbor faces in `ccell`, and depending on the face type (front,
	// optimized, normal), reconstruct mesh triangles inside `ccell`
	for (int eit = 0; eit < 12; ++eit) {
		// retrieve the two grid vertices adjacent to current edge
		std::vector<long long> edge_vertices = grid.get_verts_neighboring_edge(cell_edges[eit]);

		// retrieve grid labels of `edge_vertices`
		edge_vertex_labels[0] = unique_labeling.at(edge_vertices[0]);
		edge_vertex_labels[1] = unique_labeling.at(edge_vertices[1]);
		// if both vertices of the current edge have the same label, no triangles touching the current
		// edge are generated; skip to the next edge in `ccell`
		if (edge_vertex_labels[0] == edge_vertex_labels[1]) {
			continue;
		}

		// labels on vertices of current edge are different, we proceed to generating mesh triangles

		// decode grid labels on vertices of current edge into mesh labels
		edge_vertex_labels = grid.convertGridLabelToMeshLabel(edge_vertex_labels);

		// at this point we have a mesh vertex at the center of `ccell` (`cell_vert`); we proceed to
		// generating new mesh triangles; we independently consider both grid faces of `ccell` adjacent
		// to the current edge, for each there are three possible cases:
		// 1. the face is normal, i.e. neither front nor optimized, we obtain two mesh vertices:
		// 1.1  a mesh vertex it the center of current edge (`edge_vert`),
		// 1.2  a mesh vertex in the center of the face (`face_vert`), and generate a mesh triangle by
		// connecting `cell_vert`, `face_vert`, and `edge_vert`
		// 2. current face is a front face, in which case we generate a mesh triangle for each edge in
		// the face graph by connecting `cell_vert` with the two endpoints of the graph edge
		// 3. current face is an optimized face, in which case we check whether the optimized face has
		// already been reconstructed (has had a touching triangle generated); if not, we generate the
		// touching triangle by connecting `cell_vert` with the two vertices of the optimized face

		// retrieve the two grid faces of `ccell` that are adjacent to current edge; the faces are
		// stored in a specific order stemming from their relative orientations with respect to current
		// edge; this is used, if the face is normal, to make subsequent triangle generation easy;
		// specifically, face 0 is chosen so that orientation `cell_vert`->`face_vert`->`edge_vert` +
		// right hand rule points towards vertex 0 of current edge, and orientation
		// `cell_vert`->`edge_vert`->`face_vert` + right hand rule points towards vertex 1 of current
		// edge
		std::vector<long long> edge_faces = grid.getFacesNeighboringEdgeInCell(eit, ccell);
		for (int fit = 0; fit < 2; ++fit) {
			// check whether current face is a front face
			if (front_faces_set.count(edge_faces[fit])) {
				// reconstruct triangles at a front face

				// check that current face hasn't been processed yet
				if (!visited_front_faces.count(edge_faces[fit])) {
					// mark current face as visited
					visited_front_faces.insert(edge_faces[fit]);
					// generate mesh triangles connecting `cell_vert` with mesh vertices that constitute nodes
					// of the face graph of the current face
					generateTrianglesAdjacentToFrontFace(mesh, grid, cell_vert, edge_faces[fit]);
				}
			} else {
				// check whether current face is an optimized face
				auto o_face = optimized_grid_faces.find(OptimizedFace(edge_faces[fit]));
				if (o_face != optimized_grid_faces.end()) {
					// if the current face is an optimized face, check if it has already been processed
					if (!o_face->has_been_reconstructed) {
						// reconstruct a triangle at an optimized face

						// generate a new triangle with two points and vertex labels retrieved from the
						// optimized face
						Mesh3DTriangle* new_triangle =
						    mesh.makeNewTriangle(cell_vert, o_face->v0, o_face->v1, o_face->labels);

						// TODO: evaluate whether this information should be saved as is
						mesh.addMCTriangle(new_triangle);
						triangle_to_cell[new_triangle] = ccell;
						cell_to_triangles[ccell].insert(new_triangle);

						// add the half-corners of `new_triangle` into `internal_extending_corners`, this data
						// will be used for half-corner opposite assignment
						addInternalExtendingCorners(mesh, new_triangle);
						// set the current optimized face as processed
						o_face->has_been_reconstructed = true;
					}
				} else {
					// reconstruct triangles at a normal face

					// obtain a mesh vertex on current edge, either by picking the existing one (there can
					// be at most one mesh vertex on an edge of a complex cell), or by generating a new one
					Mesh3DVertex* edge_vert = obtainGridEdgeCenterVertex(mesh, grid, cell_edges[eit]);
					if (edge_verts.count(edge_vert) == 0) {
						edge_verts[edge_vert] = {eit, ccell};
					}

					// obtain a mesh vertex on the current face, either by picking the existing one (there
					// can be at most one mesh vertex an a non-front face of a complex cell), or by generating
					// a new one
					Mesh3DVertex* face_vert = obtainGridFaceCenterVertex(mesh, grid, edge_faces[fit]);
					// face_verts[face_vert] = edge_faces[fit];
					// debug
					for (long long n_face_it : grid.get_faces_neighboring_cell(ccell)) {
						if (n_face_it == edge_faces[fit]) {
							face_verts[face_vert] = n_face_it;
						}
					}

					// generate a mesh triangle connecting `cell_vert`, `face_vert`, `edge_vert`; we have to
					// make sure that 0-orientation of the new triangle (determined by the order of vertices
					// in its generating function) plus right hand rule points towards the vertex with the
					// new triangle's 0th material; this means that the triangles we generate when `fit`
					// equals 0 when `fit` equals 1 have to either have flipped order of vertices, or flipped
					// order of materials; we choose the former
					Mesh3DTriangle* new_triangle;
					if (fit == 0) {
						new_triangle =
						    mesh.makeNewTriangle(cell_vert, face_vert, edge_vert, edge_vertex_labels);
					} else {
						new_triangle =
						    mesh.makeNewTriangle(cell_vert, edge_vert, face_vert, edge_vertex_labels);
					}

					// TODO: evaluate whether this information should be saved as is
					mesh.addMCTriangle(new_triangle);
					triangle_to_cell[new_triangle] = ccell;
					cell_to_triangles[ccell].insert(new_triangle);

					// add the half-corners of `new_triangle` into `internal_extending_corners`, this data
					// will be used for half-corner opposite assignment
					addInternalExtendingCorners(mesh, new_triangle);
				}
			}
		}
	}
}

// reconstruct mesh surface inside input `ccell` in an optimized way, based on its vertex label
// configuration `cell_configuration`, and store grid faces adjacent to the newly generated
// triangles as optimized faces in `optimized_grid_faces`
void MultiLabelMarchingCuber::reconstructMeshInCell2Material(Mesh3DInterface& mesh,
                                                             Grid3DInterface& grid,
                                                             const long long ccell,
                                                             const int cell_configuration,
                                                             const Vec2i grid_labels) {
	// reconstruct cells with the corner configuration
	if (cell_configuration <= 8) {
		// retrieve edges of `ccell`
		std::vector<long long> cell_edge = grid.get_edges_neighboring_cell(ccell);
		// retrieve faces adjacent to the minor label vertex in `ccell` in order: face in yz plane,
		// face in xz plane, face in xy plane
		std::vector<long long> adj_faces =
		    grid.getFacesNeighboringVertexInCell(cell_configuration - 1, ccell);
		// vertices of the triangle to be generated
		Mesh3DVertex *tri_vert_0 = nullptr, *tri_vert_1 = nullptr, *tri_vert_2 = nullptr;
		// convert input `grid_labels` into mesh labels to use with the generated triangle
		Vec2i mesh_labels = Vec2i(grid.convertGridLabelToMeshLabel(grid_labels));

		// reconstructed mesh in `ccell` will be a single triangle, find its vertices; the order of how
		// we save the vertices is important - we also want to store each of the three grid faces of
		// `ccell` that are adjacent to the minor label vertex as optimized faces, each storing two
		// vertices v0,v1 of the newly generated triangle in such a way, that when we process a
		// non-optimized complex cell `no_ccell` adjacent to `ccell`, all we have to do to connect the
		// mesh in `ccell` and `no_ccell` correctly, is to generate the triangle (center of `no_ccell`,
		// v0, v1). As such, we have to make sure that we choose the order of vertices on the new
		// triangle, the order of labels on the new triangle, and the order of vertices on the optimized
		// faces in a compatible way.
		switch (cell_configuration - 1) {
			case 0:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[0]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[8]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[4]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {0, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {8, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {4, ccell};
				}
				break;
			case 1:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[0]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[9]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[5]);
				mesh_labels = Vec2i(mesh_labels[1], mesh_labels[0]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {0, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {9, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {5, ccell};
				}
				break;
			case 2:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[1]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[10]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[4]);
				mesh_labels = Vec2i(mesh_labels[1], mesh_labels[0]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {1, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {10, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {4, ccell};
				}
				break;
			case 3:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[2]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[8]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[6]);
				mesh_labels = Vec2i(mesh_labels[1], mesh_labels[0]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {2, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {8, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {6, ccell};
				}
				break;
			case 4:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[1]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[11]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[5]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {1, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {11, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {5, ccell};
				}
				break;
			case 5:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[3]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[10]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[6]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {3, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {10, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {6, ccell};
				}
				break;
			case 6:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[2]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[9]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[7]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {2, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {9, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {7, ccell};
				}
				break;
			case 7:
				tri_vert_0 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[3]);
				tri_vert_1 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[11]);
				tri_vert_2 = obtainGridEdgeCenterVertex(mesh, grid, cell_edge[7]);
				mesh_labels = Vec2i(mesh_labels[1], mesh_labels[0]);
				// debug
				if (edge_verts.count(tri_vert_0) == 0) {
					edge_verts[tri_vert_0] = {3, ccell};
				}
				if (edge_verts.count(tri_vert_1) == 0) {
					edge_verts[tri_vert_1] = {11, ccell};
				}
				if (edge_verts.count(tri_vert_2) == 0) {
					edge_verts[tri_vert_2] = {7, ccell};
				}
				break;
		}

		// add the three faces adjacent to the minor label vertex to `optimized_grid_faces`, each one
		// with a pair of `mesh_labels`, and two vertices of the new triangle that lie in the optimized
		// face; the order of faces, labels, and vertices is carefully chosen to produce a consistent
		// result
		optimized_grid_faces.emplace(adj_faces[0], mesh_labels, tri_vert_2, tri_vert_1);
		optimized_grid_faces.emplace(adj_faces[1], mesh_labels, tri_vert_1, tri_vert_0);
		optimized_grid_faces.emplace(adj_faces[2], mesh_labels, tri_vert_0, tri_vert_2);

		// generate the new triangle
		Mesh3DTriangle* new_triangle =
		    mesh.makeNewTriangle(tri_vert_0, tri_vert_1, tri_vert_2, mesh_labels);

		// add the half-corners of `new_triangle` into `internal_extending_corners`, this data will
		// be used for half-corner opposites assignment
		addInternalExtendingCorners(mesh, new_triangle);

		// TODO: evaluate whether this information should be saved as is
		mesh.addMCTriangle(new_triangle);
		optimized_triangles.insert(new_triangle);
		triangle_to_cell[new_triangle] = ccell;
		cell_to_triangles[ccell].insert(new_triangle);

		// note that a cell with the corner label configuration was reconstructed in an optimized way
		number_of_reconstructed_cells_with_corner_configuration++;
	}

	// TODO: continue the reconstruction on a case-by-case basis
}

// generate triangles connecting center of a complex cell with face graph edges on a front face
void MultiLabelMarchingCuber::generateTrianglesAdjacentToFrontFace(Mesh3DInterface& mesh,
                                                                   Grid3DInterface& grid,
                                                                   Mesh3DVertex* cell_vert,
                                                                   long long front_face) {
	// retrieve the graph on `front_face`; nodes of the graph are mesh vertices, the graph is saved as
	// a map where a key is a pair of mesh vertices that defines a graph edge, and its value is a
	// pointer to a mesh triangle, which at this point in the algorithm's run is the unique triangle
	// that includes this graph edge - it lies in the simple region, the other triangle attached to
	// this edge would have been in the complex cell and was therefore deleted, and the edge can't be
	// non-manifold due to SoS resolution of degenerate intersection cases
	const Grid3DInterface::FaceGraph& graph_on_face = grid.getGraphOnFace(front_face);

	// iterate over edges of the graph
	for (const auto& [graph_edge, oppos_triangle] : graph_on_face) {
		// pointers to the new mesh triangle that is to be generated, and to a HC on `oppos_triangle`
		// that we will set to be the opposite of a HC at `cell_vert` in the new triangle; because
		// `oppos_triangle` was generated in cell separator according to right hand rule, we can ensure
		// a compatible assignment of labels and opposites on the new triangle by anchoring it to
		// `oppos_triangle`
		Mesh3DTriangle* new_triangle;
		Mesh3DHalfCorner* extending_hfc;

		// intrinsic orientation on a triangle can be defined (among others) by the following
		// elements:
		// -triangle itself: taking the reference half-corner of the triangle and following `next`
		// pointers
		// -triangle half-corner: following `next` pointers given a half-corner of the triangle
		// -oriented triangle edge: following triangle vertices from vertex 0 to vertex 1 of a given
		// edge;
		// we say that a pair of elements is compatible, if both define the same orientation on a
		// triangle

		// check if `graph_edge` is compatible with `oppos_triangle`; additionally, store into
		// `oppos_hfc` the extending half-corner of `graph_edge` on `oppos_triangle` that is
		// compatible with `graph_edge`
		if (oppos_triangle->isEdgeOrientedSameAsTriangle(graph_edge.first, graph_edge.second,
		                                                 &extending_hfc)) {
			// we work with the assumption, that `oppos_triangle` was constructed to abide by the right
			// hand rule; in order for the new triangle to abide by the right hand rule, we anchor it to
			// `oppos_triangle`: we construct `new_triangle` so that either it traverses `graph_edge` in
			// the opposite direction compared to `oppos_triangle`, or its label assignment is flipped; we
			// choose the first option, which together with the observation that `graph_edge` and
			// `oppos_triangle` are compatible implies, that we have to generate the new triangle so that
			// its 0-orientation traverses `graph_edge` from its larger to its smaller vertex
			new_triangle = mesh.makeNewTriangle(cell_vert, graph_edge.second, graph_edge.first,
			                                    oppos_triangle->getLabels());
		} else {
			// we work with the assumption, that `oppos_triangle` was constructed to abide by the right
			// hand rule; in order for the new triangle to abide by the right hand rule, we anchor it to
			// `oppos_triangle`: we construct `new_triangle` so that either it traverses `graph_edge` in
			// the opposite direction compared to `oppos_triangle`, or its label assignment is flipped; we
			// choose the first option, which together with the observation that `graph_edge` and
			// `oppos_triangle` are not compatible implies, that we have to generate the new triangle so
			// that its 0-orientation traverses `graph_edge` from its smaller to its larger vertex
			new_triangle = mesh.makeNewTriangle(cell_vert, graph_edge.first, graph_edge.second,
			                                    oppos_triangle->getLabels());
			// we flip `extending_hfc` to its dual side, so that it is a 0-orientation HC
			extending_hfc = extending_hfc->getDual();
		}

		// we assign opposite pointers of the four extending half-corners of `graph_edge` (two dual
		// ones on `oppos_triangle`, two dual ones on `new_triangle`), i.e. the opposite pointers
		// across the front face; the specifics of the assignment (which half-corners should be
		// connected) are fully determined by the anchoring relationship between `new_triangle` and
		// `oppos_triangle` - we made sure that 0-orientations on `oppos_triangle` and `new_triangle`
		// plus right hand rule point into the same region; we set 0-orientation HCs as opposites of
		// each other, and 1-orientation HCs as opposites of each other (for `oppos_triangle`, we know
		// that `extending_hfc` is a 0-orientation HC)
		assert(extending_hfc->getLabel() == new_triangle->getHalfCorner()->getLabel());
		assert(extending_hfc->getDual()->getLabel() ==
		       new_triangle->getHalfCorner()->getDual()->getLabel());
		extending_hfc->setOppos(new_triangle->getHalfCorner());
		new_triangle->getHalfCorner()->setOppos(extending_hfc);
		extending_hfc->getDual()->setOppos(new_triangle->getHalfCorner()->getDual());
		new_triangle->getHalfCorner()->getDual()->setOppos(extending_hfc->getDual());

		// TODO: evaluate whether this information should be saved as is
		mesh.addMCTriangle(new_triangle);
		triangle_to_cell[new_triangle] = grid.getCellIdForPoint(cell_vert->getCoords());
		cell_to_triangles[grid.getCellIdForPoint(cell_vert->getCoords())].insert(new_triangle);

		// add the remaining half-corners of `new_triangle` into `front_extending_corners`, this
		// data will be used for assigning opposites on the remaining half-corners of `new_triangle`
		addFrontExtendingCorners(mesh, new_triangle);
	}
}

//------------------------------------------------------------
// functions for determining cell configurations
//------------------------------------------------------------

// check whether all vertices of `cell_id` have the same unique label in `unique_labeling`
bool MultiLabelMarchingCuber::allCellVerticesEqual(
    const Grid3DInterface& grid, const absl::flat_hash_map<long long, int>& unique_labeling,
    const long long cell_id) const {
	auto cell_verts = grid.get_verts_neighboring_cell(cell_id);
	int first_label = unique_labeling.at(cell_verts[0]);
	for (int it = 1; it < 8; ++it) {
		if (unique_labeling.at(cell_verts[it]) != first_label) {
			return false;
		}
	}

	return true;
}

// check if the input grid face has an ambiguous configuration
bool MultiLabelMarchingCuber::isFaceAmbiguous(
    const Grid3DInterface& grid, const absl::flat_hash_map<long long, int>& unique_labeling,
    long long face_id) {
	std::vector<long long> face_vertices = grid.get_verts_neighboring_face(face_id);
	// a face has an ambiguous configuration, if the scheme of its vertex labels is ABAB
	return (unique_labeling.at(face_vertices[0]) == unique_labeling.at(face_vertices[3])) &&
	       (unique_labeling.at(face_vertices[1]) == unique_labeling.at(face_vertices[2])) &&
	       (unique_labeling.at(face_vertices[0]) != unique_labeling.at(face_vertices[1]));
}

// determine label configuration on vertices of `cell_id`
int MultiLabelMarchingCuber::retrieveVertexLabelConfigurationOnCell(
    Grid3DInterface& grid, const absl::flat_hash_map<long long, int>& unique_labeling,
    const long long cell_id, Vec2i& labels) {
	// retrieve the set of grid vertices of `cell_id`
	std::vector<long long> grid_verts_in_cell = grid.get_verts_neighboring_cell(cell_id);
	// vector that stores pairs (grid label,vector of relative vertex ids of `cell_id` that have
	// this grid label)
	std::vector<std::pair<int, std::vector<int>>> label_count;

	// iterate over vertices of `cell_id`
	int relative_vertex_index = 0;
	for (long long grid_vertex : grid_verts_in_cell) {
		// retrieve the label on `cell_vertex`
		int current_label = unique_labeling.at(grid_vertex);
		// query whether `current_label` has already appeared on some previous vertex of `cell_id`
		bool label_found = false;
		for (auto& [label, relative_vertices] : label_count) {
			if (label == current_label) {
				// if the label already appeared on a vertex of `cell_id`, add `relative_vertex_index`
				// to the vector of relative vertices with this label
				relative_vertices.push_back(relative_vertex_index);
				label_found = true;
				break;
			}
		}
		// if the label hasn't appeared on a vertex of `cell_id` before, then if there are less than
		// 2 labels stored in `label_count`, push back a new vector of vertices corresponding to
		// `current_label`; if there are 2 labels already present, meaning we would add a third one,
		// return -1 (cell mesh will be reconstructed using 8-octant method)
		if (label_found == false) {
			if (label_count.size() < 2) {
				label_count.push_back({current_label, {relative_vertex_index}});
			} else {
				return -1;
			}
		}
		relative_vertex_index++;
	}

	// ASSERT: at this point there should be either 1 or 2 different labels on vertices of
	// `cell_id`
	assert(label_count.size() == 1 || label_count.size() == 2);

	// if there is only one label on all vertices of `cell_id`, return 0 (no triangles will be
	// reconstructed in this cell)
	if (label_count.size() == 1) {
		return 0;
	}

	// at this point we know that there are exactly two materials on vertices of `cell_id`, we
	// proceed to detecting the specific labeling configuration
	number_of_cells_with_exactly_2_materials++;
	// ASSERT: both labels should have at least one associated vertex
	assert(label_count[0].second.size() > 0 && label_count[1].second.size() > 0);

	// determine which of the two labels is present on the vertices of `cell_id` less frequently
	// (minor label) and which is present more frequently (major label), save into `labels` in the
	// order (minor label, major label)
	int minor_label_index = -1;
	int major_label_index = -1;
	if (label_count[0].second.size() <= label_count[1].second.size()) {
		minor_label_index = 0;
		major_label_index = 1;
		labels = Vec2i(label_count[0].first, label_count[1].first);
	} else {
		minor_label_index = 1;
		major_label_index = 0;
		labels = Vec2i(label_count[1].first, label_count[0].first);
	}

	// resolve the case where there is exactly one vertex with one label, and seven vertices with
	// another label - corner configuration
	if (label_count[minor_label_index].second.size() == 1) {
		// ASSERT: if there is 1 minor label vertex, then there should be 7 major label vertices
		assert(label_count[major_label_index].second.size() == 7);
		number_of_cells_with_unambiguous_faces++;

		// iterate over the three faces of `cell_id` that touch the vertex with the minor label
		for (long long face :
		     grid.getFacesNeighboringVertexInCell(label_count[minor_label_index].second[0], cell_id)) {
			// if any of the faces are front faces, return -1 (we don't need to check for ambiguity,
			// for a cell with corner configuration all faces are unambiguous)
			if (grid.isFaceInComplexFront(face)) {
				return -1;
			}
		}
		// at this point we know the cell is suitable for optimized reconstruction, return the
		// relative poisition+1 of the minor label vertex in `cell_id` ASSERT: relative id of the
		// minor label vertex +1 should be in the interval [1,8] (as for any relative id of a vertex
		// +1)
		assert(label_count[minor_label_index].second[0] + 1 <= 8);
		return label_count[minor_label_index].second[0] + 1;
	}

	// check if all cell faces have unambiguous label configurations, that is, not the
	// configuration ABAB (2 pairs of labels, vertices with the same label diagonally opposite of
	// each other)
	for (long long face_id : grid.get_faces_neighboring_cell(cell_id)) {
		std::vector<long long> face_vertices = grid.get_verts_neighboring_face(face_id);
		// if an ambiguous configuration is found on the current face, we return -1 (`cell_id` will
		// be reconstructed using 8-octant method)
		if (isFaceAmbiguous(grid, unique_labeling, face_id)) {
			return -1;
		}
	}

	// at this point we know that all faces of `cell_id` are unambiguous, therefore the only
	// circumstance that would prevent us from reconstructing mesh in it in an optimized way,
	// would be if there are front faces that would be touching the reconstruced triangles
	number_of_cells_with_unambiguous_faces++;

	// minor label valence of a grid vertex v in `cell_id` is the number of its neighboring grid
	// vertices in `cell_id` that also have `minor_label`; we proceed to determining minor label
	// valence of each minor label vertex in `cell_id`, and storing them in
	// `minor_label_valences`: minor_label_valences[m] is the vector of relative vertex ids of
	// minor label vertices with minor label valence m (i.e. with exactly m minor label neighbors)
	std::vector<std::vector<int>> minor_label_valences(4, std::vector<int>());

	// determine minor label valences of minor label vertices in `cell_id`, iterate over minor
	// label vertices
	for (int relative_vertex_id : label_count[minor_label_index].second) {
		int num_minor_label_neighbors = 0;
		// iterate over neighbor vertices of `relative_vertex_id` in `cell_id`
		for (long long neighbor_vertex :
		     grid.getVertsNeighboringVertexInCell(relative_vertex_id, cell_id)) {
			// if `neighbor_vertex` is also a minor label vertex, increase the valence count of
			// `relative_vertex_id`
			if (std::find(label_count[minor_label_index].second.begin(),
			              label_count[minor_label_index].second.end(),
			              neighbor_vertex) != label_count[minor_label_index].second.end()) {
				num_minor_label_neighbors++;
			}
		}
		// save `relative_vertex_id` into a vector corresponding to its minor label valence
		minor_label_valences[num_minor_label_neighbors].push_back(relative_vertex_id);
	}

	// resolve the case where there are exactly two vertices with one label, and 6 vertices with
	// another label - edge or two corners configuration
	if (label_count[minor_label_index].second.size() == 2) {
		// ASSERT: if there are 2 minor label vertices, then there should be 6 major label vertices
		assert(label_count[major_label_index].second.size() == 6);

		// two corners configuration
		if (minor_label_valences[0].size() == 2) {
			assert(minor_label_valences[1].size() == 0 && minor_label_valences[2].size() == 0 &&
			       minor_label_valences[3].size() == 0);
			number_of_reconstructed_cells_with_two_corners_configuration++;
		}

		// edge configuration
		if (minor_label_valences[1].size() == 2) {
			assert(minor_label_valences[0].size() == 0 && minor_label_valences[2].size() == 0 &&
			       minor_label_valences[3].size() == 0);
			number_of_reconstructed_cells_with_edge_configuration++;
		}

		/*// iterate over the three faces of `cell_id` that touch the vertex with the minor label
		for (int face :
		     grid.getFacesNeighboringVertexInCell(label_count[minor_label_index].second[0], cell_id)) {
		  // if any of the faces are front faces, return -1 (we don't need to check for ambiguity,
		  // for a cell with corner configuration all faces are unambiguous)
		  if (grid.isFaceInComplexFront(face)) {
		    return -1;
		  }
		}
		// at this point we know the cell is suitable for optimized reconstruction, return the
		// relative poisition+1 of the minor label vertex in `cell_id` ASSERT: relative id of the
		// minor label vertex +1 should be in the interval [1,8] (as for any relative id of a vertex
		// +1)
		assert(label_count[minor_label_index].second[0] + 1 <= 8);
		return label_count[minor_label_index].second[0] + 1;*/
	}

	// TODO: continue the analysis
	return -1;
}

//------------------------------------------------------------
// functions for obtaining mesh elements on the grid
//------------------------------------------------------------

// if a mesh vertex is stored on input grid `edge`, return it, otherwise generate a mesh vertex
// in the center of `edge` and return it
Mesh3DVertex* MultiLabelMarchingCuber::obtainGridEdgeCenterVertex(Mesh3DInterface& mesh,
                                                                  Grid3DInterface& grid,
                                                                  long long edge) {
	auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
	if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
		return edge_vertex_pair_it->second;
	} else {
		//!!!
		Vec3d edge_center;
		if (grid.hasOptimizedMCEdgePoint(edge)) {
			edge_center = grid.getOptimizedMCEdgePoint(edge)->second;
			edges_with_suggested_point.insert(edge);

		} else {
			edge_center = grid.getEdgeCenter(edge);
		}
		Mesh3DVertex* edge_vertex = mesh.makeNewVertexAtCoords(edge_center);
		grid_edge_mesh_vertex_map[edge] = edge_vertex;
		// TODO: evaluate whether this data should be saved in this way
		grid.insertNewMeshVertexIntoEdgeSet(edge_vertex, edge);
		return edge_vertex;
	}
}

// if a mesh vertex is stored on input grid `face`, return it, otherwise generate a mesh vertex
// in the center of `face` and return it
Mesh3DVertex* MultiLabelMarchingCuber::obtainGridFaceCenterVertex(Mesh3DInterface& mesh,
                                                                  Grid3DInterface& grid,
                                                                  long long face) {
	auto face_vertex_pair_it = grid_face_mesh_vertex_map.find(face);
	if (face_vertex_pair_it != grid_face_mesh_vertex_map.end()) {
		return face_vertex_pair_it->second;
	} else {
		Vec3d face_center = grid.getFaceCenter(face);
		Mesh3DVertex* face_vertex = mesh.makeNewVertexAtCoords(face_center);
		grid_face_mesh_vertex_map[face] = face_vertex;
		// TODO: evaluate whether this data should be saved in this way
		grid.insertNewMeshVertexIntoFaceSet(face_vertex, face);
		return face_vertex;
	}
}

// if a mesh vertex is stored on input grid `face`, return it, otherwise generate a mesh vertex
// in the center of `face` and return it
Mesh3DVertex* MultiLabelMarchingCuber::obtainGridFaceAverageVertex(Mesh3DInterface& mesh,
                                                                   Grid3DInterface& grid,
                                                                   long long face) {
	auto face_vertex_pair_it = grid_face_mesh_vertex_map.find(face);
	if (face_vertex_pair_it != grid_face_mesh_vertex_map.end()) {
		return face_vertex_pair_it->second;
	} else {
		Vec3d face_avg = Vec3d(0.0);
		std::vector<long long> face_edges = grid.get_edges_neighboring_face(face);
		long long num_edge_verts = 0;
		for (long long edge : face_edges) {
			auto edge_vertex_pair_it = grid_edge_mesh_vertex_map.find(edge);
			if (edge_vertex_pair_it != grid_edge_mesh_vertex_map.end()) {
				face_avg += edge_vertex_pair_it->second->getCoords();
				num_edge_verts++;
			}
		}
		face_avg /= double(num_edge_verts);
		Mesh3DVertex* face_vertex = mesh.makeNewVertexAtCoords(face_avg);
		grid_face_mesh_vertex_map[face] = face_vertex;
		// TODO: evaluate whether this data should be saved in this way
		grid.insertNewMeshVertexIntoFaceSet(face_vertex, face);
		return face_vertex;
	}
}

//------------------------------------------------------------
// functions for assigning half-corner opposites
//------------------------------------------------------------

// add half corners of an internal `triangle` to `internal_extending_corners`, respecting the right
// hand rule
void MultiLabelMarchingCuber::addInternalExtendingCorners(Mesh3DInterface& mesh,
                                                          Mesh3DTriangle* triangle) {
	Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
	Mesh3DVertex* v0 = hfc->getVertex();
	Mesh3DVertex* v1 = hfc->getNext()->getVertex();
	Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
	int v0_index = mesh.getVertexIndex(v0);
	int v1_index = mesh.getVertexIndex(v1);
	int v2_index = mesh.getVertexIndex(v2);

	if (v0_index < v1_index) {
		internal_extending_corners[{v0, v1}].push_back(hfc->getPrev());
	} else {
		internal_extending_corners[{v1, v0}].push_back(hfc->getPrev()->getDual());
	}
	if (v0_index < v2_index) {
		internal_extending_corners[{v0, v2}].push_back(hfc->getNext()->getDual());
	} else {
		internal_extending_corners[{v2, v0}].push_back(hfc->getNext());
	}
	if (v1_index < v2_index) {
		internal_extending_corners[{v1, v2}].push_back(hfc);
	} else {
		internal_extending_corners[{v2, v1}].push_back(hfc->getDual());
	}
}

// add half corners of a front `triangle` to `front_extending_corners`, respecting the right hand
// rule
// NOTE: this could be sped up to just adding the two HCs to `front_extending_corners`, since
// `v0_index` is always lower than `v1_index` and `v2_index`
void MultiLabelMarchingCuber::addFrontExtendingCorners(Mesh3DInterface& mesh,
                                                       Mesh3DTriangle* triangle) {
	Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
	Mesh3DVertex* v0 = hfc->getVertex();
	Mesh3DVertex* v1 = hfc->getNext()->getVertex();
	Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
	int v0_index = mesh.getVertexIndex(v0);
	int v1_index = mesh.getVertexIndex(v1);
	int v2_index = mesh.getVertexIndex(v2);

	// front triangles always have complex cell midpoint as their zeroth vertex (`v0` here); the
	// HC at the cell midpoint has had its opposite assigned already (to a HC at a vertex in the
	// simple region, across the front face); we therefore need to add an extending HC for edges
	// {v0,v1} and {v0,v2} (curly brackets in this comment mean that we only specify the edges,
	// not how they're ordered - their ordering will depend on the integer indices of `v0_index`,
	// `v1_index`, `v2_index`)

	// `triangle` abides by the right hand rule, since it is anchored to a triangle in the simple
	// region, which was generated during cell separation in a way that makes it abide by the right
	// hand rule; we want to save the HC that is on the CW side when looking down an edge from its
	// smaller index vertex to its larger index vertex; for the edge {v0,v1}, we therefore have to
	// figure out whether the orientation (v0,v1) is compatible with the 0-orientation of `triangle`;
	//
	// to do this, we have to figure out whether , when looking along the edge (v0,v1)know
	// whether the edge orientation (v0,v1) is compatible with the 0-orientation of `triangle`; asking
	// "is `v0_index` smaller than `v1_index`" is therefore equivalent to asking "is the edge
	// orientation (v0,v1) compatible with the 0-orientation of `triangle`"?
	if (v0_index < v1_index) {
		front_extending_corners[{v0, v1}].push_back(hfc->getPrev());
	} else {
		// this should never happen, since `v1` and `v2` were generated during cell separation,
		// while `v0` was generated during marching cubes, and therefore has a lower index (indices
		// of mesh vertices are negative integers that decrease as new mesh vertices are generated)
		front_extending_corners[{v1, v0}].push_back(hfc->getPrev()->getDual());
		std::cout << "WARNING: this should never happen\n";
	}
	if (v0_index < v2_index) {
		front_extending_corners[{v0, v2}].push_back(hfc->getNext()->getDual());
	} else {
		// this should never happen, since `v1` and `v2` were generated during cell separation,
		// while `v0` was generated during marching cubes, and therefore has a lower index (indices
		// of mesh vertices are negative integers that decrease as new mesh vertices are generated)
		front_extending_corners[{v2, v0}].push_back(hfc->getNext());
		std::cout << "WARNING: this should never happen\n";
	}
}

//------------------------------------------------------------
// not yet cleaned up stuff
//------------------------------------------------------------

void MultiLabelMarchingCuber::assignHalfCornerOpposites(Mesh3DInterface& mesh,
                                                        Grid3DInterface& grid) {
	// assign the opposites of HCs on front face triangles (apart from opposites across the front
	// face, which were already assigned)
	for (auto& [mesh_edge, extending_hfcs] : front_extending_corners) {
		// if an edge has only one extending HC stored, it is a transition edge - a mesh edge
		// adjacent to one front triangle and one internal triangle (it cannot be non-manifold by
		// construction); store it in `transition_extending_corners`
		if (extending_hfcs.size() == 1) {
			transition_extending_corners[mesh_edge] = extending_hfcs;
		}
		// if an edge has exactly two extending HCs stored, it is a manifold front edge - a mesh
		// edge shared by exactly two front triangles; assigning opposite pointers on its extending
		// HCs is straightforward (both extending HCs stored are on the CW side when we project
		// `mesh_edge` onto an orthogonal plane in an orientation preserving way, and have to
		// therefore be connected primal to dual)
		if (extending_hfcs.size() == 2) {
			assert(extending_hfcs.at(0)->getLabel() == extending_hfcs.at(1)->getDual()->getLabel());
			extending_hfcs.at(0)->setOppos(extending_hfcs.at(1)->getDual());
			extending_hfcs.at(1)->getDual()->setOppos(extending_hfcs.at(0));
			assert(extending_hfcs.at(0)->getDual()->getLabel() == extending_hfcs.at(1)->getLabel());
			extending_hfcs.at(0)->getDual()->setOppos(extending_hfcs.at(1));
			extending_hfcs.at(1)->setOppos(extending_hfcs.at(0)->getDual());
		}
		// if an edge has three or more extending HCs stored, it is a non-manifold front edge - a
		// mesh edge shared by three or more front triangles; we use previously assigned opposite
		// pointers across the front face (i.e opposite pointers on extending HCs of front face mesh
		// edges) to determine the corrent assignment of opposite pointers around non-manifold front
		// edges
		if (extending_hfcs.size() > 2) {
			// newly generated vertex in the center of a complex cell, one of the endpoints of
			// `mesh_edge`
			Mesh3DVertex* cell_vertex;

			// determine `cell_vertex` and `face_vertex`, these are fixed for all base vertices around
			// `mesh_edge`
			if (grid.isVertexNewInCell(extending_hfcs[0]->getNext()->getVertex())) {
				cell_vertex = extending_hfcs[0]->getNext()->getVertex();
			} else {
				cell_vertex = extending_hfcs[0]->getPrev()->getVertex();
			}

			// iterate over extending HCs of `mesh_edge`
			for (Mesh3DHalfCorner* hfc : extending_hfcs) {
				// std::cout << "extending hfc at vertex: " << mesh.getVertexIndex(hfc->getVertex()) <<
				// '\n';

				// opposite HC of `hfc` that we are looking for
				Mesh3DHalfCorner* current_hfc = hfc;
				Mesh3DVertex* current_vertex = hfc->getVertex();
				do {
					current_hfc = current_hfc->getNext();
					// std::cout << "next: " << mesh.getVertexIndex(current_hfc->getVertex()) << '\n';
					current_hfc = current_hfc->getOppos();
					// std::cout << "oppos: " << mesh.getVertexIndex(current_hfc->getVertex()) << '\n';
					current_vertex = current_hfc->getVertex();
				} while (current_vertex != cell_vertex);

				Mesh3DHalfCorner* mirror_oppos_mirror = current_hfc->getNext();

				// assign opposite pointers between `hfc` and `mirror_oppos_mirror`
				assert(mirror_oppos_mirror != nullptr);
				assert(hfc->getLabel() == mirror_oppos_mirror->getLabel());
				hfc->setOppos(mirror_oppos_mirror);
				mirror_oppos_mirror->setOppos(hfc);
			}
		}
	}

	// assign opposites across internal manifold edges
	for (auto& [mesh_edge, extending_hfcs] : internal_extending_corners) {
		// if an edge has only one extending HC stored, it is a transition edge - a mesh edge
		// adjacent to one front triangle and one internal triangle (it cannot be non-manifold by
		// construction); store it in `transition_extending_corners`
		if (extending_hfcs.size() == 1) {
			// debug
			// print which cell the lonely triangle is in
			/*int q_cell = triangle_to_cell[extending_hfcs[0]->getTri()];
			std::cout << "cell of lonely triangle: " << q_cell << '\n';
			if (optimized_cells.count(q_cell)) {
			  std::cout << "is an optimized cell\n";
			} else {
			  std::cout << "not an optimized cell\n";
			}
			std::cout << "vertex at the lonely extending HC: "
			          << mesh.getVertexIndex(extending_hfcs[0]->getVertex()) << '\n';
			mesh.printTriangleVertexIndices(extending_hfcs[0]->getTri());
			printGridPrimitiveForNewMeshVertex(extending_hfcs[0]->getTri()->getVertex(0));
			printGridPrimitiveForNewMeshVertex(extending_hfcs[0]->getTri()->getVertex(1));
			printGridPrimitiveForNewMeshVertex(extending_hfcs[0]->getTri()->getVertex(2));
			std::cout << "\n////////////////////////////////////////\n";
			int coun = 0;
			for (int n_cell : grid.get_cells_neighboring_cell(q_cell)) {
			  switch (coun) {
			    case 0:
			      std::cout << "cell i-1";
			      break;
			    case 1:
			      std::cout << "cell i+1";
			      break;
			    case 2:
			      std::cout << "cell j-1";
			      break;
			    case 3:
			      std::cout << "cell j+1";
			      break;
			    case 4:
			      std::cout << "cell k-1";
			      break;
			    case 5:
			      std::cout << "cell k+1";
			      break;
			  }

			  for (Mesh3DTriangle* n_tris : cell_to_triangles[n_cell]) {
			    std::cout << ": " << n_cell << '\n';
			    if (optimized_cells.count(n_cell)) {
			      std::cout << "is optimized cell\n";
			    } else {
			      std::cout << "not optimized cell\n";
			    }
			    mesh.printTriangleVertexIndices(n_tris);
			    printGridPrimitiveForNewMeshVertex(n_tris->getVertex(0));
			    printGridPrimitiveForNewMeshVertex(n_tris->getVertex(1));
			    printGridPrimitiveForNewMeshVertex(n_tris->getVertex(2));
			    std::cout << "\n-----" << '\n';
			  }
			  std::cout << "\n////////////////////////////////////////\n";
			}*/

			assert(transition_extending_corners.count(mesh_edge));
			transition_extending_corners[mesh_edge].push_back(extending_hfcs[0]);
		}
		// if an edge has exactly two extending HCs stored, it is a manifold internal edge - a mesh
		// edge shared by exactly two internal triangles; assigning opposite pointers on its
		// extending HCs is straightforward (both extending HCs stored are on the CW side when we
		// project `mesh_edge` onto an orthogonal plane in an orientation preserving way, and have
		// to therefore be connected primal to dual)
		if (extending_hfcs.size() == 2) {
			assert(extending_hfcs.at(0)->getLabel() == extending_hfcs.at(1)->getDual()->getLabel());
			extending_hfcs.at(0)->setOppos(extending_hfcs.at(1)->getDual());
			extending_hfcs.at(1)->getDual()->setOppos(extending_hfcs.at(0));
			assert(extending_hfcs.at(0)->getDual()->getLabel() == extending_hfcs.at(1)->getLabel());
			extending_hfcs.at(0)->getDual()->setOppos(extending_hfcs.at(1));
			extending_hfcs.at(1)->setOppos(extending_hfcs.at(0)->getDual());
		}
		if (extending_hfcs.size() >= 3) {
			assignOppositesAroundNonMfldInternalEdge(grid, mesh, mesh_edge, extending_hfcs);
		}
	}
	// assign opposites across transition edges
	for (auto& [mesh_edge, extending_hfcs] : transition_extending_corners) {
		// transition edge is a mesh edge adjacent to one front triangle and one internal triangle
		// (it has to be manifold by construction)
		assert(extending_hfcs.size() == 2);
		// assigning opposite pointers on its extending HCs is straightforward (both extending HCs
		// stored are on the CW side when we project `mesh_edge` onto an orthogonal plane in an
		// orientation preserving way, and have to therefore be connected primal to dual)
		assert(extending_hfcs.at(0)->getLabel() == extending_hfcs.at(1)->getDual()->getLabel());
		extending_hfcs.at(0)->setOppos(extending_hfcs.at(1)->getDual());
		extending_hfcs.at(1)->getDual()->setOppos(extending_hfcs.at(0));
		assert(extending_hfcs.at(0)->getDual()->getLabel() == extending_hfcs.at(1)->getLabel());
		extending_hfcs.at(0)->getDual()->setOppos(extending_hfcs.at(1));
		extending_hfcs.at(1)->setOppos(extending_hfcs.at(0)->getDual());
	}
}

//------------------------------------------------------------
// functions for testing mesh consistency and algorithm correctness
//------------------------------------------------------------

// performs basic checks to ensure mesh consistency, especially in terms of opposites assignment
void MultiLabelMarchingCuber::consistencyCheck(Mesh3DInterface& mesh, Grid3DInterface& grid) const {
	std::cout << "-marching cubes consistency check start\n";

	// check that HCs with opposites assigned have the same label
	for (Mesh3DTriangle* current_tri : mesh.ListTriangles()) {
		Mesh3DHalfCorner* hfc = current_tri->getHalfCorner();

		if (hfc->getOppos() != nullptr) {
			if (hfc->getLabel() != hfc->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch ";
				assert(false);
			}
		}
		if (hfc->getNext()->getOppos() != nullptr) {
			if (hfc->getNext()->getLabel() != hfc->getNext()->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch\n";
				assert(false);
			}
		}
		if (hfc->getPrev()->getOppos() != nullptr) {
			if (hfc->getPrev()->getLabel() != hfc->getPrev()->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch\n";
				assert(false);
			}
		}

		hfc = hfc->getDual();

		if (hfc->getOppos() != nullptr) {
			if (hfc->getLabel() != hfc->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch\n";
				assert(false);
			}
		}
		if (hfc->getNext()->getOppos() != nullptr) {
			if (hfc->getNext()->getLabel() != hfc->getNext()->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch\n";
				assert(false);
			}
		}
		if (hfc->getPrev()->getOppos() != nullptr) {
			if (hfc->getPrev()->getLabel() != hfc->getPrev()->getOppos()->getLabel()) {
				std::cout << "-ERROR: opposite half-corner label mismatch\n";
				assert(false);
			}
		}
	}

	// check that all HCs associated with the same intrinsic orientation have the same label side
	// (and therefore the same label)
	for (Mesh3DTriangle* current_tri : mesh.ListTriangles()) {
		Mesh3DHalfCorner* hfc = current_tri->getHalfCorner();

		if (hfc->getLabelSide() != hfc->getNext()->getLabelSide()) {
			std::cout << "-ERROR: next/prev half-corner label side mismatch\n";
			assert(false);
		}
		if (hfc->getLabelSide() != hfc->getPrev()->getLabelSide()) {
			std::cout << "-ERROR: next/prev half-corner label side mismatch\n";
			assert(false);
		}

		hfc = hfc->getDual();

		if (hfc->getLabelSide() != hfc->getNext()->getLabelSide()) {
			std::cout << "-ERROR: next/prev half-corner label side mismatch\n";
			assert(false);
		}
		if (hfc->getLabelSide() != hfc->getPrev()->getLabelSide()) {
			std::cout << "-ERROR: next/prev half-corner label side mismatch\n";
			assert(false);
		}
	}

	// check that for each HC with opposite pointer assigned, opposite of opposite is self
	for (Mesh3DTriangle* current_tri : mesh.ListTriangles()) {
		Mesh3DHalfCorner* hfc = current_tri->getHalfCorner();

		if (hfc->getOppos() != nullptr) {
			if (hfc->getOppos()->getOppos() != hfc) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}
		if (hfc->getNext()->getOppos() != nullptr) {
			if (hfc->getNext()->getOppos()->getOppos() != hfc->getNext()) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}
		if (hfc->getPrev()->getOppos() != nullptr) {
			if (hfc->getPrev()->getOppos()->getOppos() != hfc->getPrev()) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}

		hfc = hfc->getDual();

		if (hfc->getOppos() != nullptr) {
			if (hfc->getOppos()->getOppos() != hfc) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}
		if (hfc->getNext()->getOppos() != nullptr) {
			if (hfc->getNext()->getOppos()->getOppos() != hfc->getNext()) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}
		if (hfc->getPrev()->getOppos() != nullptr) {
			if (hfc->getPrev()->getOppos()->getOppos() != hfc->getPrev()) {
				std::cout << "-ERROR: half-corner opposite of opposite is not self\n";
				assert(false);
			}
		}
	}

	std::cout << "-marching cubes consistency check end\n";
}

void MultiLabelMarchingCuber::assignOppositesAroundNonMfldInternalEdge(
    Grid3DInterface& grid, Mesh3DInterface& mesh, std::pair<Mesh3DVertex*, Mesh3DVertex*> edge,
    std::vector<Mesh3DHalfCorner*> extending_hfcs) {
	// ASSERT: check that the edge is non-manifold, i.e. has at least 3 extending HCs, and is an
	// internal edge, therefore has at most 4 extending HCs
	assert(extending_hfcs.size() == 3 || extending_hfcs.size() == 4);

	// for each extending HC, we store the set of HCs that lie to its left, and to its right
	std::vector<std::set<Mesh3DHalfCorner*>> left_neighbors(extending_hfcs.size(),
	                                                        std::set<Mesh3DHalfCorner*>());
	std::vector<std::set<Mesh3DHalfCorner*>> right_neighbors(extending_hfcs.size(),
	                                                         std::set<Mesh3DHalfCorner*>());
	// retrieve coordinates of the edge vertices
	Vec3d edge_v0_coords = edge.first->getCoords();
	Vec3d edge_v1_coords = edge.second->getCoords();

	// iterate over extending HCs of `edge`, iterated extending HC is referred to as base HC; fill
	// in `left_neighbors` and `right_neighbors` sets
	for (size_t base = 0; base < extending_hfcs.size(); ++base) {
		// retrieve coordinates of base HC
		Vec3d base_ext_coords = extending_hfcs.at(base)->getVertex()->getCoords();

		// references for left and right sets of base HC
		std::set<Mesh3DHalfCorner*>&left_of_current_hfc = left_neighbors.at(base),
		&right_of_current_hfc = right_neighbors.at(base);

		// iterate over extending HCs of `edge`, iterated extending HC is refered to as current HC;
		// sort current HCs into left and right sets of base HC
		for (size_t curr = 0; curr < extending_hfcs.size(); ++curr) {
			// skip if base and current HCs are the same
			if (base == curr) {
				continue;
			}

			// retrieve coordinates of current HC
			Vec3d curr_ext_coords = extending_hfcs.at(curr)->getVertex()->getCoords();

			// assign current HC into left or right set of base HC
			if (intersector.orient3d(edge_v0_coords.v, edge_v1_coords.v, base_ext_coords.v,
			                         curr_ext_coords.v) > 0) {
				left_of_current_hfc.insert(extending_hfcs.at(curr));
			} else {
				right_of_current_hfc.insert(extending_hfcs.at(curr));
			}
		}
	}

	// iterate over extending HCs of `edge`, iterated extending HC is referred to as base HC; find
	// opposite HC candidate pairs, and if no error occurs, set their opposite pointers
	for (size_t i = 0; i < extending_hfcs.size(); ++i) {
		Mesh3DHalfCorner* oppos_candidate = nullptr;
		// reference for base HC right set
		std::set<Mesh3DHalfCorner*>& base_right_neighbors = right_neighbors.at(i);

		if (base_right_neighbors.empty()) {
			// if there are no right neighbors of base, find the extending HC with no left neighbors
			// (there should be exactly one)
			for (size_t j = 0; j < extending_hfcs.size(); ++j) {
				if (left_neighbors.at(j).empty()) {
					// found an opposite candidate
					oppos_candidate = extending_hfcs.at(j);
					break;
				}
			}
		} else {
			// if there are some right neighbors of base, iterate over extending HCs of `edge`,
			// iterated extending HC is refered to as current HC; find the current extending HC that
			// is in the right set of base, and the intersection of right set of base and left set of
			// current is empty
			for (size_t j = 0; j < extending_hfcs.size(); ++j) {
				// skip if base == current
				if (i == j) {
					continue;
				}
				if (base_right_neighbors.count(extending_hfcs.at(j))) {
					std::set<Mesh3DHalfCorner*>& curr_left_neighbors = left_neighbors.at(j);
					std::vector<Mesh3DHalfCorner*> intersect_set;
					std::set_intersection(base_right_neighbors.begin(), base_right_neighbors.end(),
					                      curr_left_neighbors.begin(), curr_left_neighbors.end(),
					                      inserter(intersect_set, intersect_set.begin()));
					if (intersect_set.size() == 0) {
						// found an opposite candidate
						oppos_candidate = extending_hfcs.at(j);
						break;
					}
				}
			}
		}
		if (oppos_candidate != nullptr) {
			// assign the opposite pointers of base HC and of dual of opposite candidate; we take dual
			// of the opposite candidate, because we consistently chose to store those extending HCs
			// that are on the same side of triangles with respect to the orientation imposed by
			// following `edge` (namely all extending HC are on the side into which right hand normal
			// points)

			printLocalConfiguration(mesh, edge, extending_hfcs, left_neighbors, right_neighbors,
			                        oppos_candidate, i);
			// ASSERT: neither cuurent HC, nor its opposite candidate should have opposites assigned
			assert(extending_hfcs.at(i)->getOppos() == nullptr);
			assert(oppos_candidate->getDual()->getOppos() == nullptr);
			// ASSERT: make sure the HCs that are to be assigned as each other's opposites have the
			// same label
			assert(extending_hfcs.at(i)->getLabel() == oppos_candidate->getDual()->getLabel());

			extending_hfcs.at(i)->setOppos(oppos_candidate->getDual());
			oppos_candidate->getDual()->setOppos(extending_hfcs.at(i));
		} else {
			// if the HC has no opposite candidate, quit
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: half-corner " << extending_hfcs.at(i)
				          << " has no opposite half-corner, quitting\n";
			}
			assert(false);
		}
	}
}

void MultiLabelMarchingCuber::printLocalConfiguration(
    const Mesh3DInterface& mesh, std::pair<Mesh3DVertex*, Mesh3DVertex*> edge,
    std::vector<Mesh3DHalfCorner*> extending_hfcs,
    std::vector<std::set<Mesh3DHalfCorner*>>& left_neighbors,
    std::vector<std::set<Mesh3DHalfCorner*>>& right_neighbors, Mesh3DHalfCorner* oppos_candidate,
    size_t current_index) {
	// print info if current HC or the opposite candidate already have an opposite assigned
	if (extending_hfcs.at(current_index)->getOppos() != nullptr) {
		std::cout << "WARNING: base HC at vertex: "
		          << mesh.getVertexIndex(extending_hfcs.at(current_index)->getVertex())
		          << " already has an opposite assigned at vertex: "
		          << mesh.getVertexIndex(extending_hfcs.at(current_index)->getOppos()->getVertex())
		          << '\n';
	}
	if (oppos_candidate->getDual()->getOppos() != nullptr) {
		std::cout << "WARNING: oppos candidate HC at vertex: "
		          << mesh.getVertexIndex(oppos_candidate->getDual()->getVertex())
		          << " already has an opposite assigned at vertex: "
		          << mesh.getVertexIndex(oppos_candidate->getDual()->getOppos()->getVertex()) << '\n';
	}

	// print info if current HC and opposite candidate don't match labels
	if (extending_hfcs.at(current_index)->getLabel() != oppos_candidate->getDual()->getLabel()) {
		// print info about current edge
		std::cout << "edge:\n";
		std::cout << "vertex: " << mesh.getVertexIndex(edge.first);
		printGridPrimitiveForNewMeshVertex(edge.first);
		std::cout << " coords: " << edge.first->getCoords();
		std::cout << ", vertex: " << mesh.getVertexIndex(edge.second);
		printGridPrimitiveForNewMeshVertex(edge.second);
		std::cout << " coords: " << edge.second->getCoords();
		std::cout << '\n';

		// print info about extending vertices of current edge
		std::cout << "extending vertices:\n";
		int print_it = 0;
		for (Mesh3DHalfCorner* e_hfc : extending_hfcs) {
			std::cout << "---" << mesh.getVertexIndex(e_hfc->getVertex()) << ": "
			          << e_hfc->getVertex()->getCoords() << ", left:";
			for (Mesh3DHalfCorner* left_hfc : left_neighbors[print_it]) {
				std::cout << " " << mesh.getVertexIndex(left_hfc->getVertex());
			}
			std::cout << ", right:";
			for (Mesh3DHalfCorner* right_hfc : right_neighbors[print_it]) {
				std::cout << " " << mesh.getVertexIndex(right_hfc->getVertex());
			}
			printGridPrimitiveForNewMeshVertex(e_hfc->getVertex());
			std::cout << '\n';
			print_it++;
		}
	}
}

void MultiLabelMarchingCuber::printGridPrimitiveForNewMeshVertex(Mesh3DVertex* vertex) {
	if (cell_verts.count(vertex)) {
		std::cout << " cell: " << cell_verts[vertex];
	} else if (face_verts.count(vertex)) {
		std::cout << " relative face: " << face_verts[vertex];
	} else if (edge_verts.count(vertex)) {
		std::cout << " relative edge: " << edge_verts[vertex].first
		          << " in cell: " << edge_verts[vertex].second;
	}
}

void MultiLabelMarchingCuber::moveVertsToNaiveLocations(Mesh3DInterface& mesh,
                                                        Grid3DInterface& grid) {
	for (auto [vertex, cell_id] : cell_verts) {
		Vec3d coords(0.0);
		for (long long vertex_id : grid.get_verts_neighboring_cell(cell_id)) {
			coords += grid.getVertexPosition(vertex_id);
		}
		optimized_coords_[vertex] = vertex->getCoords();
		vertex->setCoords(coords / 8.0);
	}

	for (auto [vertex, face_id] : face_verts) {
		Vec3d coords(0.0);
		for (long long vertex_id : grid.get_verts_neighboring_face(face_id)) {
			coords += grid.getVertexPosition(vertex_id);
		}
		optimized_coords_[vertex] = vertex->getCoords();
		vertex->setCoords(coords / 4.0);
	}
}

void MultiLabelMarchingCuber::moveVertsToOptimizedLocations(Mesh3DInterface& mesh) {
	for (auto [vertex, coords] : optimized_coords_) {
		vertex->setCoords(coords);
	}
}
