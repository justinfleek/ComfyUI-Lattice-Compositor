/* ComplexCellDetector.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the implementation file for the module that detects complex elements.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "ComplexCellDetector.h"

#include <queue>
#include <unordered_set>

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// function that coordinates the run of the complex cell detector module
int ComplexCellDetector::run(Mesh3DInterface& mesh, Grid3DInterface& grid,
                             GridMeshIntersector& intersector, int orientation) {
	int return_value = 0;

	if (settings->complex_cell_resample_mode ==
	    TopoFixerSettings::ComplexCellResampleMode::ResampleAll) {
		const GridLattice<long long, long long>& sparse_rays = grid.getSparseRays(orientation);
		// iterate over sparse rays
		for (const auto& ray : sparse_rays) {
			for (auto ray_it = ray.second.begin(); ray_it != ray.second.end(); ++ray_it) {
				for (const long long cell_id : grid.get_cells_neighboring_vertex(ray_it->element)) {
					grid.markCellAsComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed);
				}
			}
		}
		if (settings->verbosity >= 2) {
			std::cout << "-marked all cells as complex" << std::endl;
		}

		return return_value;
	}

	markComplexVertices(grid, orientation);
	markComplexEdges(mesh, grid);
	if (settings->run_deep_edge_test) {
		deepEdgeTest(grid);
		if (settings->verbosity >= 3) {
			std::cout << "-number of shallow cells: " << grid.getEdgeShallowCells().size() << '\n';
		}
	}
	// ASSERT: at this point all flexible-complex cells should have been either marked as
	// fixed-complex, or unmarked from being flexible-complex, thus being non-complex
	assert(grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFlexible).empty());

	if (settings->faces_to_check_for_complexity ==
	    TopoFixerSettings::FacesToCheckForComplexity::All) {
		markComplexFaces(mesh, grid, intersector);
	}
	propagateComplexCellFront(mesh, grid, intersector);

	for (long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
		for (long long vert : grid.get_verts_neighboring_cell(ccell)) {
			if (grid.isVertexMarkedComplex(vert)) {
				for (long long ncell : grid.get_cells_neighboring_vertex(vert)) {
					if (!grid.isCellMarkedComplex(ncell, Grid3DInterface::ComplexCellType::kFixed)) {
						std::cout << "-ERROR: complex vertex adjacent to a simple cell\n";
					}
				}
			}
		}
	}

	if (settings->verbosity >= 1) {
		std::cout << "-complex cell detector finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// test all vertices for complexity, using a labeling direction given by `orientation`
void ComplexCellDetector::markComplexVertices(Grid3DInterface& grid, const int orientation) const {
	const GridLattice<long long, long long>& sparse_rays = grid.getSparseRays(orientation);
	Vec3ll ray_direction = sparse_rays.get_ray_direction();
	// iterate over sparse rays
	for (const auto& ray : sparse_rays) {
		auto ray_it = ray.second.begin();
		auto ray_end = ray.second.end();
		// iterate over values (i.e. pairs {grid vertex id, vertex coord on ray}) on current ray,
		// excluding the last entry (this is done to accommodate the function's logic below)
		for (; ray_it + 1 != ray_end; ++ray_it) {
			const long long vert_id = ray_it->element;
			// check whether a vertex on the current ray is complex
			if (isVertexComplex(grid, vert_id)) {
				Vec3ll vertex_coords;
				Vec3ll vertex_coords_end;
				// retrieve grid coordinates of the current vertex
				grid.get_vertex_coords(ray_it->element, vertex_coords[0], vertex_coords[1],
				                       vertex_coords[2]);
				// retrieve grid coordinates of the next vertex on the sparse ray
				grid.get_vertex_coords((ray_it + 1)->element, vertex_coords_end[0], vertex_coords_end[1],
				                       vertex_coords_end[2]);
				// iterate between current vertex and the next vertex on the sparse ray; we never iterate
				// past the last vertex on the sparse ray, meaning any vertex past the last vertex on the
				// sparse ray will not be marked as complex; if our algorithm's input is correct, all such
				// vertices should have the unique label 0, i.e. global outside
				for (; vertex_coords != vertex_coords_end; vertex_coords += ray_direction) {
					// mark vertex whose grid coordinates are equal to `vertex_coords`, as well as all its
					// grid neighbor vertices as fixed complex; in every iteration of this loop after the
					// first one is such vertex not saved on the sparse ray
					grid.markVertexAsComplex(
					    grid.get_vertex_id(vertex_coords[0], vertex_coords[1], vertex_coords[2]));
					for (const long long cell_id : grid.get_cells_neighboring_vertex(
					         vertex_coords[0], vertex_coords[1], vertex_coords[2])) {
						grid.markCellAsComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed);
					}
				}
			}
		}
	}

	if (settings->verbosity >= 2) {
		std::cout << "-mark complex vertices routine finished" << std::endl;
	}
}

// test input grid vertex for complexity
bool ComplexCellDetector::isVertexComplex(Grid3DInterface& grid, const long long vertex_id) const {
	// vertex is topologically complex if at least one of the following holds:
	// -it has a non-unique material vector
	// -it has already been marked complex, such as due to a rollback (in practice there is no
	// functionality currently to cause this to occur)

	if (grid.isVertexMarkedComplex(vertex_id)) {
		return true;
	}
	return findMaterialVectorUniqueEntry(grid.getVertexMaterial(vertex_id)) == -1;
}

// if `material_vector` is unique, returns the index of the unique material, otherwise returns -1
int ComplexCellDetector::findMaterialVectorUniqueEntry(
    const SparseVector<int>& material_vector) const {
	return material_vector.getNNZ() == 1 ? material_vector.getKey(0) : -1;
}

// test edges in cells that are not fixed-complex for complexity
void ComplexCellDetector::markComplexEdges(Mesh3DInterface& mesh, Grid3DInterface& grid) {
	absl::flat_hash_set<long long> is_edge_processed;
	// iterate over cells with triangles
	for (const long long cell_id : grid.getCellsWithTriangles()) {
		// only consider cells that aren't marked as fixed complex (fixed complex cells have to be
		// remeshed, therefore we don't need to test their edges for complexity)
		if (!grid.isCellMarkedComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed)) {
			// iterate over the 12 grid edges adjacent to current cell
			for (const long long edge_id : grid.get_edges_neighboring_cell(cell_id)) {
				// skip edges that were already examined
				auto [it, is_inserted] = is_edge_processed.insert(edge_id);
				if (!is_inserted) {
					continue;
				}
				// perform topological edge complexity test
				if (isEdgeTopologicallyComplex(grid, edge_id)) {
					grid.markEdgeAsTopoComplex(edge_id);
					// perform geometric edge complexity test; if positive, mark edge as geometrically complex
					// and mark all neighboring cells as fixed complex (have to be remeshed); if negative,
					// mark neighboring cells that aren't fixed complex as flexible complex (might become
					// exempt from remeshing during deep edge test); neighbor cells could only have become
					// fixed complex as a result of a nearby edge being geometrically complex, not due to a
					// nearby complex vertex (such edges would be skipped over at the beginning of this
					// function)
					if (isEdgeGeometricallyComplex(mesh, grid, edge_id)) {
						grid.markEdgeAsGeomComplex(edge_id);
						for (const long long cell_id_to_mark : grid.get_cells_neighboring_edge(edge_id)) {
							grid.markCellAsComplex(cell_id_to_mark, Grid3DInterface::ComplexCellType::kFixed);
						}
					} else {
						for (const long long cell_id_to_mark : grid.get_cells_neighboring_edge(edge_id)) {
							if (!grid.isCellMarkedComplex(cell_id_to_mark,
							                              Grid3DInterface::ComplexCellType::kFixed)) {
								grid.markCellAsComplex(cell_id_to_mark,
								                       Grid3DInterface::ComplexCellType::kFlexible);
							}
						}
					}
				}
			}
		}
	}

	if (settings->verbosity >= 2) {
		std::cout << "-mark complex edges routine finished" << std::endl;
	}
}

// test input grid edge for topological complexity
bool ComplexCellDetector::isEdgeTopologicallyComplex(Grid3DInterface& grid,
                                                     const long long edge_id) const {
	// edge is topologically complex if at least one of the following holds:
	// -it intersectes more than one mesh triangle
	// -it has already been marked complex

	return grid.isEdgeMarkedTopoComplex(edge_id) ||
	       grid.get_intersections_on_edge(edge_id).size() > 1;
}

// test input grid edge for geometric complexity based on a complexity metric
bool ComplexCellDetector::isEdgeGeometricallyComplex(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                                     const long long edge_id) {
	// if geometric complexity metric is set to `none`, no edges are considered geometrically complex
	if (settings->edge_geometric_complexity_metric ==
	    TopoFixerSettings::EdgeGeometricComplexityMetric::None) {
		return false;
	}

	// if geometric complexity metric is set to `inversion`, check whether a non-physical state is
	// entered while traversing the input edge (material vector becomes non-unique at any time)
	if (settings->edge_geometric_complexity_metric ==
	    TopoFixerSettings::EdgeGeometricComplexityMetric::Inversion) {
		if (isMaterialFlippedAlongEdge(mesh, grid, edge_id)) {
			return true;
		}
	}

	// if all performed tests were negative, the edge is not geometrically complex, return false
	return false;
}

// returns true if while traversing the input grid edge the material vector ever becomes non-unique
bool ComplexCellDetector::isMaterialFlippedAlongEdge(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                                     const long long edge_id) {
	// retrieve a vector of intersections between the input edge and mesh triangles
	std::vector<GridEdgeMeshFaceIntersection> edge_intersections =
	    grid.get_intersections_on_edge(edge_id);
	long long dummy_i, dummy_j, dummy_k, orientation;
	grid.get_edge_coords(edge_id, dummy_i, dummy_j, dummy_k, orientation);
	// sort the intersections on the input edge
	sort(edge_intersections.begin(), edge_intersections.end(),
	     [orientation](auto& int_1, auto& int_2) {
		     return int_1.getPosition()[orientation] < int_2.getPosition()[orientation];
	     });

	// retrieve one of the two grid vertices adjacent to input edge, namely the one with a smaller
	// vertex id; this is the vertex that is encountered first if we traverse grid rays in the
	// increasing coordinate direction given by `orientation`
	std::vector<long long> edge_verts = grid.get_verts_neighboring_edge(edge_id);
	long long edge_starting_vertex_id = edge_verts[0];
	// retrieve the material vector on the edge starting vertex
	SparseVector<int> material_vector = grid.getVertexMaterial(edge_starting_vertex_id);
	// reduce `material_vector` to the unique label on edge starting vertex
	int starting_label = findMaterialVectorUniqueEntry(material_vector);
	// ASSERT: material vector saved on the edge starting vertex has to be unique (we only investigate
	// edges that are not adjacent to any fixed-complex cells)
	assert(starting_label >= 0);
	// retrieve the other grid vertex adjacent to input edge; we use it to determine whether the
	// labels on the input edge's ends (these must be unique if the algorithm execution arrived here)
	// are separated by at least one other different material as we traverse the input edge; this
	// information forms the basis of the edge bad cell test
	long long edge_ending_vertex_id = edge_verts[1];
	// retrieve the material vector on the edge ending vertex
	SparseVector<int> material_vector_end = grid.getVertexMaterial(edge_ending_vertex_id);
	// reduce `material_vector_end` to the unique label on edge ending vertex
	int ending_label = findMaterialVectorUniqueEntry(material_vector_end);
	// ASSERT: material vector saved on the edge ending vertex has to be unique
	assert(ending_label >= 0);
	// set that stores all labels that correspond to materials that are entered when traversing the
	// input edge, excluding `starting_label` and `ending_label`, i.e. a set of materials that
	// separate the starting and ending vertex labels of input edge
	absl::flat_hash_set<int> current_separating_materials;

	// investigate intersections along the input edge, to see if the material vector is always unique
	for (GridEdgeMeshFaceIntersection intersection : edge_intersections) {
		Mesh3DTriangle* triangle = intersection.getTriangle();
		Vec2i labels = triangle->getLabels();
		// mesh labels have to be converted to grid labels before we can use them to determine how the
		// material vector evolves as we move along a grid edge
		labels = grid.convertMeshLabelsToGridLabels(labels);

		// change the material vector based on the orientation of `triangle` w.r.t. increasing grid edge
		// direction
		if (intersection.isTriNormalEdgeAligned()) {
			// entering into the material on triangle right hand normal side, if this causes
			// `material_vector` to become non-unique, materials are flipped, i.e. a non-physical state
			// was entered, return true
			// Equivalent to:
			// if (material_vector[labels[0]] != 0 || material_vector[labels[1]] != 1) {
			// 	return true;
			// }

			int l0_key = material_vector.find(labels[0]);
			if (l0_key != -1) {
				return true;
			}
			int l1_key = material_vector.find(labels[1]);
			if (l1_key == -1 || material_vector.getValue(l1_key) != 1) {
				return true;
			}
			material_vector.add(labels[0], +1);
			material_vector.add(labels[1], -1);
			// add the material that was just entered into `separating_materials_along_current_edge`
			current_separating_materials.insert(labels[0]);
		} else {
			// exiting from the material on triangle right hand normal side, if this causes
			// `material_vector` to become non-unique, materials are flipped, i.e. a non-physical state
			// was entered, return true
			int l0_key = material_vector.find(labels[0]);
			if (l0_key == -1 || material_vector.getValue(l0_key) != 1) {
				return true;
			}
			int l1_key = material_vector.find(labels[1]);
			if (l1_key != -1) {
				return true;
			}

			material_vector.add(labels[0], -1);
			material_vector.add(labels[1], +1);
			// add the material that was just entered into `separating_materials_along_current_edge`
			current_separating_materials.insert(labels[1]);
		}
	}

	// if the algorithm reaches this line, it means that `material_vector` didn't enter a non-unique
	// state while processing all intersections on the input grid edge, i.e. no materials are flipped,
	// and all states entered are physical

	// remove `starting_label` and `ending_label` from `separating_materials_along_current_edge`,
	// (they might have been added during edge traversal), and store the set in `separating_materials`
	current_separating_materials.erase(starting_label);
	current_separating_materials.erase(ending_label);
	separating_materials[edge_id] = current_separating_materials;
	return false;
}

// perform deep edge test on topologically complex, geometrically non-complex edges
void ComplexCellDetector::deepEdgeTest(Grid3DInterface& grid) {
	// iterate over topologically complex, geometrically simple edges (those that might cause
	// flexible-complex cells to be excluded from remeshing)
	for (long long edge_id : grid.getTopoComplexGeomSimpleEdges()) {
		// check if any cells adjacent to current edge are fixed complex, if yes, skip the current edge,
		// and label all its neighbor cells as fixed complex - we require all edges adjacent to cells
		// that will be remeshed to be topologically simple, so that the mesh generated by marching
		// cubes can be seamlessly connected to the mesh that isn't remeshed
		if (grid.doesEdgeHaveFixedComplexNeighbors(edge_id)) {
			for (long long cell_id_to_mark : grid.get_cells_neighboring_edge(edge_id)) {
				grid.markCellAsComplex(cell_id_to_mark, Grid3DInterface::ComplexCellType::kFixed);
			}
			continue;
		}

		// we want to consider labels on vertices in the neighborhood of the current edge, with size of
		// the neighborhood depending on the `edge_deep_cell_test_depth` parameter in l1 sense:
		// -0: consider labels on vertices of the tested edge (these have already been retrieved),
		// -1: consider labels on vertices in 0, plus labels on vertices on all edges adjacent to 0,
		// -2: consider labels on vertices in 1, plus labels on vertices on all edges adjacent to 1,
		// ... and so on
		int depth = settings->edge_deep_cell_test_depth;

		// calculate the set of `nearby_verts` (those within desired l1 neighborhood of current edge)
		std::vector<long long> initial_verts = grid.get_verts_neighboring_edge(edge_id);
		// initialize `nearby_verts` to endpoints of current edge (distance 0 away from current edge)
		absl::flat_hash_set<long long> nearby_verts(initial_verts.begin(), initial_verts.end());
		// initialize `nearby_edges` to current edge
		absl::flat_hash_set<long long> nearby_edges = {edge_id};
		// for every unit of distance, add adjacent edges and their endpoints
		// We expect depth to be small, so we can afford going through the same edges several times.
		for (int i = 1; i <= depth; ++i) {
			// add edges adjacent to the current set of vertices
			for (long long vertex : nearby_verts) {
				std::vector<long long> vert_edges = grid.get_edges_neighboring_vertex(vertex);
				nearby_edges.insert(vert_edges.begin(), vert_edges.end());
			}
			// add vertices adjacent to the current set of edges
			for (long long edge : nearby_edges) {
				std::vector<long long> edge_verts = grid.get_verts_neighboring_edge(edge);
				nearby_verts.insert(edge_verts.begin(), edge_verts.end());
			}
		}

		// collect labels on `nearby_verts` into the appropriate entry of `nearby_grid_materials`
		// OPEN TO DISCUSS: what to do with vertices with non-unique labels? currently we ignore them
		// with the reasoning that they are to be remeshed, so the information stored on them might be
		// unreliable
		for (long long vert : nearby_verts) {
			int vert_label = findMaterialVectorUniqueEntry(grid.getVertexMaterial(vert));
			if (vert_label != -1) {
				nearby_grid_materials[edge_id].insert(vert_label);
			}
		}

		// iterate over the set of separating materials for the current edge if there exists a
		// separating material not present in the set of nearby materials, then cells adjacent to the
		// current edge are deep, and flagged as fixed complex (must be remeshed); we separately flag
		// them as edge deep for visualization purposes
		bool is_deep = false;
		for (int label : separating_materials[edge_id]) {
			if (nearby_grid_materials[edge_id].count(label) == 0) {
				for (long long cell : grid.get_cells_neighboring_edge(edge_id)) {
					grid.markCellAsComplex(cell, Grid3DInterface::ComplexCellType::kFixed);
					grid.markCellAsEdgeDeep(cell);
				}
				is_deep = true;
				break;
			}
		}
		if (is_deep) {
			continue;
		}

		// arriving here means that all separating materials are present in the set of nearby materials;
		// unmark adjacent cells of current edge from being flexible-complex, therefore excluding them
		// from being remeshed; we separately flag these cells as edge shallow for visualization
		// purposes
		for (long long cell : grid.get_cells_neighboring_edge(edge_id)) {
			// ASSERT: adjacent cells of current edge can only be flexible-complex (by design), or
			// non-complex (if they have been unmarked from being flexible-complex due to being
			// adjacent to another topologically complex edge that was excluded from remeshing)
			assert(!grid.isCellMarkedComplex(cell, Grid3DInterface::ComplexCellType::kFixed));
			grid.unmarkCellAsComplex(cell, Grid3DInterface::ComplexCellType::kFlexible);
			grid.markCellAsEdgeShallow(cell);
		}
	}

	if (settings->verbosity >= 2) {
		std::cout << "-deep edge detection routine finished" << std::endl;
	}
}

// test grid faces for complexity
void ComplexCellDetector::markComplexFaces(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                           GridMeshIntersector& intersector) {
	absl::flat_hash_set<long long> is_face_processed;
	// iterate over cells with triangles
	for (const long long cell_id : grid.getCellsWithTriangles()) {
		// only consider cells that aren't marked as fixed complex (fixed complex cells have to be
		// remeshed, therefore we don't need to test their faces for complexity)
		if (!grid.isCellMarkedComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed)) {
			// iterate over the 6 grid faces adjacent to current cell
			for (const long long face_id : grid.get_faces_neighboring_cell(cell_id)) {
				// skip faces that were already examined
				if (is_face_processed.count(face_id) > 0) {
					continue;
				}
				is_face_processed.insert(face_id);

				// retrieve the two (generic case) or one (border case) cells adjacent to current grid face
				std::vector<long long> cell_ids = grid.get_cells_neighboring_face(face_id);
				// if the face is on the boundary of the grid, skip it - it can't be complex, because the
				// grid was chosen so that it fully covers the mesh+reserve
				if (cell_ids.size() == 1) {
					continue;
				}

				// perform topological face complexity test
				// if the face is topologically complex, mark it on the grid as such, and mark its
				// adjacent cells as fixed-complex; if the face is topologically suspicious, mark it on
				// the grid as such, but don't mark the neighboring cells as complex
				int topo_test_result = isFaceTopologicallyComplex(mesh, grid, intersector, face_id);
				if (topo_test_result == 0) {
					grid.markFaceAsTopoSimple(face_id);
				} else if (topo_test_result == 1) {
					grid.markFaceAsTopoComplex(face_id);
					for (const long long cell_id_to_mark : grid.get_cells_neighboring_face(face_id)) {
						grid.markCellAsComplex(cell_id_to_mark, Grid3DInterface::ComplexCellType::kFixed);
					}
				} else if (topo_test_result == 2) {
					grid.markFaceAsTopoSuspicious(face_id);
				}
				// TODO: in the future, we could implement a face geometric complexity test, if we do, we
				// should follow the logic in the analogous test for edges - a geometrically complex face
				// should have its adjacent cells labeled fixed-complex, a geometrically non-complex face
				// should have its adjacent cells that are not fixed-complex labeled flexible-complex, and
				// examined with a deep face test.
			}
		}
	}

	if (settings->verbosity >= 2) {
		std::cout << "-mark complex faces routine finished" << std::endl;
	}
}

// test input grid face for topological complexity (either containing a cycle in its face graph)
int ComplexCellDetector::isFaceTopologicallyComplex(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                                    GridMeshIntersector& intersector,
                                                    long long face_id) {
	// possible return values:
	// -0: grid face is not topologically complex
	// -1: grid face is topologically complex
	// -2: an inconsistency came up during the test; face should be treated as complex
	int return_value = 0;

	// if the face is already marked topologically simple, complex or suspicious, return
	if (grid.isFaceMarkedTopoSimple(face_id)) {
		return 0;
	}
	if (grid.isFaceMarkedTopoComplex(face_id)) {
		return 1;
	}
	if (grid.isFaceMarkedTopoSuspicious(face_id)) {
		return 2;
	}

	// we call mesh triangle-grid edge intersection Type 1 intersection
	// we call mesh edge-grid face intersection Type 2 intersection

	// there are 3 non-degenerate configurations how a mesh triangle can intersect a grid face:
	// a) 0 triangle edges intersect the grid face, triangle intersects 2 grid edges
	// b) 1 triangle edge intersects the grid face, triangle intersects 1 grid edge
	// c) 2 triangle edges intersect the grid face, triangle intersects 0 grid edges

	// a triangle taking part in configuration a) constructs its own component in the grid face
	// graph, we could count the number of such components by enumerating Type 1 intersections that
	// are stored on grid edges (thus no new intersections need to be computed); additionally,
	// determining configuration a) triangles could only ever lead to labeling a face topologically
	// complex if at least one of the grid edges adjacent to the grid face is also topologically
	// complex; therefore, all we need to do regarding configuration a) triangles is to check the
	// adjacent grid edges for topological complexity

	// configurations b) and c) form a graph on the grid face, with triangles in configuration b)
	// representing "end edges" of the graph (one of its vertices has degree 1), and triangles in
	// configuration c) representing "internal edges" of the graph (both vertices having degree 2 or
	// more); the face is topologically non-complex iff one of the following two conditions is
	// satisfied:
	// 1. the graph is a tree,
	// 2. the graph consists of exactly two components, each of which is a path;
	// it is not necessary to check for the condition 2 separately, since assuming that the four
	// edges surrounding the grid face are all topologically non-complex, the only way how condition
	// 2 could be violated, is if there exists a cycle in the face graph;

	// our strategy to check the topological complexity of the face will therefore be to
	// incrementally construct each component of the face graph and after adding a new edge,
	// checking whether a cycle was formed - if yes, the sets the return value to 1 (face is
	// topologically complex); if no cycle is formed once all the components of the graph are fully
	// constructed, the function returns 0 (face is topologically non-complex);

	// cast all triangles that could intersect the face into a queue; in theory it is enough to pick
	// triangles from one of the neighbor cells of the current face, so this is used if
	// "complex_face_test" parameter is set to "quick_reject"; if it is set to "thorough", both
	// neighbor cells are checked (TODO)
	absl::flat_hash_set<Mesh3DTriangle*> intersection_candidates;
	long long cell_i_coord, cell_j_coord, cell_k_coord;
	grid.get_cell_coords(grid.get_cells_neighboring_face(face_id)[0], cell_i_coord, cell_j_coord,
	                     cell_k_coord);
	if (grid.cell_out_of_bounds(cell_i_coord, cell_j_coord, cell_k_coord)) {
		intersection_candidates =
		    grid.get_cell_triangles_set(grid.get_cells_neighboring_face(face_id)[1]);
	} else {
		intersection_candidates =
		    grid.get_cell_triangles_set(grid.get_cells_neighboring_face(face_id)[0]);
	}

	// if there are no triangles that could intersect the grid face, it can't be complex, return 0
	if (intersection_candidates.empty()) {
		if (settings->verbosity >= 3) {
			std::cout << "-no intersection candidates on face: " << face_id << ", quitting\n ";
		}
		return 0;
	}

	// iterate over grid edges adjacent to the grid face; this has two purposes:
	// -we determine whether any of the edges are topologically complex; if yes, the grid face
	// itself has to be topologically complex -we find the end edges of the face graph (triangles in
	// configuration b)) by determining the number of type 1 intersections; we get the number of
	// triangles in configuration a) for free, which we can use for a correctness check
	absl::flat_hash_map<Mesh3DTriangle*, long long> type_1_counter;
	std::vector<long long> grid_face_edges = grid.get_edges_neighboring_face(face_id);
	// iterate over the four grid edges of a grid face
	for (int it = 0; it < 4; ++it) {
		// check adjacent edges for topological complexity
		if (grid.isEdgeMarkedTopoComplex(grid_face_edges[it])) {
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
				return 1;
			}
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
				return_value = 1;
				// OPTIONAL TODO: compute the intersections of configuration a) triangles with the face
				// for the purpose of visualization
				break;
			}
		}
		// count the number of type 1 intersections, namely for each intersection on a grid edge,
		// increase a counter associated with the intersecting mesh triangle
		for (auto& intersection : grid.get_intersections_on_edge(grid_face_edges[it])) {
			type_1_counter[intersection.getTriangle()] += 1;
		}
	}

	// stores triangles in configuration b), i.e. those, whose intersection with a grid face forms
	// an end edge; these will be used as starting points for constructing face graph components
	std::vector<Mesh3DTriangle*> end_edges;
	// check the number of triangles involved in type 1 intersections (configurations (a) and b))
	int conf_a_count = 0;
	int conf_b_count = 0;
	int error_conf_count = 0;
	for (auto& [key, val] : type_1_counter) {
		if (val == 1) {
			conf_b_count++;
			end_edges.push_back(key);
		}
		if (val == 2) {
			conf_a_count++;
		}
		if (val > 2) {
			error_conf_count++;
		}
	}

	if (settings->verbosity >= 3) {
		std::cout << "number of type 1 intersection configurations:\n";
		std::cout << "configuration a) triangles: " << conf_a_count << '\n';
		std::cout << "configuration b) triangles: " << conf_b_count << '\n';
		std::cout << "error configuration count: " << error_conf_count << '\n';
	}

	// a state where a mesh triangle intersects more than 2 edges of the grid face is inconsistent,
	// most likely an error has occcured, therefore the current face is labeled as complex
	if (error_conf_count > 0) {
		if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
			return 2;
		}
		if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
			return_value = 2;
		}
	}
	// if there are more than two configuration a) triangles, the face can't be topologically
	// non-complex; this should have been detected when checking adjacent grid edges for topological
	// complexity, if it wasn't (i.e. if the return_value is still set to 0), then we arrived in an
	// inconsistent state, and the current face is labeled as complex
	if (conf_a_count > 2 && return_value == 0) {
		if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
			return 2;
		}
		if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
			return_value = 2;
		}
	}

	// stores triangles to be be examined for intersection with the grid face
	std::deque<Mesh3DTriangle*> triangle_queue;
	// add configuration b) triangles to the queue; these serve as starting points for constructing
	// graph components containing configuration b) triangles
	triangle_queue = std::deque<Mesh3DTriangle*>(end_edges.begin(), end_edges.end());

	// add the remaining intersection candidates to `triangle_queue` (those in configuration c), and
	// those that don't intersect the grid face at all)
	for (Mesh3DTriangle* triangle : intersection_candidates) {
		if (type_1_counter.count(triangle) == 0) {
			triangle_queue.push_back(triangle);
		}
	}
	// alternatively, we could add all intersection candidates into `triangle_queue`; these would
	// include configuration b) triangles already in the queue (they will be skipped when they are
	// encountered for the second time); this way we would still ensure that all components
	// containing configuration b) triangles will be constructed before any components containing
	// only configuration c) triangles
	/*triangle_queue.insert(triangle_queue.end(), intersection_candidates.begin(),
	                          intersection_candidates.end());*/

	// keeps triangles that were already added to the face graph during construction of a face graph
	// component; whenever we add a new edge to a face graph, we add its constituting triangle to
	// `visited_mesh_triangles`; once a graph component is fully constructed, we need to check
	// whether there exist more graph components, and during this process we can use the collection
	// of triangles in `visited_mesh_triangles` to make sure we don't start constructing the same
	// component we already constructed
	absl::flat_hash_set<Mesh3DTriangle*> visited_mesh_triangles;

	// number of graph components constructed
	int num_graph_components = 0;

	// retrieve the two triangles that constitute the grid face, these are used by the intersector
	std::vector<Vec3ll> grid_face_triangles = grid.get_face_triangles(face_id);

	// stores the face graph edges as pairs of world coordinate triples for visualization
	std::vector<std::pair<Vec3d, Vec3d>> face_graph;

	// helper variables that store the coordiates of an intersection point on the mesh edge that is
	// currently being processed, it's barycentric coordinate, a flag noting whether a cycle in the
	// face graph was found, and a flag determining whether a cycle should be expected to appear in
	// the face graph; the last one is triggered when a graph component is without configuration b)
	// triangles is detected, if no cycle is subsequently found, an inconsistency is detected
	Vec3d int_point;
	double bary_coord;
	bool cycle_found = false;
	bool expect_cycle = false;

	// loop only finishes once all triangles in the queue have been visited
	while (!triangle_queue.empty()) {
		// pop the front element of the queue
		Mesh3DTriangle* triangle = triangle_queue.front();
		triangle_queue.pop_front();

		// if the triangle has already been visited, it is included in a graph component that was
		// already constructed; skip to the next triangle
		if (visited_mesh_triangles.count(triangle)) {
			continue;
		}
		// mark the current triangle as visited
		visited_mesh_triangles.insert(triangle);

		// retrieve the mesh triangle vertices
		std::vector<Mesh3DVertex*> mesh_triangle_verts = triangle->getVerts();

		// counts number of triangle mesh edges that intersect the grid face; one intersection means
		// that `triangle` is in configuration b), two intersections mean that `triangle` is in
		// configuration c)
		int num_intersecting_edges = 0;

		// a queue facilitating breadth-first graph construction on the grid face, an entry consists of
		// a half-corner H and a grid face-mesh edge intersection I; each half-corner uniquely
		// determines a mesh edge, namely the mesh edge that is opposite to the vertex of the
		// half-corner, we therefore use half-corner H to represent a mesh edge intersecting the grid
		// face; each intersection of a mesh edge with the grid face corresponds to a vertex in the face
		// graph, we store this intersection I and within it the coordinates of the intersection point
		std::deque<std::pair<Mesh3DHalfCorner*, GridFaceMeshEdgeIntersection>> mesh_edge_queue;

		// check for intersections between the grid face and the three mesh edges of the triangle; if
		// at least one intersection is found, add exactly one of the intersecting mesh edges into
		// `mesh_edge_queue` - the reason we only add one mesh edge even if there can be up to two
		// that intersect the grid face is that the face graph construction procedure is written in
		// such a way, that initially adding two mesh edges into `mesh_edge_queue` would be seen as
		// constructing a face graph component from two starting points, which would break the
		// procedure's consistency; instead, the potentially ignored intersection will be visited
		// later during the component's construction

		for (size_t vert_id = 0; vert_id < mesh_triangle_verts.size(); ++vert_id) {
			// permutate vertices of `triangle`
			Mesh3DVertex* mesh_tri_v0 = mesh_triangle_verts[vert_id];
			Mesh3DVertex* mesh_tri_v1 = mesh_triangle_verts[(vert_id + 1) % mesh_triangle_verts.size()];
			Mesh3DVertex* mesh_tri_v2 = mesh_triangle_verts[(vert_id + 2) % mesh_triangle_verts.size()];

			// do the intersection test
			if (intersector.intersect_mesh_edge_with_grid_face_triangles_int_priorities(
			        grid, grid_face_triangles, mesh, mesh_tri_v0, mesh_tri_v1, int_point, bary_coord)) {
				num_intersecting_edges++;
				if (num_intersecting_edges == 1) {
					// push the `GridFaceMeshEdgeIntersection` into `mesh_edge_queue`; we perform an
					// optimization via reusing variables in the following way: we make sure that
					// `mesh_tri_v0`, which will be saved as `first` in the intersection object, is the mesh
					// edge vertex that lies in the grid cell with the larger grid coordinates (in product
					// order sense), and that the `is_first_inside` flag is set to true; at the same time we
					// make sure that `mesh_tri_v1`, which will be saved as `second` in the intersection
					// object, is the mesh edge vertex that lies in the grid cell with the smaller grid
					// coordinates and that the `is_second_inside` flag is set to false; the `is_first_inside`
					// and `is_second_inside` flags at this point have nothing to do with being inside or
					// outside a specific region; instead, saving them in the described way allows us later to
					// trivially determine which side of the input face do mesh edge vertices lie on as we
					// intersect the input grid face with mesh edges during the iterative face graph
					// construction; later, in cell separator, we will look at front faces, and will use the
					// intersection flags to store which of the two mesh edge vertices lies inside the complex
					// region, and which lies outside of it; given the way we stored `first` and `second`
					// vertices, and `is_first_inside` and `is_second_inside` flags, we will be able to do
					// this by simply checking whether the complex cell adjacent to the front face has larger
					// grid coordinates than the adjacent non-complex cell (do nothing), or the other way
					// around (flip the flag values); this adjustment is performed in function
					// `CellSeparator::addIntersectionToMeshEdge`
					// TODO: the information obtained by the orientation test below is already calculated
					// within the intersection test, we could retrieve it from there
					if (intersector.orient_mesh_vertex_against_grid_face_triangle(
					        grid, grid_face_triangles[0], mesh, mesh_tri_v0) < 0) {
						std::swap(mesh_tri_v0, mesh_tri_v1);
						bary_coord = 1.0 - bary_coord;
					}
					// push the half-corner opposite to the intersecting mesh, and the associated intersection
					// object into `mesh_edge_queue`
					mesh_edge_queue.push_back({triangle->getHalfCornerAtVertex(mesh_tri_v2),
					                           {face_id, mesh_tri_v0,
					                            /*is_first_inside=*/true, mesh_tri_v1,
					                            /*is_second_inside=*/false, bary_coord, nullptr}});
				}
			}
		}

		// in a non-degenerate configuration, no more than 2 mesh triangle edges can intersect the
		// grid face, therefore if all three do, an inconsistency is detected, and the current face is
		// labeled as complex
		if (num_intersecting_edges == 3) {
			if (settings->verbosity >= 3) {
				std::cout << "-WARNING: three edges of a triangle interssect grid face: " << face_id
				          << ", this could be a degenerate configuration\n";
			}
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
				return 2;
			}
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
				return_value = 2;
			}
		}

		// `triangle_queue` has configuration b) triangles before any configuration c) triangles,
		// therefore if the first vertex of a new face graph component comes from the intersection of
		// the grid face with a configuration c) triangle (determined by there being two edges of the
		// triangle that intersect the grid face), this component can't contain a configuration b)
		// triangle, and has to therefore contain a cycle (assuming consistency); if "quick_reject" is
		// chosen, the face is labeled complex, if "thorough" is chosen, a flag is set to expect a
		// cycle in the face graph; if that cycle isn't found, an inconsistency is detected
		if (num_intersecting_edges == 2) {
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
				return 1;
			}
			if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
				expect_cycle = true;
			}
		}

		// if at least one of the triangle edges intersects the grid face, we start constructing a
		// face graph component
		if (num_intersecting_edges > 0) {
			num_graph_components++;

			// if there are more than 2 graph components the face must be complex
			if (num_graph_components > 2) {
				if (settings->verbosity >= 3) {
					std::cout << "-found third graph componenet on face: " << face_id << '\n';
				}
				// in "quick_reject" mode, quit the test, face is marked topologically complex
				if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
					if (num_intersecting_edges == 2) {
						// `triangle` should be in configuration c), if so, return 1 (face is topologically
						// complex)
						return 1;
					} else if (num_intersecting_edges == 1) {
						// if `triangle` is in configuration b), an inconsistency is detected, return 2
						return 2;
					}
				}
				// in "thorough" mode, mark the face as topologically complex
				if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
					if (num_intersecting_edges == 2) {
						// `triangle` should be in configuration c), if so, return 1 (face is topologically
						// complex)
						return_value = 1;
					} else if (num_intersecting_edges == 1) {
						// if `triangle` is in configuration b), an inconsistency is detected, return 2
						return_value = 2;
					}
				}
			}

			// stores mesh edges that we visited during construction of the current graph component; if
			// the same edge is visited twice, there is a cycle in the graph, thus the face is complex;
			// here we represent mesh edges as pairs of vertices, because the purpose of this set is to
			// query which mesh edges have already been visited, and since the mapping of (pairs of
			// dual) HCs to mesh edges is non-injective (as a result of edges being generally
			// non-manifold), just comparing HCs, many of which can map to the same mesh edge, wouldn't
			// answer our queries reliably
			absl::flat_hash_set<std::pair<Mesh3DVertex*, Mesh3DVertex*>> visited_mesh_edges;

			// graph component construction ends once `mesh_edge_queue` is empty
			while (!mesh_edge_queue.empty()) {
				// pop the front element of the queue
				Mesh3DHalfCorner* mesh_edge = mesh_edge_queue.front().first;
				GridFaceMeshEdgeIntersection intersection = mesh_edge_queue.front().second;
				mesh_edge_queue.pop_front();

				// if this mesh edge has already been visited (we need to check both permutations of edge
				// vertices), a cycle in the face graph was found, thus the face is be topologically
				// complex
				Mesh3DVertex* edge_v0 = intersection.getEdgeFirst();
				Mesh3DVertex* edge_v1 = intersection.getEdgeSecond();
				if (visited_mesh_edges.count({edge_v0, edge_v1}) ||
				    visited_mesh_edges.count({edge_v1, edge_v0})) {
					cycle_found = true;
					if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
						return 1;
					} else if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
						return_value = 1;
						continue;
					}
				}

				// mark the current mesh edge as visited
				visited_mesh_edges.insert({edge_v0, edge_v1});

				// save the `GridFaceMeshEdgeIntersection` on the grid
				grid.add_mesh_edge_intersection_to_grid_face(face_id, intersection);

				// retrieve one extending HC per triangle (except for `triangle`) adjacent to `mesh_edge`
				std::vector<Mesh3DHalfCorner*> edge_adjacent_triangles;
				mesh.walkAroundEdge(mesh_edge, edge_adjacent_triangles, false);

				// each extending HC of `mesh_edge` has two mesh edges adjacent to it - these mesh edges
				// have one of their ends at `mesh_edge`, and the other end at the extending HC; we use
				// these two edges to facilitate the breadth-first grid face graph construction - at most
				// one of them can intersect the grid face, and if it does, we add it to
				// `mesh_edge_queue`; this means we are adding to `mesh_edge_queue` the edges of the mesh
				// triangles that are adjacent to `mesh_edge` (without adding `mesh_edge` and without
				// adding edges in `triangle`), which also intersect the grid face; in this way we
				// iteratively construct the grid face graph component
				for (Mesh3DHalfCorner* hfc : edge_adjacent_triangles) {
					// add the triangle of `hfc` to `visited_mesh_triangles`
					Mesh3DTriangle* visited_tri = hfc->getTri();
					visited_mesh_triangles.insert(visited_tri);
					int num_intersecting_edges = 0;
					Mesh3DVertex* non_edge_vertex = hfc->getVertex();
					// Go through candidate edges.
					if (intersector.intersect_mesh_edge_with_grid_face_triangles_int_priorities(
					        grid, grid_face_triangles, mesh, edge_v0, non_edge_vertex, int_point,
					        bary_coord)) {
						num_intersecting_edges++;
						// add the intersecting mesh edge to the queue for graph construction
						mesh_edge_queue.push_back({visited_tri->getHalfCornerAtVertex(edge_v1),
						                           {face_id, edge_v0,
						                            /*is_first_inside=*/true, non_edge_vertex,
						                            /*is_second_inside=*/false, bary_coord, nullptr}});
						// add the face graph edge to a set, in order to later visualize it
						face_graph.emplace_back(intersection.getPosition(), int_point);
					}
					if (intersector.intersect_mesh_edge_with_grid_face_triangles_int_priorities(
					        grid, grid_face_triangles, mesh, non_edge_vertex, edge_v1, int_point,
					        bary_coord)) {
						num_intersecting_edges++;
						// add the intersecting mesh edge to the queue for graph construction
						mesh_edge_queue.push_back({visited_tri->getHalfCornerAtVertex(edge_v0),
						                           {face_id, non_edge_vertex,
						                            /*is_first_inside=*/true, edge_v1,
						                            /*is_second_inside=*/false, bary_coord, nullptr}});
						// add the face graph edge to a set, in order to later visualize it
						face_graph.emplace_back(intersection.getPosition(), int_point);
					}

					// test value of `num_intersecting_edges`:
					// -there should never be 2 intersections
					// -there should be 1 intersection, if triangle of `hfc` is in configuration c)
					// -there should be 0 intersection, if triangle of `hfc` is in configuration b)

					// in a non-degenerate configuration, no more than 2 mesh triangle edges can intersect
					// the grid	face, therefore if all three do, an inconsistency is detected
					if (num_intersecting_edges == 2) {
						if (settings->verbosity >= 2) {
							std::cout << "-WARNING: three edges of a triangle intersect grid face: " << face_id
							          << ", this could be a degenerate configuration\n";
						}
						if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
							return 2;
						}
						if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
							return_value = 2;
						}
					}
					// if one intersection was detected (meaning that two edges of `triangle` intersect the
					// grid face, the other being `mesh_edge`), `triangle` should be in configuration c),
					// and therefore not present in `type_1_counter`; if this is not the case, an
					// inconsistency is detected
					if (num_intersecting_edges == 1 && type_1_counter.count(hfc->getTri())) {
						if (settings->verbosity >= 2) {
							std::cout << "-WARNING: 2 triangle edges intersect grid face: " << face_id
							          << ", which indicates that "
							             "the triangle is in configuration c), however, the triangle is also "
							             "involved "
							             "in type 1 intersection (therefore should be in configuration a) or "
							             "b); this "
							             "could be a degenerate configuration\n";
						}
						if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
							return 2;
						}
						if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
							return_value = 2;
						}
					}
					// if no intersections were detected (meaning that one edges of `triangle` intersects
					// the grid face, namely `mesh_edge`), `triangle` should be in configuration b), and
					// therefore present in `type_1_counter` with value 1; if this is not the case, an
					// inconsistency is detected
					if (num_intersecting_edges == 0) {
						if (!type_1_counter.count(hfc->getTri())) {
							if (settings->verbosity >= 2) {
								std::cout << "-WARNING: 1 triangle edge intersects grid face: " << face_id
								          << ", which indicates that "
								             "the triangle is in configuration b), however, it is not involved in "
								             "any type 1 intersections; this could be a degenerate configuration\n";
							}
							if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
								return 2;
							}
							if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
								return_value = 2;
							}
						} else if (type_1_counter.count(hfc->getTri()) && type_1_counter[hfc->getTri()] == 2) {
							if (settings->verbosity >= 2) {
								std::cout << "-WARNING: 1 triangle edge intersects grid face: " << face_id
								          << ", which indicates that "
								             "the triangle is in configuration b), however, it is involved in 2 "
								             "type 2 intersections; this could be a degenerate configuration\n";
							}
							if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::QuickReject) {
								return 2;
							}
							if (settings->complex_face_test == TopoFixerSettings::ComplexFaceTest::Thorough) {
								return_value = 2;
							}
						}
					}
				}
			}
		}

		// If there are no mesh edge intersections but the triangle is in configuration b), then it
		// is a degenerate case, return inconsistency result.
		if (num_intersecting_edges == 0) {
			long long t1_count = 0;
			auto it = type_1_counter.find(triangle);
			if (it != type_1_counter.end()) {
				t1_count = it->second;
			}
			if (t1_count == 1) {
				if (settings->verbosity >= 2) {
					std::cout << "-WARNING: 1 triangle edge intersects grid face: " << face_id
					          << ", which indicates that "
					             "the triangle is in configuration b), however, it is involved in no "
					             "type 2 intersections; this could be a degenerate configuration\n";
				}
				return 2;
			}
		}
	}

	// if the face graph is non-empty, add it to `all_face_graphs`, and the face id to `graph_faces`
	if (!face_graph.empty()) {
		long long face_i_coord, face_j_coord, face_k_coord, face_orient;
		grid.get_face_coords(face_id, face_i_coord, face_j_coord, face_k_coord, face_orient);

		// ASSERT: face should never be outside of the grid
		assert(!grid.face_out_of_bounds(face_i_coord, face_j_coord, face_k_coord, face_orient) &&
		       "-Error: face out of bounds!");

		all_face_graphs[face_id] = face_graph;
	}

	// if a cycle is expected in the face graph (the construction of a graph component started with
	// a configuration c) triangle), but a cycle was not detected, an inconsistency is detected
	if (expect_cycle && !cycle_found) {
		return_value = 2;
	}

	// return values:
	// -0: if the face is determined to be non-complex
	// -1: if the face is determined to complex
	// -2: if an inconsistency was detected; the face should be added to the complex region and
	// remeshed
	return return_value;
}

// test input grid face for geometric complexity based on a complexity metric
bool ComplexCellDetector::isFaceGeometricallyComplex(const long long face_id) const {
	// if no geometric complexity metric is chosen, only topological complexity determines face
	// complexity
	if (settings->face_geometric_complexity_metric ==
	    TopoFixerSettings::FaceGeometricComplexityMetric::None) {
		return 1;
	}

	// Not implemented.
	return 0;
}

// enlarge the complex cell region until all edges and cells on its boundary are topologically
// simple
void ComplexCellDetector::propagateComplexCellFront(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                                    GridMeshIntersector& intersector) {
	// queue of face ids to check for complexity
	std::deque<long long> faces_to_check;

	// fill in the queue with front faces (faces in the interface between complex and non-complex
	// regions)
	std::vector<long long> front_faces = grid.getFrontFacesVector();
	if (front_faces.empty()) {
		// if there are no faces to check (complex cell region is empty), return
		if (settings->verbosity >= 2) {
			std::cout << "-empty complex cell region, propagation trivially ended" << std::endl;
		}
		return;
	}
	faces_to_check = std::deque<long long>(front_faces.begin(), front_faces.end());

	// helper variables
	long long face_id;
	std::vector<long long> adjacent_cells;

	// counters for the frequency of events, used for debugging
	int num_checked_faces = 0;
	int num_skipped_faces = 0;
	int num_topo_complex_faces = 0;
	int num_topo_suspicious_faces = 0;

	// investigate grid faces in the queue
	while (!faces_to_check.empty()) {
		num_checked_faces++;
		// pop the front element of the queue
		face_id = faces_to_check.front();
		faces_to_check.pop_front();
		// retrieve the two (generic case) or one (border case) cells adjacent to current grid face
		adjacent_cells = grid.get_cells_neighboring_face(face_id);

		// if the face is on the boundary of the grid, skip it - we can't propagate the complex cell
		// region outside of the gridthe it can't be complex, because the grid was chosen so that it
		// fully covers the mesh+reserve
		if (adjacent_cells.size() == 1) {
			// ASSERT: faces on grid boundary cannot be complex
			assert(!isFaceTopologicallyComplex(mesh, grid, intersector, face_id));
			num_skipped_faces++;
			continue;
		}

		// if the face is between two complex cells, skip it; this can happen as grid faces are added to
		// `faces_to_check` queue when extending the complex cell region
		if (grid.isCellMarkedComplex(adjacent_cells[0], Grid3DInterface::ComplexCellType::kFixed) &&
		    grid.isCellMarkedComplex(adjacent_cells[1], Grid3DInterface::ComplexCellType::kFixed)) {
			num_skipped_faces++;
			continue;
		}

		// if any edge of current face is topologically complex, add all cells adjacent to this edge to
		// the complex cell region - these cells have to be remeshed, otherwise we wouldn't be able to
		// connect mesh triangles that don't get remeshed to triangles generated by marching cubes; then
		// skip to the next face in `faces_to_check`
		bool face_has_topo_complex_edges = false;
		for (long long edge_id : grid.get_edges_neighboring_face(face_id)) {
			if (isEdgeTopologicallyComplex(grid, edge_id)) {
				for (long long cell_id : grid.get_cells_neighboring_edge(edge_id)) {
					grid.markCellAsComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed);
					std::vector<long long> faces_neighboring_cell = grid.get_faces_neighboring_cell(cell_id);
					std::move(begin(faces_neighboring_cell), end(faces_neighboring_cell),
					          back_inserter(faces_to_check));
				}
				face_has_topo_complex_edges = true;
			}
		}
		if (face_has_topo_complex_edges) {
			continue;
		}

		// perform the face topological complexity check
		int topo_test_result = isFaceTopologicallyComplex(mesh, grid, intersector, face_id);
		if (topo_test_result == 0) {
			grid.markFaceAsTopoSimple(face_id);
		} else if (topo_test_result == 1) {
			grid.markFaceAsTopoComplex(face_id);
			num_topo_complex_faces++;
		} else if (topo_test_result == 2) {
			grid.markFaceAsTopoSuspicious(face_id);
			num_topo_suspicious_faces++;
		}

		if (topo_test_result > 0) {
			// mark the non-complex cell adjacent to current face (there is exactly one) as fixed-complex
			// and add all its faces to `faces_to_check` queue - the current face is thus added as well,
			// but will be skipped when popped from the queue next time
			for (long long cell_id : adjacent_cells) {
				if (!grid.isCellMarkedComplex(cell_id, Grid3DInterface::ComplexCellType::kBoth)) {
					grid.markCellAsComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed);
					std::vector<long long> faces_neighboring_cell = grid.get_faces_neighboring_cell(cell_id);
					std::move(begin(faces_neighboring_cell), end(faces_neighboring_cell),
					          back_inserter(faces_to_check));
				}
			}
		}
	}

	if (settings->verbosity >= 2) {
		std::cout << "-propagate complex cell front routine finished" << std::endl;
	}

	if (settings->verbosity >= 3) {
		std::cout << "-some statistics:\n";
		std::cout << "---checked faces: " << num_checked_faces << '\n';
		std::cout << "---skipped faces: " << num_skipped_faces << '\n';
		std::cout << "---topologically complex faces encountered: " << num_topo_complex_faces << '\n';
		std::cout << "---topologically suspicious faces encountered: " << num_topo_complex_faces
		          << '\n';
	}
}