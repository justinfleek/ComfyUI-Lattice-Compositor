/* LabelResolver.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2023
 *
 * This is the implementation file for the module that resolves a material vector on each grid
 * vertex into a single material label.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "LabelResolver.h"

#include <queue>

#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// coordinating functions
//------------------------------------------------------------

// function that coordinates the run of the label resolver module
int LabelResolver::run(Mesh3DInterface& mesh, Grid3DInterface& grid,
                       GridMeshIntersector& intersector_, int orientation) {
	int return_value = 0;

	// retrieve the map that to a grid vertex in the complex region assigns a unique material label;
	// this map is saved on the grid, and will be used again by the marching cubes algorithm; the goal
	// of this module is to fill this map with data
	absl::flat_hash_map<long long, int>& unique_labeling = grid.getUniqueLabelingMap();

	// BFS preprocess, collect simple vertices in the complex region in a queue
	std::deque<long long> vertices_to_process = preprocessMaterialFloodFill(grid, unique_labeling);

	// perform label resolution based on the input parameter "grid_vertex_resolution_method"
	if (settings->grid_vertex_resolution_method ==
	    TopoFixerSettings::GridVertexResolutionMethod::NaiveBFS) {
		// make labels on complex grid vertices unique via a naive BFS flood fill
		generateUniqueLabelsOnGridVerticesNaiveFloodFill(grid, vertices_to_process, unique_labeling);
	}
	if (settings->grid_vertex_resolution_method ==
	    TopoFixerSettings::GridVertexResolutionMethod::PathTracingBFS) {
		// determine path tracing method based on input parameter "path_tracing_BFS_method"
		int path_tracing_method_type = 0;
		if (settings->path_tracing_BFS_method == TopoFixerSettings::PathTracingBFSMethod::Naive) {
			path_tracing_method_type = 1;
		}
		if (settings->path_tracing_BFS_method ==
		    TopoFixerSettings::PathTracingBFSMethod::AllBreakingPointsPerTrace) {
			path_tracing_method_type = 2;
		}
		if (settings->path_tracing_BFS_method ==
		    TopoFixerSettings::PathTracingBFSMethod::OneBreakingPointPerTrace) {
			path_tracing_method_type = 3;
		}

		// make labels on complex grid vertices unique via a path tracing BFS flood fill
		generateUniqueLabelsOnGridVerticesTrackingFloodFill(mesh, grid, vertices_to_process,
		                                                    unique_labeling, path_tracing_method_type);

		// if naive path tracing method is chosen, calculate the closest breaking point to each complex
		// grid vertex, by comparing distances between a given compelx grid vertex and each breaking
		// point
		if (path_tracing_method_type == 1) {
			computeClosestBreakingPointsForGridVerticesNaive(grid, unique_labeling);
		}

		// determine optimized positions for mesh vertices along grid edges, whose two end vertices have
		// two different material labels assigned; this data will be used by the marching cubes
		// algorithm
		findOptimizedMarchingCubesEdgeVertices(grid, unique_labeling);
	}

	if (settings->grid_vertex_resolution_method ==
	    TopoFixerSettings::GridVertexResolutionMethod::FastMarchingMethod) {
		// Collect breaking points around the complex cell region.
		// We're exploiting a bit different function for these purposes.
		int path_tracing_method_type = 1;
		generateUniqueLabelsOnGridVerticesTrackingFloodFill(mesh, grid, vertices_to_process,
		                                                    unique_labeling, path_tracing_method_type);

		std::priority_queue<FastMarchingTrace> queue =
		    initFastMarching(grid, unique_labeling, breaking_points);
		propogateFastMarching(grid, queue, grid_vertex_traces, unique_labeling);

		// determine optimized positions for mesh vertices along grid edges, whose two end vertices have
		// two different material labels assigned; this data will be used by the marching cubes
		// algorithm
		findOptimizedMarchingCubesEdgeVertices(grid, unique_labeling);
	}

	if (settings->verbosity >= 1) {
		std::cout << "-label resolver finished return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// clear label resolver data structures
void LabelResolver::clearState() { grid_vertex_traces.clear(); }

//------------------------------------------------------------
// functions for generating unique labeling
//------------------------------------------------------------

// fill in the map `unique_labeling` by traversing the complex region in BFS manner and assigning
// unique labels to grid vertices
void LabelResolver::generateUniqueLabelsOnGridVerticesNaiveFloodFill(
    Grid3DInterface& grid, std::deque<long long>& vertices_to_process,
    absl::flat_hash_map<long long, int>& unique_labeling) const {
	// traverse grid vertices in the queue `vertices_to_process`, i.e. in BFS order
	while (!vertices_to_process.empty()) {
		// pop an element of the queue
		long long current_vertex = vertices_to_process.front();
		vertices_to_process.pop_front();

		// only process vertices that haven't been processed yet (haven't had their labels assigned yet)
		if (unique_labeling.count(current_vertex)) {
			continue;
		}

		// ASSERT: at this point, all vertices in `vertices_to_process` should be complex - we processed
		// all non-complex vertices in the complex region during BFS pre-process
		assert(grid.isVertexMarkedComplex(current_vertex));

		// tracks whether `current_vertex` had a unique label assigned in `unique_labeling`
		bool was_current_vertex_assigned = false;
		// tracks whether a vertex with unique label == 0 is a neighbor of `current_vertex`; label 0
		// (global outside) is only spread to `current_vertex`, if there are no other neighbors of
		// `current_vertex` that have a unique label (technically, this is only used as a consistency
		// check)
		bool global_outside_neighbor = false;
		// iterate over the 6 grid neighbors of `current_vertex` (each is offset in one of 6 possible
		// directions), until finding one that has a unique label (because of the queue pre-process,
		// there is at least one neighbor guaranteed to have a unique label); if the unique label != 0,
		// assign it to `current_vertex`; if it is == 0, only assign it if there are no neighbor
		// vertices with non-zero unique labels
		for (int direction = 0; direction < 6; ++direction) {
			// retrieve the neighbour vertex
			long long neigh_vertex = grid.get_vertex_neighboring_vertex(current_vertex, direction);
			// ASSERT: neigh vertex is complex, therefore it has to be inside the grid
			assert(neigh_vertex != -1);

			// if the neighbour has a unique label assigned in `unique_labeling` and `current_vertex` has
			// not had a unique label assigned yet, then if the label != 0, assign it to `current_vertex`,
			// and if the label == 0, don't assign it, but mark that a vertex with global outside label is
			// a neighbor of `current_vertex`; if both the neighbor and `current_vertex` have a unique
			// label assigned, continue to the next neighbor (we don't just quit the loop, because we want
			// to add all neighbors without a unique label to the queue); if the neighbor does not have a
			// unique label assigned, add it to `vertices_to_process`, thus propagating the flood fill

			// this procedure results in the following behavior: a vertex gets its label from the first
			// (in terms of direction) neighbor with a unique label, i.e. we arbitrarily prefer earlier
			// directions; however, this does not apply to the global outside, which is skipped when
			// encountered, but in this case the flag `global_outside_neighbor` is set to true - if it
			// later turns out that the only neighbors of `current_vertex` that have a unique label have
			// label == 0, we will assign it to `current_vertex`
			auto unique_it = unique_labeling.find(neigh_vertex);
			if (unique_it != unique_labeling.end()) {
				if (!was_current_vertex_assigned) {
					if (unique_it->second != 0) {
						unique_labeling[current_vertex] = unique_it->second;
						was_current_vertex_assigned = true;
					} else {
						global_outside_neighbor = true;
					}
				}
			} else {
				// we know `neigh_vertex` is a complex vertex in the complex region; this is because we
				// assign a unique label to all simple (including front) vertices in the BFS pre-process,
				// and only add complex vertices to the BFS queue `vertices_to_process`; the flood fill
				// therefore starts from complex vertices neighboring simple vertices and continues toward
				// the remaining complex vertices in the complex region
				vertices_to_process.push_back(neigh_vertex);
			}
		}

		// if `current_vertex` doesn't have a unique label assigned, it must mean its only neighbors
		// with a unique label assigned have label 0, i.e. the global outside - assign this label to
		// `current_vertex`
		if (!was_current_vertex_assigned) {
			assert(global_outside_neighbor);
			unique_labeling[current_vertex] = 0;
		}
	}
}

//
void LabelResolver::generateUniqueLabelsOnGridVerticesTrackingFloodFill(
    Mesh3DInterface& mesh, Grid3DInterface& grid, std::deque<long long>& vertices_to_process,
    absl::flat_hash_map<long long, int>& unique_labeling, const int path_tracing_method) {
	// traverse grid vertices in the queue `vertices_to_process`, i.e. in BFS order
	while (!vertices_to_process.empty()) {
		// pop an element of the queue
		long long current_vertex = vertices_to_process.front();
		vertices_to_process.pop_front();

		// only process vertices that haven't had their labels assigned yet
		if (unique_labeling.count(current_vertex)) {
			continue;
		}

		// ASSERT: at this point, all vertices in `vertices_to_process` should be complex - we processed
		// all non-complex vertices in the complex region during BFS pre-process
		assert(grid.isVertexMarkedComplex(current_vertex));

		// iterate over the 6 grid neighbors of `current_vertex` (each is offset in one of 6 possible
		// directions)
		for (int direction = 0; direction < 6; ++direction) {
			// retrieve the neighbour grid vertex; if `direction` is even, neighbor vertex is larger than
			// current vertex, if `direction` is odd, neighbor vertex is smaller than current vertex
			long long neigh_vertex = grid.get_vertex_neighboring_vertex(current_vertex, direction);

			// ASSERT: neigh vertex is complex, therefore it has to be inside the grid
			assert(neigh_vertex != -1);

			// if `neigh_vertex` doesn't have a unique label assigned yet, add it to the queue (unless the
			// selected path tracing method is "naive"), and continue to the next neighbor of
			// `current_vertex`
			auto unique_it = unique_labeling.find(neigh_vertex);
			if (unique_it == unique_labeling.end()) {
				// we know `neigh_vertex` is in the complex region, because we assign a unique label to
				// all simple vertices in the complex region in the BFS pre-process, and only add complex
				// vertices to the BFS queue `vertices_to_process`; the flood fill therefore starts from the
				// complex vertices adjacent to simple vertices in the complex region, and continues inward
				// into the complex region
				if (path_tracing_method >= 2) {
					vertices_to_process.push_back(neigh_vertex);
				}
				continue;
			}

			// we know that `neigh_vertex` has a unique label assigned; the we continue processing it
			// based on whether it is simple or complex
			if (!grid.isVertexMarkedComplex(neigh_vertex)) {
				// if `neigh_vertex` is simple, we look for the breaking point along the edge connecting
				// `current_vertex` and `neigh_vertex`, i.e. for the point where the material vector first
				// becomes unphysical

				// retreive the neighbor edge connecting `current_vertex` to `neigh_vertex`
				long long neigh_edge = grid.get_edge_neighboring_vertex(current_vertex, direction);
				// determine orientation of `neigh_edge` (0 for directions 0 and 1, 1 for directions 2 and
				// 3, 2 for directions 4 and 5)
				int edge_orientation = direction / 2;
				// retrieve the vector of intersections between `neigh_edge` and mesh triangles
				std::vector<GridEdgeMeshFaceIntersection> edge_intersections =
				    grid.get_intersections_on_edge(neigh_edge);

				// sort the intersections based on their position on `neigh_edge` either from largest to
				// smallest (if `current_vertex` is smaller than `neigh_vertex`), or from smallest to
				// largest (if `current_vertex` is larger than `neigh_vertex`); this way, investigating the
				// vector `edge_intersections` from its smallest index to its largest index corresponds to
				// traversing from `neigh_index` to `current_index`
				if (direction % 2 == 0) {
					std::sort(edge_intersections.begin(), edge_intersections.end(),
					          [edge_orientation](auto& int_1, auto& int_2) {
						          return int_1.getPosition()[edge_orientation] >
						                 int_2.getPosition()[edge_orientation];
					          });
				} else {
					std::sort(edge_intersections.begin(), edge_intersections.end(),
					          [edge_orientation](auto& int_1, auto& int_2) {
						          return int_1.getPosition()[edge_orientation] <
						                 int_2.getPosition()[edge_orientation];
					          });
				}

				// retrieve the label on `neigh_vertex`; we update it as we traverse along intersections on
				// `neigh_edge` that maintain a physical material vector
				int label_on_edge = unique_labeling[neigh_vertex];

				// we iterate over grid edge-mesh face intersections on `neighbor_edge`, that are saved in
				// vector `edge_intersections`
				for (GridEdgeMeshFaceIntersection intersection : edge_intersections) {
					// for each intersection we check if it constitutes a "breaking point" (a point, where the
					// material vector becomes unphysical)
					if (!isIntersectionPhysical(mesh, grid, direction % 2, intersection, label_on_edge)) {
						// if a breaking point is found, if the selected path tracing method is not "naive", add
						// the breaking point it to the trace of `current_vertex`; if the selected path tracing
						// method is "naive", store the breaking point (together with its associated label)
						if (path_tracing_method >= 2) {
							addBreakingPointToTrace(mesh, grid, current_vertex, label_on_edge, intersection);
						} else {
							breaking_points.emplace_back(intersection, label_on_edge);
						}
						// store the breaking point as an optimized marching cubes mesh vertex location
						grid.addOptimizedMCEdgePoint(neigh_edge, intersection.getPosition());
						// there is no need to investigate other grid edge-mesh face intersections on
						// `neigh_edge`, break the loop
						break;
					}
				}
				if (!grid.hasOptimizedMCEdgePoint(neigh_edge)) {
					grid.addOptimizedMCEdgePoint(neigh_edge, grid.getEdgeCenter(neigh_edge));
				}
			} else {
				// ASSERT: this place should never be reachable only ever be reachable when determining
				// labels for vertices that were added to the queue during the run of this function, not
				// during BFS pre-process (each vertex added to the queue in the pre-process should have a
				// simple neighbor)always, which for `path_tracing_method` equal to 1 (i.e. the "naive"
				// method) should be an empty set
				assert(path_tracing_method != 1);

				// if `neigh_vertex` is complex, check if `current_vertex` has a trace; if not, make a new
				// one
				auto grid_vertex_traces_it = grid_vertex_traces.find(current_vertex);
				if (grid_vertex_traces_it == grid_vertex_traces.end()) {
					grid_vertex_traces[current_vertex] =
					    GridVertexTrace(current_vertex, grid.getVertexPosition(current_vertex));
				}
				// merge the trace of `neigh_vertex` into the trace of `current_vertex`; trace of
				// `neigh_vertex` is assumed to exist, given that `neigh_vertex` is a complex vertex with a
				// unique label, thus it had to have been resolved earlier
				// ASK: should we also merge the trace of `current_vertex` into the trace of
				// `neigh_vertex`?
				grid_vertex_traces[current_vertex].mergeTrace(grid_vertex_traces[neigh_vertex]);
			}
		}

		if (path_tracing_method >= 2) {
			// ASSERT: at least one of the neighbors of `current_vertex` should have a unique label
			// assigned, and therefore a trace should have been created for `current_vertex`
			assert(grid_vertex_traces.count(current_vertex));

			int current_vertex_unique_label = grid_vertex_traces[current_vertex].closest_label;
			if (current_vertex_unique_label == -1) {
				// std::cout << "-for loop ERROR: vertex " << current_vertex << " has label -1\n";
				// std::getchar();
			} else {
				// std::cout << "-OK: vertex " << current_vertex << " has label " <<
				// current_vertex_unique_label
				//          << "\n";
			}
			unique_labeling[current_vertex] = current_vertex_unique_label;

			// check label consistency
			for (auto& [id, trace] : grid_vertex_traces) {
				if (id != trace.id) {
					// std::cout << "-ERROR: id inconsistency: key = " << id << ", trace id = " << trace.id
					//           << '\n';
					// std::getchar();
				}
			}
		}
	}

	// perform checks
	if (path_tracing_method >= 2) {
		// check if all grid vertices in the complex region have a unique label assigned
		absl::flat_hash_set<long long> vertices_in_complex_region;
		for (const long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kBoth)) {
			for (const long long vertex : grid.get_verts_neighboring_cell(ccell)) {
				vertices_in_complex_region.insert(vertex);
			}
		}
		int no_label_counter = 0;
		for (long long vertex : vertices_in_complex_region) {
			if (!unique_labeling.count(vertex)) {
				std::cout << "-ERROR: grid vertex " << vertex
				          << " in complex region does not have a unique label\n";
				no_label_counter++;
			}
			if (unique_labeling[vertex] < 0) {
				std::cout << "-ERROR: grid vertex " << vertex << " has negative material label\n";
			}
			if (unique_labeling.at(vertex) >= 1000) {
				std::cout << "-ERROR: too high grid label: " << unique_labeling.at(vertex) << "\n";
				no_label_counter++;
			}
		}
		std::cout << no_label_counter << '\n';
	}

	// merge traces of neighboring vertices
	if (path_tracing_method >= 2) {
		absl::flat_hash_set<long long> processed_edges;
		// go over all non-front grid edges in the complex region, if the
		for (long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
			for (long long edge : grid.get_edges_neighboring_cell(ccell)) {
				if (!processed_edges.count(edge)) {
					processed_edges.insert(edge);
					std::vector<long long> edge_verts = grid.get_verts_neighboring_edge(edge);
					if (grid_vertex_traces.count(edge_verts[0]) && grid_vertex_traces.count(edge_verts[1])) {
						grid_vertex_traces[edge_verts[0]].mergeTrace(grid_vertex_traces[edge_verts[1]]);
						unique_labeling[edge_verts[0]] = grid_vertex_traces[edge_verts[0]].closest_label;
						grid_vertex_traces[edge_verts[1]].mergeTrace(grid_vertex_traces[edge_verts[0]]);
						unique_labeling[edge_verts[1]] = grid_vertex_traces[edge_verts[1]].closest_label;
					}
					// findMaterialSwitchingPoint(grid, unique_labeling, edge);
				}
			}
		}
	}
}

// find for each complex grid vertex its closest breaking point by comparing distances to all
// existing breaking points, and generate a trace this grid vertex containing only this breaking
// point; also store the label associated to the breaking point in `unique_labeling`
void LabelResolver::computeClosestBreakingPointsForGridVerticesNaive(
    Grid3DInterface& grid, absl::flat_hash_map<long long, int>& unique_labeling) {
	// retrieve complex cells (at this point there shouldn't be any flexible complex cells)
	absl::flat_hash_set<long long> complex_cells =
	    grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kBoth);

	// if there are no complex cells, it means that all vertices have a unique label, return
	if (complex_cells.empty()) {
		return;
	}

	// iterate over all vertices in the complex region
	for (const long long ccell : complex_cells) {
		for (const long long vertex : grid.get_verts_neighboring_cell(ccell)) {
			// check that `vertex` has not been processed yet and that it is complex
			if (!unique_labeling.count(vertex) && grid.isVertexMarkedComplex(vertex)) {
				int closest_label = -1;
				Vec3d closest_BP = Vec3d(0.0);
				findClosestBreakingPointForGridVertexNaive(grid, vertex, closest_label, closest_BP);

				// ASSERT: we can only get here if `vertex` is complex, which necessitates the existence of
				// at least one breaking point
				assert(closest_label != -1);

				// add `vertex` to `unique_labeling` (it will be considered as processed from now on)
				unique_labeling[vertex] = closest_label;
				// make a trace for `vertex`, containing (closest_label,closest_BP) as its only
				// label-breaking point pair
				grid_vertex_traces[vertex] =
				    GridVertexTrace(vertex, grid.getVertexPosition(vertex), closest_label, closest_BP);
			}
		}
	}
}

// find the breaking point in `breaking_points` that is closest to `grid_vertex`, return this
// breaking point, and its associated label
void LabelResolver::findClosestBreakingPointForGridVertexNaive(Grid3DInterface& grid,
                                                               long long grid_vertex,
                                                               int& closest_label,
                                                               Vec3d& closest_BP) const {
	double min_distance_squared_to_BP = std::numeric_limits<double>::max();
	double distance_squared_to_current_BP = std::numeric_limits<double>::max();
	Vec3d vertex_pos = grid.getVertexPosition(grid_vertex);
	for (auto& [breaking_point, label] : breaking_points) {
		// TODO: figure out if we need to unfavour global outside in any way to avoid intrusions in the
		// mesh. The way it was implemented in the commented out code was failing for the case of
		// inversion, producing components of materials instead of removing the outside material.

		// if (label == 0) {
		// 	continue;
		// }
		distance_squared_to_current_BP = dist2(vertex_pos, breaking_point.getPosition());
		if (distance_squared_to_current_BP < min_distance_squared_to_BP) {
			min_distance_squared_to_BP = distance_squared_to_current_BP;
			closest_label = label;
			closest_BP = breaking_point.getPosition();
		}
	}

	// if (closest_label == -1) {
	// 	for (auto& [breaking_point, label] : breaking_points) {
	// 		distance_squared_to_current_BP = mag2(grid.getVertexPosition(grid_vertex) - breaking_point);
	// 		if (distance_squared_to_current_BP < min_distance_squared_to_BP) {
	// 			min_distance_squared_to_BP = distance_squared_to_current_BP;
	// 			closest_label = label;
	// 			closest_BP = breaking_point;
	// 		}
	// 	}
	// }
}

//------------------------------------------------------------
// functions for generating optimized mesh vertex locations
//------------------------------------------------------------

void LabelResolver::findOptimizedMarchingCubesEdgeVertices(
    Grid3DInterface& grid, absl::flat_hash_map<long long, int>& unique_labeling) {
	// set of edges that were already processed to avoid double processing the same edge
	absl::flat_hash_set<long long> processed_edges;
	// iterate over all non-front grid edges (not adjacent to front faces) in the complex region, for
	// each call `findMaterialSwitchingPoint`
	for (long long ccell : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
		for (long long edge : grid.get_edges_neighboring_cell(ccell)) {
			if (!processed_edges.count(edge) && !grid.isFrontEdge(edge)) {
				processed_edges.insert(edge);
				findMaterialSwitchingPoint(grid, unique_labeling, edge);
			}
		}
	}
}

void LabelResolver::findMaterialSwitchingPoint(Grid3DInterface& grid,
                                               absl::flat_hash_map<long long, int>& unique_labeling,
                                               long long edge) {
	// retrieve endpoints of `edge`
	long long edge_v0 = grid.get_verts_neighboring_edge(edge)[0];
	long long edge_v1 = grid.get_verts_neighboring_edge(edge)[1];

	// if `edge` already has an optimized mesh vertex position assigned, return; this happens exactly
	// when `edge` has a breaking point
	if (grid.hasOptimizedMCEdgePoint(edge)) {
		// ASSERT: the only way how `edge` could already have an optimized vertex position assigned is
		// if contains a breaking point, that is, if it connects a simple and a complex vertex
		assert((grid.isVertexMarkedComplex(edge_v0) && !grid.isVertexMarkedComplex(edge_v1)) ||
		       (!grid.isVertexMarkedComplex(edge_v0) && grid.isVertexMarkedComplex(edge_v1)));
		return;
	}

	// if both edge endpoints are simple, there is no switching point to be found, return
	if (!grid.isVertexMarkedComplex(edge_v0) && !grid.isVertexMarkedComplex(edge_v1)) {
		if (unique_labeling[edge_v0] == unique_labeling[edge_v1]) {
			return;
		} else {
			// retrieve the vector of intersections between `neigh_edge` and mesh triangles
			std::vector<GridEdgeMeshFaceIntersection> edge_intersections =
			    grid.get_intersections_on_edge(edge);
			if (edge_intersections.empty()) {
				// This case should not happen naturally. It is caused by the inconsistency during grid
				// labeling. The way we resolve inconsistent vertices right now can lead to the case where
				// edge has different labels but there are not intersections on this edge.
				grid.addOptimizedMCEdgePoint(edge, grid.getEdgeCenter(edge));
			} else if (edge_intersections.size() == 1) {
				grid.addOptimizedMCEdgePoint(edge, edge_intersections[0].getPosition());
			} else {
				// std::cout << "intersections on edge connecting simple vertices: "
				//           << edge_intersections.size() << "\n";
				Vec3d average_point = Vec3d(0.0);
				int num_intersections = 0;
				for (auto& intersection : edge_intersections) {
					average_point += intersection.getPosition();
					num_intersections++;
				}
				average_point /= static_cast<double>(num_intersections);
				grid.addOptimizedMCEdgePoint(edge, average_point);
			}
			return;
		}
	}

	// ASSERT: if the function hasn't returned yet, it must mean that both edge endpoints are complex
	assert(grid.isVertexMarkedComplex(edge_v0) && grid.isVertexMarkedComplex(edge_v1));

	// retrieve material labels on the endpoints of `edge`; both are complex, therefore have a trace
	int mat_v0 = grid_vertex_traces[edge_v0].closest_label;
	int mat_v1 = grid_vertex_traces[edge_v1].closest_label;

	// if material labels on the endpoints of `edge` match, there is no switching point to be found,
	// return
	if (mat_v0 == mat_v1) {
		return;
	}

	Vec3d v0_pos = grid_vertex_traces[edge_v0].position;
	Vec3d v1_pos = grid_vertex_traces[edge_v1].position;
	Vec3d v0_closest_BP = grid_vertex_traces[edge_v0].label_to_breaking_point[mat_v0];
	Vec3d v1_closest_BP = grid_vertex_traces[edge_v1].label_to_breaking_point[mat_v1];

	Vec3d bp_offset = v0_closest_BP - v1_closest_BP;
	Vec3d v_offset = v0_pos - v1_pos;

	double alpha = 0.0;
	double numerator = dot(bp_offset, v0_closest_BP + v1_closest_BP - 2.0 * v1_pos);
	double denominator = 2.0 * dot(bp_offset, v_offset);
	if (mag2(bp_offset) < 1e-100) {
		// Breakings points are extemely close to each other.
		// Just project the mid-point between them on the edge.
		Vec3d mid_point = 0.5 * (v0_closest_BP + v1_closest_BP);
		alpha = dot(mid_point + v1_pos, v_offset) / mag2(v_offset);
	} else if (denominator < 1e-20) {
		// If the closest points are correctly computed, then the only case when this condition is true,
		// is when breaking points are equidistant from any point on the `v0 - v1` line. In this case,
		// just project any of the end points on the line.
		alpha = dot(v0_closest_BP + v1_pos, v_offset) / mag2(v_offset);
	} else {
		// Normal case.
		// Compute the point that is equidistant from both breaking points.
		alpha = numerator / denominator;
	}

	// Clamp the alpha, so we stay inside the edge.
	alpha = std::max(0.0, std::min(1.0, alpha));

	// compute the switching point
	Vec3d offset_point = alpha * (v_offset) + v1_pos;
	grid.addOptimizedMCEdgePoint(edge, offset_point);
}

//------------------------------------------------------------
// helper functions
//------------------------------------------------------------

// collects complex vertices neighboring simple vertices in the complex region, adds them to a queue
// for a BFS flood fill
std::deque<long long> LabelResolver::preprocessMaterialFloodFill(
    Grid3DInterface& grid, absl::flat_hash_map<long long, int>& unique_labeling) const {
	// retrieve complex cells (at this point there shouldn't be any flexible complex cells)
	absl::flat_hash_set<long long> complex_cells =
	    grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kBoth);

	// if there are no complex cells, it means that all vertices have a unique label, return
	if (complex_cells.empty()) {
		return std::deque<long long>();
	}

	// BFS flood fill pre-process: find all non-complex grid vertices in complex cells, add them to
	// `unique_labeling`, and add their complex grid neighbors to vector `bfs_starting_vertices`;
	// they will serve as BFS starting vertices
	absl::flat_hash_set<long long> bfs_starting_vertices_set;
	for (const long long ccell : complex_cells) {
		for (const long long vertex : grid.get_verts_neighboring_cell(ccell)) {
			// check that `vertex` has not been processed yet and that it is simple
			if (!unique_labeling.count(vertex) && !grid.isVertexMarkedComplex(vertex)) {
				// retrieve the unique grid label on `vertex`
				int vertex_label = grid.getLabelFromUniqueMaterialVector(vertex);
				// add `vertex_label` to `unique_labeling`
				unique_labeling[vertex] = vertex_label;
				// add the complex neighbors of `vertex` to `verticecs_to_process`, they will be the BFS
				// starting vertices
				for (int direction = 0; direction < 6; ++direction) {
					long long neigh_vertex = grid.get_vertex_neighboring_vertex(vertex, direction);
					// only including complex grid vertices means we can't add vertices outside of the grid
					if (grid.isVertexMarkedComplex(neigh_vertex)) {
						bfs_starting_vertices_set.insert(neigh_vertex);
					}
				}
			}
		}
	}

	// we sort the BFS starting vertices according to their index, and add them to the return queue in
	// this order - this is to ensure, that the order in which we resolve grid vertices (and therefore
	// the shape of the output mesh) is the same across repeated runs on the same input
	std::vector<long long> bfs_starting_vertices_vector(bfs_starting_vertices_set.begin(),
	                                                    bfs_starting_vertices_set.end());
	std::sort(bfs_starting_vertices_vector.begin(), bfs_starting_vertices_vector.end());
	// queue of grid vertices that will facilitate BFS-based resolving of grid vertex material labels
	std::deque<long long> vertices_to_process(bfs_starting_vertices_vector.begin(),
	                                          bfs_starting_vertices_vector.end());

	return vertices_to_process;
}

// determines whether `intersection`, when encountered in a given direction physically transitions
// from `edge_label` into a new label; `decreasing_edge_traversal` determines whether going from
// neighbor vertex to current vertex traverses the connecting grid edge in a positive or negative
// (x,y,z)-direction
bool LabelResolver::isIntersectionPhysical(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                           bool aligned_edge_traversal,
                                           const GridEdgeMeshFaceIntersection& intersection,
                                           int& edge_label) const {
	Mesh3DTriangle* triangle = intersection.getTriangle();
	Vec2i tri_labels = triangle->getLabels();
	// mesh labels have to be converted to grid labels before we can use them to determine how
	// the material vector evolves as we cross `intersection`
	tri_labels = grid.convertMeshLabelsToGridLabels(tri_labels);
	if (tri_labels[0] == -1 || tri_labels[1] == -1) {
		// std::cout << "negative material\n";
		// std::getchar();
	}

	if (print_debug) {
		// std::cout << "triangle labels: " << tri_labels[0] << " " << tri_labels[1] << '\n';
		// std::cout << "edge labels: " << edge_label << '\n';
	}

	if (!aligned_edge_traversal) {
		if (print_debug) {
			// std::cout << "decreasing edge traversal\n";
		}

		// we are in the regime where we investigate `neigh_edge` from its "larger" end, towards its
		// "smaller" end (i.e. neighbor vertex > current vertex)
		if (intersection.isTriNormalEdgeAligned()) {
			if (print_debug) {
				// std::cout << "triangle normal aligned with grid edge\n";
			}

			if (tri_labels[0] != edge_label) {
				if (print_debug) {
					// std::cout << "triangle label 0 != edge label, non-physical\n";
					//  std::getchar();
				}

				// breaking point found
				return false;
			} else {
				if (print_debug) {
					// std::cout << "triangle label 0 == edge label, physical\n";
					//  std::getchar();
				}

				// intersection is physical
				assert(tri_labels[1] != edge_label);
				edge_label = tri_labels[1];
				return true;
			}
		} else {
			if (print_debug) {
				// std::cout << "triangle normal opposing grid edge\n";
			}

			if (tri_labels[1] != edge_label) {
				if (print_debug) {
					// std::cout << "triangle label 1 != edge label, non-physical\n";
					// std::getchar();
				}

				// breaking point found
				return false;
			} else {
				if (print_debug) {
					// std::cout << "triangle label 1 == edge label, physical\n";
					// std::getchar();
				}

				// intersection is physical
				assert(tri_labels[0] != edge_label);
				edge_label = tri_labels[0];
				return true;
			}
		}
	} else {
		if (print_debug) {
			// std::cout << "increasing edge traversal\n";
		}

		// we are in the regime where we investigate `neigh_edge` from its "smaller" end, towards its
		// "largler" end (i.e. neighbor vertex < current vertex)
		if (intersection.isTriNormalEdgeAligned()) {
			if (print_debug) {
				// std::cout << "triangle normal aligned with grid edge\n";
			}

			if (tri_labels[1] != edge_label) {
				// std::cout << "triangle label 1 != edge label, non-physical\n";
				//  std::getchar();

				// breaking point found
				return false;
			} else {
				// std::cout << "triangle label 1 == edge label, physical\n";
				//  std::getchar();

				// intersection is physical
				assert(tri_labels[0] != edge_label);
				edge_label = tri_labels[0];
				return true;
			}
		} else {
			if (print_debug) {
				// std::cout << "triangle normal opposing grid edge\n";
			}

			if (tri_labels[0] != edge_label) {
				// std::cout << "triangle label 0 != edge label, non-physical\n";
				//  std::getchar();

				// breaking point found
				return false;
			} else {
				// std::cout << "triangle label 0 == edge label, physical\n";
				//  std::getchar();

				// intersection is physical
				assert(tri_labels[1] != edge_label);
				edge_label = tri_labels[1];
				return true;
			}
		}
	}
}

// take the point in `intersection` as a breaking point associated to `label` and either add it to
// the trace of `current_vertex` (if it exists), or generate a new trace for `current_vertex` and
// add the `intersection` point and `label` pair to it
void LabelResolver::addBreakingPointToTrace(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                            long long current_vertex, int label,
                                            const GridEdgeMeshFaceIntersection& intersection) {
	// find if `current_vertex` has a trace in `grid_vertex_traces`
	auto grid_vertex_traces_it = grid_vertex_traces.find(current_vertex);
	if (grid_vertex_traces_it == grid_vertex_traces.end()) {
		// if `current_vertex` doesn't have a trace, make a new trace for it
		grid_vertex_traces[current_vertex] = GridVertexTrace(
		    current_vertex, grid.getVertexPosition(current_vertex), label, intersection.getPosition());
	} else {
		// if `current_vertex` already has a trace, add the breaking point to it
		grid_vertex_traces_it->second.updateBreakingPointForLabel(label, intersection.getPosition());
	}
}

double LabelResolver::distanceToBreakingPoint(Grid3DInterface& grid, long long grid_vertex,
                                              Vec3d breaking_point, long long edge_orient) const {
	assert(edge_orient >= 0 && edge_orient <= 2);
	return std::abs(grid.getVertexPosition(grid_vertex)[edge_orient] - breaking_point[edge_orient]);
}

std::priority_queue<FastMarchingTrace> LabelResolver::initFastMarching(
    Grid3DInterface& grid, const absl::flat_hash_map<long long, int>& unique_labeling,
    const std::vector<std::pair<GridEdgeMeshFaceIntersection, int>>& breaking_points) {
	std::priority_queue<FastMarchingTrace> queue;
	for (auto& [intersection, label] : breaking_points) {
		for (long long neigh : grid.get_verts_neighboring_edge(intersection.getEdgeId())) {
			double distance = dist(intersection.getPosition(), grid.getVertexPosition(neigh));
			queue.emplace(neigh, intersection.getPosition(), label, distance);
		}
	}

	// Fail-safe query generation in case breaking points were not detected.
	if (breaking_points.empty()) {
		absl::flat_hash_set<long long> processed_vertices;
		for (long long cell_id : grid.getComplexCellsSet(Grid3DInterface::ComplexCellType::kFixed)) {
			for (long long vertex_id : grid.get_verts_neighboring_cell(cell_id)) {
				auto [it, is_inserted] = processed_vertices.insert(vertex_id);
				if (!is_inserted || grid.isVertexMarkedComplex(vertex_id)) {
					continue;
				}
				int label = unique_labeling.at(vertex_id);
				for (long long neigh_id : grid.get_verts_adjacent_to_vert(vertex_id)) {
					if (!grid.isVertexMarkedComplex(neigh_id)) {
						continue;
					}
					Vec3d pos = (grid.getVertexPosition(neigh_id) + grid.getVertexPosition(vertex_id)) / 2;
					queue.emplace(neigh_id, pos, label, grid.get_cell_dx());
				}
			}
		}
	}
	return queue;
}

void LabelResolver::propogateFastMarching(
    Grid3DInterface& grid, std::priority_queue<FastMarchingTrace>& queue,
    absl::flat_hash_map<long long, GridVertexTrace>& grid_vertex_traces,
    absl::flat_hash_map<long long, int>& unique_labeling) {
	absl::flat_hash_set<long long> visited;
	while (!queue.empty()) {
		FastMarchingTrace trace = queue.top();
		long long vertex = trace.getVertexId();
		queue.pop();
		auto [it, is_inserted] = visited.insert(vertex);
		if (!is_inserted) {
			// Skip if already visited.
			continue;
		} else if (grid.isVertexMarkedComplex(vertex)) {
			unique_labeling[vertex] = trace.getLabel();
			grid_vertex_traces[vertex] = GridVertexTrace(vertex, grid.getVertexPosition(vertex),
			                                             trace.getLabel(), trace.getBreakingPosition());
		}

		for (long long neighbor : grid.get_verts_adjacent_to_vert(vertex)) {
			if (visited.contains(neighbor) || !grid.isVertexInComplexRegion(neighbor)) {
				continue;
			}
			double distance = dist(grid.getVertexPosition(neighbor), trace.getBreakingPosition());
			queue.emplace(neighbor, trace.getBreakingPosition(), trace.getLabel(), distance);
		}
	}
}