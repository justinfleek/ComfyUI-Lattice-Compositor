/* OpenGLRenderer.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for an openGL renderer used for visual debugging.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include <string>
#include <unordered_set>

#include "../datastructures/Grid3DSparseCubical.h"
#include "../datastructures/GridMeshIntersection.h"
#include "../schemes/SDTopoFixer.h"
#include "../submodules/GridMeshIntersector.h"
#include "ComplexCellVisualizer.h"
#include "GridLabelerVisualizer.h"
#include "ImGUIWindows.h"
#include "IntersectionElementsVisualizer.h"
#include "MeshColorizers.h"
#include "NonmanifoldEdgeVisualizer.h"
#include "OldComplexCellVisualizer.h"
#include "RenderingPrimitives.h"
#include "SmoothingVisualizer.h"
#include "ValueTransferrerVisualizer.h"

// Forward declaration.
class ImGUIWindows;
class ValueTransferrerVisualizer;
class GridLabelerVisualizer;

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the SuperDuperTopoFixer code
class OpenGLRenderer {
	friend ImGUIWindows;
	friend ValueTransferrerVisualizer;
	friend GridLabelerVisualizer;
	friend GridLabelerVisualizer;

 public:
	// constructors
	OpenGLRenderer() = default;
	~OpenGLRenderer() = default;

	// maintenance functions
	static void init(SDTopoFixer* sdtf_, int grid_mode_ = 0, int mesh_mode_ = 0,
	                 bool just_render_ = false, std::string output_path_ = "");

	// openGL callbacks
	static void idle();
	static void display();
	static void mouse(int b, int s, int x, int y);
	static void motion(int x, int y);
	static void passiveMotion(int x, int y);
	static void reshape(int w, int h);
	static void keyboard(unsigned char k, int x, int y);
	static void specialKeyboard(int k, int x, int y);

 private:
	// pointer to the SDTopoFixer object
	static SDTopoFixer* sdtf;
	static TopoFixerSettings settings;
	// pointer to the Mesh3DInterface object
	static Mesh3DInterface* mesh;
	// pointer to the Grid3DCubical object
	static Grid3DSparseCubical* grid3DC;
	// pointer to the multilabelmarchingcuber object
	static MultiLabelMarchingCuber* marchingCube;
	// grid labeler used in the algorithm
	static GridLabeler* grid_labeler;
	// Intersector class to intersect objects
	// static GridMeshSoSIntersector intersector;
	// Intersector class to detect warnings objects
	static std::unique_ptr<GridMeshIntersectorNaive> warning_intersector;

	// Rendering utility functions
	static RenderingPrimitives rendering_primitives;

	// Visualizers
	// Draws vertex labels on the grid.
	static GridLabelerVisualizer grid_labeler_visualizer;
	// Visualizes elements from complex cell detection.
	static ComplexCellVisualizer complex_cell_visualizer;
	// Visualizes values transferred between mesh and grid.
	static ValueTransferrerVisualizer value_transferrer_visualizer;
	// Smoothes positions of mesh vertices.
	static SmoothingVisualizer smoothing_visualizer;
	// Draws complex cell elements.
	static OldComplexCellVisualizer old_complex_cell_visualizer;
	// Draws intersection elements between grid and mesh.
	static IntersectionElementsVisualizer intersection_elements_visualizer;
	// Draws nonmanifold edges.
	static NonmanifoldEdgeVisualizer nonmanifold_edge_visualizer;
	// Collection of all visualizers
	static std::vector<Visualizer*> visualizers;

	// Colorizers
	// Colors triangles in their label colors.
	static MaterialColorizer material_colorizer;
	// Colors triangles around selected one, making others semi-transparent.
	static SelectionColorizer selection_colorizer;
	// Colors inside / outside triangles during separation.
	static CellSeparationColorizer cell_separation_colorizer;
	// Collection of all colorizers.
	static std::vector<Colorizer*> colorizers;
	// A colorizer that combines all previous ones and that will be applied to the mesh.
	static Colorizer* final_colorizer;

	// data for visualization pulled from the mesh
	static std::vector<Vec3d> vertex_positions;
	// static std::vector<Vec3i> triangle_vertices;
	// static std::vector < std::vector<Mesh3DVertex*> > triangle_vertices;
	static std::vector<Vec2i> triangle_labels;
	// static std::vector<Mesh3DHalfCorner> mesh_corner_table;

	// data for visulization pulled from the marching cube
	static std::vector<Vec3d> iso_vertex_positions;
	static std::vector<Vec3i> iso_triangle_vertices;
	static std::vector<Vec2i> iso_triangle_labels;
	static std::vector<long long> sparse_grid_ids;
	static absl::flat_hash_map<long long, int> unique_grid_labeling;

	// data for intersected cells
	static std::vector<long long> intersected_cells;
	static std::vector<std::vector<GridEdgeMeshFaceIntersection>> intersections;
	static std::vector<GridEdgeMeshFaceIntersection> flattened_intersections;
	static absl::flat_hash_set<long long> rendered_cells;

	// data for intersection warnings
	static std::vector<GridMeshDegeneracy> degeneracies;

	// view settings
	static double view_theta;
	static double view_alpha;
	static double view_translate_x;
	static double view_translate_y;
	static double view_dist;

	static int win_w;  // window width
	static int win_h;  // window height

	// view parameters for isosurface from marching cub
	static int smoothingsteps;     // smoothing steps for isosurface mesh from marching cube
	static int selected_material;  // slected material numbering for displaying

	// rotation center
	static double center_x, center_y, center_z;

	// view parameters for grid
	static int cell_x, cell_y, cell_z;               // cell coords
	static int vert_x, vert_y, vert_z;               // vert coords
	static int edge_x, edge_y, edge_z, edge_orient;  // edge coords
	static int face_x, face_y, face_z, face_orient;  // face coords

	// view parameter for labeling purpose on the grid
	static int vert_id, vert_dir;  // vert id and direction
	static int boundary_id;        // boundary id

	// view parameters for mesh
	static double plane_x, plane_y, plane_z, plane_d;  // specify coefficient of cutting plane plane_x
	                                                   // + plane_y y + plane_z z + plane_d = 0
	static int mesh_vert_index;                        // specify the index of a vert of a mesh
	static int use_vert;
	static int use_next;
	static int use_prev;
	static int use_twin;
	static int use_oppos;
	static Mesh3DVertex* marked_vert;
	static int marked;
	static Mesh3DHalfCorner current_hfc;

	// interactive controls
	static int mouse_x;
	static int mouse_y;

	static bool ldrag;
	static int ldrag_start_x;
	static int ldrag_start_y;
	static bool rdrag;
	static int rdrag_start_x;
	static int rdrag_start_y;
	static bool mdrag;
	static int mdrag_start_x;
	static int mdrag_start_y;

	// utility functions
	static void drawCoordinateAxis();
	static void renderBitmapString(float x, float y, float z, std::string s);
	static void drawTextInfo(std::string s, int pos_x, int pos_y);

	// Functions to render mesh related objects
	static void renderMesh();
	static void renderMeshSurface();
	static void renderMeshWireframe();
	static void renderMeshSurfaceWireframe();
	// static void renderMeshCorner();

	// Functions to render grid related objects
	static void renderGrid();
	static void renderIntersectedGridCells();
	static void renderPrimitivesNeighboringCell();
	static void renderPrimitivesNeighboringEdge();
	static void renderPrimitivesNeighboringVertex();
	static void renderPrimitivesNeighboringFace();

	// rendering function for grid labeling
	static void renderVertexNeighboringVertex();

	// Degeneracy handlers
	static void initializeDegeneracies();
	static void renderDegeneracyWarnings();

	// Cell separation rendering
	static void renderFrontFacesGraph();

	// Mesh upkeeping rendering
	static void renderPinches();

	// Save current window state to file.
	static void screenshotPPM(const std::string& filename, unsigned int width, unsigned int height);

	// helper functions
	static void constructCube(const double x, const double y, const double z, const double half_side);
	static void shrinkTriangle(const Vec3d& v0, const Vec3d& v1, const Vec3d& v2,
	                           double shrink_factor, Vec3d& sv0, Vec3d& sv1, Vec3d& sv2);
	static double getTriangleLength(const Vec3d& sv0, const Vec3d& sv1, const Vec3d& sv2);

	static void setLights();

	// bookkeeping variables for rendering and visual debugging
	static int grid_mode;
	static const int num_grid_modes;
	static int mesh_mode;
	static const int num_mesh_modes;
	static int degeneracy_warning_mode;
	static const int num_degeneracy_warning_modes;
	static int grid_mesh_intersection_counter;

	// for material colors
	static const Vec4d matcolors[10];

	static ImGUIWindows imgui_windows;
};
