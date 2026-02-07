/* OpenGLRenderer.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the scheme that manages the SuperDuperTopoFixer code
 * execution.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "OpenGLRenderer.h"

#include <unordered_set>

#include "imgui.h"

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

// pointer to the SDTopoFixer object
SDTopoFixer* OpenGLRenderer::sdtf = NULL;
TopoFixerSettings OpenGLRenderer::settings;

// pointer to the Mesh3DInterface object
Mesh3DInterface* OpenGLRenderer::mesh = NULL;

// pointer to the Mesh3DCT object
Grid3DSparseCubical* OpenGLRenderer::grid3DC = NULL;

// pointer to the marhcing cube object
MultiLabelMarchingCuber* OpenGLRenderer::marchingCube = NULL;

GridLabeler* OpenGLRenderer::grid_labeler = NULL;

// Intersector class to intersect objects
//GridMeshSoSIntersector OpenGLRenderer::intersector;
// Intersector class to detect degeneracies
std::unique_ptr<GridMeshIntersectorNaive> OpenGLRenderer::warning_intersector = NULL;

// Rendering utility functions
RenderingPrimitives OpenGLRenderer::rendering_primitives;

// Draws vertex labels on the grid.
GridLabelerVisualizer OpenGLRenderer::grid_labeler_visualizer;
// Visualizes elements from complex cell detection.
ComplexCellVisualizer OpenGLRenderer::complex_cell_visualizer;
// Visualizes values transferred between mesh and grid.
ValueTransferrerVisualizer OpenGLRenderer::value_transferrer_visualizer;
// Smoothes positions of mesh vertices.
SmoothingVisualizer OpenGLRenderer::smoothing_visualizer;
// Draws complex cell elements.
OldComplexCellVisualizer OpenGLRenderer::old_complex_cell_visualizer;
// Draws intersection elements between grid and mesh.
IntersectionElementsVisualizer OpenGLRenderer::intersection_elements_visualizer;
// Draws nonmanifold edges.
NonmanifoldEdgeVisualizer OpenGLRenderer::nonmanifold_edge_visualizer;
std::vector<Visualizer*> OpenGLRenderer::visualizers = {
    &grid_labeler_visualizer,    &complex_cell_visualizer,     &value_transferrer_visualizer,
    &smoothing_visualizer,       &old_complex_cell_visualizer, &intersection_elements_visualizer,
    &nonmanifold_edge_visualizer};
// Colors triangles in their label colors.
MaterialColorizer OpenGLRenderer::material_colorizer;
// Colors triangles around selected one, making others semi-transparent.
SelectionColorizer OpenGLRenderer::selection_colorizer;
// Colors inside / outside triangles during separation.
CellSeparationColorizer OpenGLRenderer::cell_separation_colorizer;
// Collection of all colorizers.
std::vector<Colorizer*> OpenGLRenderer::colorizers = {
    &material_colorizer, &cell_separation_colorizer, &selection_colorizer};
Colorizer* OpenGLRenderer::final_colorizer = nullptr;

// data for visualization pulled from the mesh
std::vector<Vec3d> OpenGLRenderer::vertex_positions;
// std::vector<Vec3i> OpenGLRenderer::triangle_vertices;
// std::vector < std::vector<Mesh3DVertex*> > triangle_vertices;
std::vector<Vec2i> OpenGLRenderer::triangle_labels;
// std::vector<Mesh3DHalfCorner> OpenGLRenderer::mesh_corner_table;

// data for visualization pulled from the marching cube
std::vector<Vec3d> OpenGLRenderer::iso_vertex_positions;
std::vector<Vec3i> OpenGLRenderer::iso_triangle_vertices;
std::vector<Vec2i> OpenGLRenderer::iso_triangle_labels;
std::vector<long long> OpenGLRenderer::sparse_grid_ids;
absl::flat_hash_map<long long, int> OpenGLRenderer::unique_grid_labeling;

// data for intersected cells
std::vector<long long> OpenGLRenderer::intersected_cells;
absl::flat_hash_set<long long> OpenGLRenderer::rendered_cells;

// data for intersection warnings
bool are_degeneracies_initialized = false;
std::vector<GridMeshDegeneracy> OpenGLRenderer::degeneracies;

// view settings
double OpenGLRenderer::view_theta = 180;
double OpenGLRenderer::view_alpha = -0.3;  // using 180 turns the scene upside-down
double OpenGLRenderer::view_translate_x = -1.4;
double OpenGLRenderer::view_translate_y = 1.5;
double OpenGLRenderer::view_dist = 5.15;

int OpenGLRenderer::win_w = 1080;  // window width
int OpenGLRenderer::win_h = 720;   // window height

// center for rotation
double OpenGLRenderer::center_x;
double OpenGLRenderer::center_y;
double OpenGLRenderer::center_z;

// view parameters for grid
int OpenGLRenderer::cell_x = 0;
int OpenGLRenderer::cell_y = 0;
int OpenGLRenderer::cell_z = 0;
int OpenGLRenderer::vert_x = 0;
int OpenGLRenderer::vert_y = 0;
int OpenGLRenderer::vert_z = 0;
int OpenGLRenderer::edge_x = 0;
int OpenGLRenderer::edge_y = 0;
int OpenGLRenderer::edge_z = 0;
int OpenGLRenderer::edge_orient = 0;
int OpenGLRenderer::face_x = 0;
int OpenGLRenderer::face_y = 0;
int OpenGLRenderer::face_z = 0;
int OpenGLRenderer::face_orient = 0;

// view parameter for labeling purpose on the grid
int OpenGLRenderer::vert_id = 0;
int OpenGLRenderer::vert_dir = 0;     // 0: x; 1: -x; 2: y; 3: -y; 4: z; 5: -z
int OpenGLRenderer::boundary_id = 0;  // 0:x_min, 1:x_max, 2:y_min, 3:y_max, 4:z_min, 5:z_max

// view parameter for mesh
double OpenGLRenderer::plane_x = 0;
double OpenGLRenderer::plane_y = -1;
double OpenGLRenderer::plane_z = 0;
double OpenGLRenderer::plane_d = 0.55;
int OpenGLRenderer::mesh_vert_index = 0;
int OpenGLRenderer::use_vert = 1;
int OpenGLRenderer::use_next = 0;
Mesh3DVertex* OpenGLRenderer::marked_vert = 0;
int OpenGLRenderer::marked = 0;
int OpenGLRenderer::use_prev = 0;
int OpenGLRenderer::use_twin = 0;
int OpenGLRenderer::use_oppos = 0;
Mesh3DHalfCorner OpenGLRenderer::current_hfc;

// view parameter for isosurface from marching cube
int OpenGLRenderer::smoothingsteps = 0;
int OpenGLRenderer::selected_material = 0;

// interactive controls
int OpenGLRenderer::mouse_x = 0;
int OpenGLRenderer::mouse_y = 0;

bool OpenGLRenderer::ldrag = false;
int OpenGLRenderer::ldrag_start_x = 0;
int OpenGLRenderer::ldrag_start_y = 0;
bool OpenGLRenderer::rdrag = false;
int OpenGLRenderer::rdrag_start_x = 0;
int OpenGLRenderer::rdrag_start_y = 0;
bool OpenGLRenderer::mdrag = false;
int OpenGLRenderer::mdrag_start_x = 0;
int OpenGLRenderer::mdrag_start_y = 0;

// bookkeeping variables for rendering and visual debugging
int OpenGLRenderer::grid_mode = 0;
const int OpenGLRenderer::num_grid_modes = 7;
int OpenGLRenderer::mesh_mode = 0;
const int OpenGLRenderer::num_mesh_modes = 5;
int OpenGLRenderer::degeneracy_warning_mode = 0;
const int OpenGLRenderer::num_degeneracy_warning_modes = 2;
int OpenGLRenderer::grid_mesh_intersection_counter = 0;

absl::flat_hash_set<Mesh3DVertex*> pinches;

// predefined for different materials
const Vec4d OpenGLRenderer::matcolors[10] = {
    /*
    {1.0, 0.0, 0.0},
    {0.25, 0.0, 0.0},
    {0.0, 1.0, 0.0},
    {0.0, 0.25, 0.0},
    {0.0, 0.0, 0.1},
    {0.0, 0.0, 0.25}
    */

    ///*
    {1.0, 0.25, 0.5, 1.0},
    {0.5, 1.0, 0.25, 1.0},
    {0.0, 0.45, 1.0, 1.0},
    {1.0, 1.0, 0.0, 1.0},
    {1.0, 0.50, 1.0, 1.0},
    //{1.0, 0.125, 0.67},
    {0.625, 1.0, 0.67, 1.0},
    {0.25, 1.0, 0.45, 1.0},
    //{0.87, 0.75, 0.1267},
    {0.187, 0.75, 0.1267, 1.0},
    {0.75, 0.125, 1.0, 1.0},
    {1, 0.2, 0.80, 1.0}
    //*/

    /*
    {0.9, 0.5, 0.6},
    {0.6, 0.2, 0.0},
    {0.3, 0.2, 0.8},
    {0.1, 1.0, 0.2},
    {0.9, 0.6, 0.1},
    {1.0, 0, 0.5},
    {0.6, 0.8, 0.1},
    {0.6, 0.6, 0.7},
    {0.7, 0.2, 1.0},
    {1.0, 0.5, 0.0}
    */

    /*
    {1.0, 0.0, 0.35},
    {1.0, 1.0, 0.0},
    {1.0, 0.125, 1.0},
    {0.0, 1.0, 0.125},
    {0.125, 0.0, 1.0},
    {1.0, 1.0, 0.125},
    {1.0, 0.125, 1.0},
    {1.0, 0.25, 0.5},
    {0.5, 1.0, 0.25},
    */

    /*
    {1.0, 0.25, 0.5},
    {0.25, 0.58, 0.45},
    {0.68, 1.0, 0.25},
    {0.5, 0.45, 0.0},
    {0.0, 0.45, 0.78},
    {1.0, 1.0, 0.47},
    {0.25, 0.50, 1.0},
    {1.0, 0.25, 0.67},
    {1.0, 1.0, 0.5},
    {0.25, 0.0, 0.80}
    */
};

ImGUIWindows OpenGLRenderer::imgui_windows;

bool just_render;
std::string output_path;

//------------------------------------------------------------
// maintenance functions
//------------------------------------------------------------

// initialize the renderer,
// sdtf_ is the topofixer object
// graphics_mode_ determines the way that the mesh is drawn
void OpenGLRenderer::init(SDTopoFixer* sdtf_, int grid_mode_, int mesh_mode_, bool just_render_,
                          std::string output_path_) {
	sdtf = sdtf_;
	settings = sdtf->getSettings();
	mesh = sdtf->getMesh3DInterface();
	grid3DC = sdtf->getGrid3DCubical();
	grid_labeler = sdtf->getGridLabeler();
	marchingCube = sdtf->getMultiLabelMarchingCuber();
	std::vector<Vec4d> material_colors(std::begin(matcolors), std::end(matcolors));
	warning_intersector = std::make_unique<GridMeshIntersectorNaive>(sdtf->getSettings(), 1.e-7);

	for (Colorizer* colorizer : colorizers) {
		colorizer->init(sdtf, final_colorizer);
		final_colorizer = colorizer;
	}
	material_colorizer.setMaterialColors(material_colors);
	material_colorizer.setOutlineColor({0.25, 1.0, 1.0, 1.0});
	material_colorizer.setOutlineColor({0.0, 0.0, 0.0, 1.0});
	cell_separation_colorizer.setHighlightColor({0.0, 1.0, 0.0, 1.0});

	intersected_cells = grid3DC->getCellsWithTriangles();
	pinches = sdtf_->getMeshUpkeeper()->getT1Resolver()->getPinches();

	grid_mode = grid_mode_;
	mesh_mode = mesh_mode_;
	just_render = just_render_;
	output_path = output_path_;

	// compute the center of mesh
	Vec3d mesh_center = mesh->getMeshCenter();
	center_x = mesh_center[0];
	center_y = mesh_center[1];
	center_z = mesh_center[2];

	// initialize glut with empty parameters
	int _subs_argc = 1;
	char* _subs_argv[1] = {(char*)""};
	glutInit(&_subs_argc, _subs_argv);
	glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH);

	// initial window settings
	glutInitWindowPosition(0, 0);
	glutInitWindowSize(win_w, win_h);
	glutCreateWindow("SuperDuperTopoFixer");
	glewInit();

	// link openGL callbacks
	glutDisplayFunc(&OpenGLRenderer::display);

	glutMouseFunc(&OpenGLRenderer::mouse);
	glutMotionFunc(&OpenGLRenderer::motion);
	glutPassiveMotionFunc(&OpenGLRenderer::passiveMotion);
	glutIdleFunc(&OpenGLRenderer::idle);
	glutReshapeFunc(&OpenGLRenderer::reshape);
	glutKeyboardFunc(&OpenGLRenderer::keyboard);
	glutSpecialFunc(&OpenGLRenderer::specialKeyboard);

	glClearColor(1, 1, 1, 1);
	glClearDepth(1);

	rendering_primitives.init(mesh->getNumberTris());
	imgui_windows.init();

	rendering_primitives.moveMeshToGPU(mesh->ListTriangles(), final_colorizer);

	for (auto visualizer : visualizers) {
		visualizer->init(sdtf, material_colors);
	}

	setLights();

	if (settings.verbosity >= 1)
		std::cout << "-initialized openGL renderer" << std::endl;
}

//------------------------------------------------------------
// utility functions
//------------------------------------------------------------

// draw coordinate axis
void OpenGLRenderer::drawCoordinateAxis() {
	glBegin(GL_LINES);
	glColor3d(1, 0, 0);
	glVertex3d(0, 0, 0);
	glVertex3d(2, 0, 0);
	glColor3d(0, 1, 0);
	glVertex3d(0, 0, 0);
	glVertex3d(0, 2, 0);
	glColor3d(0, 0, 1);
	glVertex3d(0, 0, 0);
	glVertex3d(0, 0, 2);
	glEnd();
}

// draw given string at given position
void OpenGLRenderer::renderBitmapString(float x, float y, float z, std::string s) {
	glColor3f(0, 0, 0);
	glRasterPos3f(x, y, z);
	for (size_t i = 0; i < s.size(); i++)
		glutBitmapCharacter(GLUT_BITMAP_HELVETICA_18, s[i]);
}

// draw text information in top left corner
void OpenGLRenderer::drawTextInfo(std::string text, int pos_x, int pos_y) {
	// set martices for drawing text
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glOrtho(0, win_w, 0, win_h, -1, 1);
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();

	renderBitmapString(pos_x, win_h - pos_y, 0, text);
}

//------------------------------------------------------------
// openGL callbacks
//------------------------------------------------------------

// function that coordinates the run of the SuperDuperTopoFixer scheme
void OpenGLRenderer::idle() {}

// OpenGL callback for displaying a scene
void OpenGLRenderer::display() {
	// clear the scene
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

	// set up visualization matrices
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	double ar = (double)win_w / win_h;
	double vfh = 0.01 * 0.4;
	glFrustum(-vfh * ar, vfh * ar, -vfh, vfh, 0.01, 500);

	// original version rotate around origin
	/*
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	glTranslated(view_translate_x, -view_translate_y, -view_dist);
	glRotated(view_alpha, 1, 0, 0);
	glRotated(view_theta, 0, 1, 0);
	glRotated(-90, 1, 0, 0);
	*/

	// rotate around center of a object
	///*
	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	glTranslated(view_translate_x, -view_translate_y, -view_dist);  // move object to center
	glPushMatrix();
	glTranslated(center_x, center_y, center_z);  // move object to center

	glRotated(view_alpha, 1, 0, 0);
	glRotated(view_theta, 0, 1, 0);
	glRotated(-90, 1, 0, 0);
	glTranslated(-center_x, -center_y, -center_z);  // move back to focus of gluLookAt
	//*/

	drawCoordinateAxis();

	GLdouble eqn[4] = {plane_x, plane_y, plane_z, plane_d};
	glClipPlane(GL_CLIP_PLANE0, eqn);
	glEnable(GL_CLIP_PLANE0);
	renderMesh();
	renderGrid();
	for (auto visualizer : visualizers) {
		visualizer->display();
	}
	renderDegeneracyWarnings();
	// renderFrontFacesGraph();
	renderPinches();
	glDisable(GL_CLIP_PLANE0);

	imgui_windows.renderWindows();

	// text should go last, otherwise it doesn't draw everything
	// drawTextInfo("meshes are great", 20, 20);

	// start processing buffered OpenGL routines
	glutSwapBuffers();

	glPopMatrix();

	if (just_render) {
		screenshotPPM(output_path, glutGet(GLUT_WINDOW_WIDTH), glutGet(GLUT_WINDOW_HEIGHT));
		exit(0);
	}
	// Important to ensure smoothness of the rendering.
	glutPostRedisplay();
}

// OpenGL callback for processing mouse events: b is button, s is state, x,y are coordinates
void OpenGLRenderer::mouse(int b, int s, int x, int y) {
	imgui_windows.mouse(b, s, x, y);

	if (ImGui::GetIO().WantCaptureMouse) {
		return;
	}

	if (b == GLUT_LEFT_BUTTON && s == GLUT_DOWN) {
		ldrag = true;
		ldrag_start_x = x;
		ldrag_start_y = y;
	} else if (b == GLUT_LEFT_BUTTON && s == GLUT_UP) {
		ldrag = false;
	}

	else if (b == GLUT_RIGHT_BUTTON && s == GLUT_DOWN) {
		rdrag = true;
		rdrag_start_x = x;
		rdrag_start_y = y;
	} else if (b == GLUT_RIGHT_BUTTON && s == GLUT_UP) {
		rdrag = false;
	}

	else if (b == GLUT_MIDDLE_BUTTON && s == GLUT_DOWN) {
		mdrag = true;
		mdrag_start_x = x;
		mdrag_start_y = y;
	} else if (b == GLUT_MIDDLE_BUTTON && s == GLUT_UP) {
		mdrag = false;
	}

	glutPostRedisplay();
}

// OpenGL callback for reactions to mouse movement; motion of the mouse is translated into camera
// view changes
void OpenGLRenderer::motion(int x, int y) {
	imgui_windows.motion(x, y);

	if (ImGui::GetIO().WantCaptureMouse) {
		return;
	}

	if (ldrag) {
		view_theta += (x - ldrag_start_x) * 0.1;
		view_alpha += (y - ldrag_start_y) * 0.1;

		ldrag_start_x = x;
		ldrag_start_y = y;
	}

	if (rdrag) {
		view_dist *= pow(2.0, (y - rdrag_start_y) * 0.01);

		rdrag_start_x = x;
		rdrag_start_y = y;
	}

	if (mdrag) {
		view_translate_x +=
		    (x - mdrag_start_x) *
		    0.004;  // * g_sc.view_dist;//*= pow(2.0, (x - g_sc.mdrag_start_x) * 0.01);//
		view_translate_y +=
		    (y - mdrag_start_y) *
		    0.004;  // * g_sc.view_dist;//*= pow(2.0, (y - g_sc.mdrag_start_y) * 0.01);//

		mdrag_start_x = x;
		mdrag_start_y = y;
	}

	mouse_x = x;
	mouse_y = y;

	glutPostRedisplay();
}

// OpenGL callback for mouse movement with no buttons pressed
void OpenGLRenderer::passiveMotion(int x, int y) {
	mouse_x = x;
	mouse_y = y;
	imgui_windows.passiveMotion(x, y);

	glutPostRedisplay();
}

// OpenGL callback for change of window size
void OpenGLRenderer::reshape(int w, int h) {
	win_w = w;
	win_h = h;
	glViewport(0, 0, w, h);
	imgui_windows.reshape(w, h);

	glutPostRedisplay();
}

// OpenGL callback to process keyboard events: k is the key pressed, x and y are mouse coordinates
// in the window when the key is pressed
void OpenGLRenderer::keyboard(unsigned char k, int x, int y) {
	imgui_windows.keyboard(k, x, y);
	if (ImGui::GetIO().WantCaptureKeyboard) {
		return;
	}

	switch (k) {
		case 'q':  // quit
			if (settings.verbosity >= 1)
				std::cout << "-run end called" << std::endl;
			std::cout << "============================================================================="
			             "========"
			          << std::endl;
			std::exit(0);
			break;
		case 'Q':  // shift mesh by 0.01 along x-axis
			mesh->shiftMeshByConstant(0, 0.01);
			break;
		case 'W':  // shift mesh by -0.01 along x-axis
			mesh->shiftMeshByConstant(0, -0.01);
			break;
		case 'n':
			std::cout << "-input selected material numbering for isosurface of a marching cube"
			          << std::endl;
			std::cin >> selected_material;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-selected_material: " << selected_material << std::endl;
			break;
		case 's':  // toggle smoothing of mesh vertices
			smoothing_visualizer.nextState();
			glutPostRedisplay();
			break;
		case 'C':  // cycle complex element visualization
			complex_cell_visualizer.nextState();
			glutPostRedisplay();
			break;
		case 'F':  // cycle individual complex elements to be visualized
			complex_cell_visualizer.nextElement();
			glutPostRedisplay();
			break;
		case 'S':  // cycle value transferrer visualization
			value_transferrer_visualizer.nextState();
			glutPostRedisplay();
			break;
		case 'b':  // input id of a selected boundary;
			std::cout << "-input id of a selected boundary (0:x_min, 1:x_max, 2:y_min, 3:y_max, 4:z_min, "
			             "5:z_max)"
			          << std::endl;
			std::cin >> boundary_id;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-boundary id: " << boundary_id << std::endl;
			break;
		case 'p':  // input coefffient of the cutting plane:  plane_x x + plane_y y + plane_z z +
		           // plane_d = 0;
			std::cout << "-input plane_x, plane_y, plane_z and plane_d for the cutting plane: plane_x x "
			             "+ plane_y y + plane_z z + plane_d = 0"
			          << std::endl;
			std::cin >> plane_x;
			std::cin >> plane_y;
			std::cin >> plane_z;
			std::cin >> plane_d;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-cutting plane: " << plane_x << "x + " << plane_y << "y + " << plane_z
				          << "z + " << plane_d << " = 0" << std::endl;
			break;
		case 'i':  // input vert id
			std::cout << "-input id and direction (0:x, 1:-x, 2:y, 3:-y, 4:z, 5-z) of a chosen vert"
			          << std::endl;
			std::cin >> vert_id;
			std::cin >> vert_dir;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-id and direction of the selected vert: " << vert_id << " " << vert_dir
				          << std::endl;
			break;
		case 'c':  // input cell coords
			std::cout << "-input cell_x, cell_y, cell_z of a chosen cell" << std::endl;
			std::cin >> cell_x;
			std::cin >> cell_y;
			std::cin >> cell_z;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-coords of selected cell: " << cell_x << " " << cell_y << " " << cell_z
				          << std::endl;
			break;
		case 'e':  // input edge coords
			std::cout << "-input edge_x, edge_y, edge_z, edge_orient of a chosen edge" << std::endl;
			std::cin >> edge_x;
			std::cin >> edge_y;
			std::cin >> edge_z;
			std::cin >> edge_orient;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-coords of selected edge: " << edge_x << " " << edge_y << " " << edge_z
				          << " with orient: " << edge_orient << std::endl;
			break;
		case 'f':  // input face coords
			std::cout << "-input face_x, face_y, face_z, face_orient of a chosen face" << std::endl;
			std::cin >> face_x;
			std::cin >> face_y;
			std::cin >> face_z;
			std::cin >> face_orient;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-coords of selected face: " << face_x << " " << face_y << " " << face_z
				          << " with orient: " << face_orient << std::endl;
			break;
		case 'v':  // input vert coords
			std::cout << "-input vert_x, vert_y, vert_z of a chosen vertex" << std::endl;
			std::cin >> vert_x;
			std::cin >> vert_y;
			std::cin >> vert_z;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-coords of selected vert: " << vert_x << " " << vert_y << " " << vert_z
				          << std::endl;
			break;
		case 'V':  // input vert index of a mesh
			std::cout << "-input vert index of a chosen vertex in a mesh" << std::endl;
			std::cin >> mesh_vert_index;
			use_vert = 1;
			std::cout << std::endl;
			if (settings.verbosity >= 1)
				std::cout << "-index of a selected vert of the mesh: " << mesh_vert_index << std::endl;
			break;

		// navigating from one halfcorner:
		case '.':  // next
			printf("moving to next\n");
			use_next = 1;
			use_vert = 0;
			glutPostRedisplay();
			break;
		case ',':  // prev
			// printf("moving to prev\n")
			use_prev = 1;
			use_vert = 0;
			glutPostRedisplay();
			break;
		case 't':  // twin
			printf("moving to twin\n");
			use_twin = 1;
			use_vert = 0;
			glutPostRedisplay();
			break;
		case 'o':  // oppos
			printf("moving to opposite\n");
			use_oppos = 1;
			use_vert = 0;
			glutPostRedisplay();
			break;
		case 'x':  // for marking the vertex we want to walk around
			// printf("marked vertex %p, hfc: %p\n", current_hfc.getVertex(),
			//        current_hfc.getVertex()->getHalfCorner());
			// marked_vert = current_hfc.getVertex();
			// marked = 1;
			std::cout << view_theta << std::endl;
			std::cout << view_alpha << std::endl;
			std::cout << view_translate_x << std::endl;
			std::cout << view_translate_y << std::endl;
			std::cout << view_dist << std::endl;
			glutPostRedisplay();
			break;
		case 'j':  // flip edge
			printf("flipped");
			mesh->EdgeFlipFast(current_hfc.getTri(), current_hfc.getNext()->getVertex(),
			                   current_hfc.getPrev()->getVertex());
			current_hfc = *(current_hfc.getNext());
			glutPostRedisplay();
			break;

		// Go to triangle by address
		case 'a': {
			size_t address;
			std::cout << "Input the triangle address: ";
			std::cin >> address;
			Mesh3DTriangle* tri = reinterpret_cast<Mesh3DTriangle*>(address);
			current_hfc = *(tri->getHalfCorner());
			glutPostRedisplay();
			break;
		}
		case 'l':
			grid_labeler_visualizer.nextState();
			glutPostRedisplay();
			break;
		case 'g':
			// cycle through a counter which represents the current graphics display mode
			// for now, these graphics modes will be arbitrary and probably change a lot during
			// debugging, depending on what we want to draw
			grid_mode++;
			if (grid_mode == num_grid_modes)
				grid_mode = 0;
			if (settings.verbosity >= 1)
				std::cout << "-grid display mode set to " << grid_mode << ": ";
			switch (grid_mode) {
				case 0:
					std::cout << "(render nothing in the grid)" << std::endl;
					break;
				case 1:
					std::cout << "(render every edge in the grid)" << std::endl;
					break;
				case 2:
					std::cout << "(render primitive(s) touching a selected cell)" << std::endl;
					break;
				case 3:
					std::cout << "(render primitive(s) touching a selected vertex)" << std::endl;
					break;
				case 4:
					std::cout << "(render primitive(s) touching a selected edge)" << std::endl;
					break;
				case 5:
					std::cout << "(render primitive(s) touching a selected face)" << std::endl;
					break;
				case 6:
					std::cout << "(render neighboring vertex of a selected vertex with id and direction "
					             "(0:x, 1-x, 2:y, 3-y, 4:z, 5:-z))"
					          << std::endl;
					break;
				case 7:
					std::cout << "(render verts on a selected boundary (0:x_min, 1:x_max, 2:y_min, 3:y_max, "
					             "4:z_min, 5:z_max))"
					          << std::endl;
					break;
			}
			glutPostRedisplay();
			break;
		case 'm':
			// cycle through a counter which represents the current graphics display mode
			// for now, these graphics modes will be arbitrary and probably change a lot during
			// debugging, depending on what we want to draw
			mesh_mode++;
			if (mesh_mode == num_mesh_modes)
				mesh_mode = 0;
			if (settings.verbosity >= 1)
				std::cout << "-mesh display mode set to " << mesh_mode << ": ";
			switch (mesh_mode) {
				case 0:
					std::cout << "render nothing of the mesh" << std::endl;
					break;
				case 1:
					std::cout << "render surface of mesh (with cutting plane)" << std::endl;
					break;
				case 2:
					std::cout << "render wireframe of mesh (with cutting plane)" << std::endl;
					break;
				case 3:
					std::cout << "render wireframe and surface of mesh (with cutting plane)" << std::endl;
					break;
				case 4:
					std::cout << "(render half corner information on a selected vertex)" << std::endl;
					break;
			}
			glutPostRedisplay();
			break;
		case 'd':
			std::cout << "Provide an interface to burst as two integers: ";
			int ll, lr;
			std::cin >> ll >> lr;
			mesh->removeInterface(Vec2i(ll, lr));
			break;
		case 'I':
			intersection_elements_visualizer.nextState();
			glutPostRedisplay();
			break;
		case 'w':
			degeneracy_warning_mode = (degeneracy_warning_mode + 1) % num_degeneracy_warning_modes;
			glutPostRedisplay();
			break;
		case 'X':
			old_complex_cell_visualizer.nextState();
			glutPostRedisplay();
			break;
	}
}

// OpenGL callback to process special keyboard events, such as arrow presses: k is the key
// pressed, x and y are mouse coordinates in the window when the key is pressed
void OpenGLRenderer::specialKeyboard(int k, int x, int y) {
	switch (k) {
		case GLUT_KEY_LEFT:
			break;
		case GLUT_KEY_RIGHT:
			break;
	}
}

//------------------------------------------------------------
// Mesh-related rendering functions
//------------------------------------------------------------

// based on the current value of graphics_mode determine in which way the mesh will be drawn
void OpenGLRenderer::renderMesh() {
	bool is_changed = false;
	for (const Visualizer* visualizer : visualizers) {
		is_changed |= visualizer->isMeshChanged();
	}
	for (const Colorizer* colorizer : colorizers) {
		is_changed |= colorizer->isMeshChanged();
	}

	if (is_changed) {
		rendering_primitives.moveMeshToGPU(mesh->ListTriangles(), final_colorizer);
	}

	switch (mesh_mode) {
		case 0:  // render nothing
			break;

		case 1:  // render surface of mesh
			renderMeshSurface();
			break;

		case 2:  // render wireframe of a mesh
			renderMeshWireframe();
			break;

		case 3:  // render wireframe and surface of a mesh
			renderMeshSurfaceWireframe();
			break;

		case 4:  // render only selected mesh subset
			break;
	}
}

// draw the mesh as a surface
void OpenGLRenderer::renderMeshSurface() {
	rendering_primitives.renderMeshFaces(/*is_shrunk=*/false);
}

// draw the mesh as a wireframe structure
void OpenGLRenderer::renderMeshWireframe() { rendering_primitives.renderMeshEdges(1.0); }

// draw the mesh as a surface and wireframe
void OpenGLRenderer::renderMeshSurfaceWireframe() {
	rendering_primitives.renderMeshEdges(3.0);
	rendering_primitives.renderMeshFaces(/*is_shrunk=*/true);
}

//------------------------------------------------------------
// Grid-related rendering functions
//------------------------------------------------------------

// grid drawing
void OpenGLRenderer::renderGrid() {
	switch (grid_mode) {
		case 0:  // render nothing
			break;
		case 1:  // render every edge in the grid
			renderIntersectedGridCells();
			break;
		case 2:  // render primitive(s) touching a cell
			renderPrimitivesNeighboringCell();
			break;
		case 3:  // render primitive(s) touching a vertex
			renderPrimitivesNeighboringVertex();
			break;
		case 4:  // render primitive(s) touching a edge
			renderPrimitivesNeighboringEdge();
			break;
		case 5:  // render primitive(s) touching a face
			renderPrimitivesNeighboringFace();
			break;
		case 6:  // render neighboring vertex of a selected vertex in a direction
			renderVertexNeighboringVertex();
			break;
	}
}

void OpenGLRenderer::renderIntersectedGridCells() {
	glLineWidth(0.2);
	glBegin(GL_LINES);
	glColor3f(0, 0, 0);

	double x(0), y(0), z(0);

	// draw all edges oriented
	for (const auto cell_id : intersected_cells) {
		const std::vector<long long> edges = grid3DC->get_edges_neighboring_cell(cell_id);
		for (const long long edge_id : edges) {
			std::vector<long long> vertices = grid3DC->get_verts_neighboring_edge(edge_id);
			grid3DC->getVertexPosition(vertices[0], x, y, z);
			glVertex3f(x, y, z);
			grid3DC->getVertexPosition(vertices[1], x, y, z);
			glVertex3f(x, y, z);
		}
	}
	glEnd();
	rendered_cells.clear();
	glLineWidth(1);
}

// draw promitives neighboring vertex
void OpenGLRenderer::renderPrimitivesNeighboringVertex() {
	double x(0), y(0), z(0);
	long long nx(grid3DC->get_dim_nx()), ny(grid3DC->get_dim_ny()), nz(grid3DC->get_dim_nz());
	long long vi, vj, vk;

	if (vert_x > nx || vert_y > ny || vert_z > nz) {
		std::cout << "-WARNING: vert_x, vert_y, vert_z shall be smaller than " << nx + 1 << " "
		          << ny + 1 << " " << nz + 1 << std::endl;
	}

	glEnable(GL_DEPTH_TEST);
	glDepthFunc(GL_LEQUAL);
	glDepthRange(0.0f, 1.0f);
	glClearDepth(1.0f);

	renderIntersectedGridCells();

	// draw the selected point
	grid3DC->getVertexPosition(vert_x, vert_y, vert_z, x, y, z);
	glPointSize(20.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glBegin(GL_POINTS);
	glColor3f(0.60, 0.0, 0.0);
	glVertex3f(x, y, z);
	glEnd();

	// draw edges touching a selected vertex
	std::vector<long long> edges(grid3DC->get_edges_neighboring_vertex(vert_x, vert_y, vert_z));

	glLineWidth(18.0);
	glColor3f(0.65, 0.5, 0.0);
	for (const auto& e : edges) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

		glBegin(GL_LINES);
		for (const auto& v : verts) {
			grid3DC->get_vertex_coords(v, vi, vj, vk);
			grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
			glVertex3f(x, y, z);
		}
		glEnd();
	}

	// draw faces touching a vertex
	std::vector<long long> faces(grid3DC->get_faces_neighboring_vertex(vert_x, vert_y, vert_z));
	glColor3f(0.0, 0.65, 0.65);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	for (const auto& f : faces) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_face(f));

		if (verts.size() == 4) {
			glBegin(GL_TRIANGLE_STRIP);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		} else {
			std::cout << "-WARNING: the face touching selected vertex is out of range " << nx + 1 << " "
			          << ny + 1 << " " << nz + 1 << std::endl;
		}
	}
	glEnd();

	// draw cells toucing a vetex
	std::vector<long long> cells(grid3DC->get_cells_neighboring_vertex(vert_x, vert_y, vert_z));
	glLineWidth(4);
	glColor3f(0.0, 0.25, 0.5);

	for (const auto& c : cells) {
		std::vector<long long> edges(grid3DC->get_edges_neighboring_cell(c));

		for (const auto& e : edges) {
			std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

			glBegin(GL_LINES);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		}
	}

	glEnd();
	glLineWidth(1);
}

// draw primitives neighboring cell
void OpenGLRenderer::renderPrimitivesNeighboringCell() {
	double x(0), y(0), z(0);
	long long nx(grid3DC->get_dim_nx()), ny(grid3DC->get_dim_ny()), nz(grid3DC->get_dim_nz());
	long long vi, vj, vk;

	if (cell_x >= nx || cell_y >= ny || cell_z >= nz) {
		std::cout << "-WARNING: cell_x, cell_y, cell_z shall be smaller than " << nx << " " << ny << " "
		          << nz << std::endl;
	}

	renderIntersectedGridCells();

	// draw points toucing a selected cell
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glEnable(GL_DEPTH_TEST);
	glPointSize(18.0);
	glColor3f(0.860, 0.0, 0.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glBegin(GL_POINTS);
	std::vector<long long> verts(grid3DC->get_verts_neighboring_cell(cell_x, cell_y, cell_z));
	for (const auto& v : verts) {
		grid3DC->get_vertex_coords(v, vi, vj, vk);
		grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
		glVertex3f(x, y, z);
	}
	glEnd();

	// draw edges toucing a selected cell
	glLineWidth(16);
	glColor3f(0.65, 0.5, 0.0);

	std::vector<long long> edges(grid3DC->get_edges_neighboring_cell(cell_x, cell_y, cell_z));

	for (const auto& e : edges) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

		glBegin(GL_LINES);
		for (const auto& v : verts) {
			grid3DC->get_vertex_coords(v, vi, vj, vk);
			grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
			glVertex3f(x, y, z);
		}
		glEnd();
	}

	// draw faces touching a selected cell
	std::vector<long long> faces(grid3DC->get_faces_neighboring_cell(cell_x, cell_y, cell_z));
	glColor3f(0.0, 0.65, 0.65);
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	for (const auto& f : faces) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_face(f));
		if (verts.size() == 4) {
			glBegin(GL_TRIANGLE_STRIP);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		} else {
			std::cout << "-WARNING: the selected cell is out of range " << nx + 1 << " " << ny + 1 << " "
			          << nz + 1 << std::endl;
		}
	}
	glEnd();

	// draw cells toucing a selected cell
	std::vector<long long> cells(grid3DC->get_cells_neighboring_cell(cell_x, cell_y, cell_z));
	glLineWidth(4);
	glColor3f(0.25, 0.25, 0.0);
	for (const auto& c : cells) {
		std::vector<long long> edges(grid3DC->get_edges_neighboring_cell(c));

		for (const auto& e : edges) {
			std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));
			glBegin(GL_LINES);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		}
	}
	glLineWidth(1);
}

// draw promitives neighboring edge
void OpenGLRenderer::renderPrimitivesNeighboringEdge() {
	double x(0), y(0), z(0);

	long long nx(grid3DC->get_dim_nx()), ny(grid3DC->get_dim_ny()), nz(grid3DC->get_dim_nz());

	long long vi, vj, vk;

	if (edge_x > nx || edge_y > ny || edge_z > nz || edge_orient > 3) {
		std::cout << "-WARNING: edge_x, edge_y, edge_z shall be smaller than " << nx + 1 << " "
		          << ny + 1 << " " << nz + 1 << " edge orientation shall be smaller than " << 4
		          << std::endl;
	}

	glEnable(GL_DEPTH_TEST);
	renderIntersectedGridCells();

	// draw the selected edge
	std::vector<long long> verts(
	    grid3DC->get_verts_neighboring_edge(edge_x, edge_y, edge_z, edge_orient));
	glLineWidth(18);
	glColor3f(0.65, 0.5, 0.0);
	glBegin(GL_LINES);

	for (const auto& v : verts) {
		grid3DC->get_vertex_coords(v, vi, vj, vk);
		grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
		glVertex3f(x, y, z);
	}
	glEnd();

	// draw vertex touching a selected edge
	glPointSize(20.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glBegin(GL_POINTS);
	glColor3f(0.65, 0.0, 0.0);
	for (const auto& v : verts) {
		grid3DC->get_vertex_coords(v, vi, vj, vk);
		grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
		glVertex3f(x, y, z);
	}
	glEnd();

	// draw faces toucing a selected edge
	std::vector<long long> faces(
	    grid3DC->get_faces_neighboring_edge(edge_x, edge_y, edge_z, edge_orient));
	glColor3f(0.0, 0.65, 0.65);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	for (const auto& f : faces) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_face(f));

		if (verts.size() == 4) {
			glBegin(GL_TRIANGLE_STRIP);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		} else {
			std::cout << "-WARNING: the face touching selected vertex is out of range " << nx + 1 << " "
			          << ny + 1 << " " << nz + 1 << std::endl;
		}
	}
	glEnd();

	// draw cells touching a selected edge
	std::vector<long long> cells(
	    grid3DC->get_cells_neighboring_edge(edge_x, edge_y, edge_z, edge_orient));
	glLineWidth(4);
	glColor3f(0.0, 0.25, 0.5);

	for (const auto& c : cells) {
		std::vector<long long> edges(grid3DC->get_edges_neighboring_cell(c));

		for (const auto& e : edges) {
			std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

			glBegin(GL_LINES);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		}
	}

	glLineWidth(1);
}

// draw promitives neighboring face
void OpenGLRenderer::renderPrimitivesNeighboringFace() {
	double x(0), y(0), z(0);

	long long nx(grid3DC->get_dim_nx()), ny(grid3DC->get_dim_ny()), nz(grid3DC->get_dim_nz());

	long long vi, vj, vk;

	if (face_x > nx || face_y > ny || face_z > nz || face_orient > 3) {
		std::cout << "-WARNING: face_x, face_y, face_z shall be smaller than " << nx + 1 << " "
		          << ny + 1 << " " << nz + 1 << " face orientation shall be smaller than " << 4
		          << std::endl;
	}

	glEnable(GL_DEPTH_TEST);

	renderIntersectedGridCells();

	// draw the vertices touching a selected face
	glPointSize(18.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glBegin(GL_POINTS);
	glColor3f(0.0, 0.65, 0.5);

	std::vector<long long> verts(
	    grid3DC->get_verts_neighboring_face(face_x, face_y, face_z, face_orient));
	for (const auto& v : verts) {
		grid3DC->get_vertex_coords(v, vi, vj, vk);
		grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
		glVertex3f(x, y, z);
	}
	glEnd();

	// draw the selected facegl
	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glColor3f(0.85, 0.00, 0.05);
	if (verts.size() == 4) {
		glBegin(GL_TRIANGLE_STRIP);
		for (const auto& v : verts) {
			grid3DC->get_vertex_coords(v, vi, vj, vk);
			grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
			glVertex3f(x, y, z);
		}
		glEnd();
	}

	// draw the edges touching a selected face
	std::vector<long long> edges(
	    grid3DC->get_edges_neighboring_face(face_x, face_y, face_z, face_orient));
	glLineWidth(8);
	glColor3f(0.65, 0.5, 0.0);

	for (const auto& e : edges) {
		std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

		glBegin(GL_LINES);
		for (const auto& v : verts) {
			grid3DC->get_vertex_coords(v, vi, vj, vk);
			grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
			glVertex3f(x, y, z);
		}
		glEnd();
	}

	// draw the cells touching a selected face
	std::vector<long long> cells(
	    grid3DC->get_cells_neighboring_face(face_x, face_y, face_z, face_orient));
	glLineWidth(4);
	glColor3f(0.0, 0.25, 0.5);

	for (const auto& c : cells) {
		std::vector<long long> edges(grid3DC->get_edges_neighboring_cell(c));

		for (const auto& e : edges) {
			std::vector<long long> verts(grid3DC->get_verts_neighboring_edge(e));

			glBegin(GL_LINES);
			for (const auto& v : verts) {
				grid3DC->get_vertex_coords(v, vi, vj, vk);
				grid3DC->getVertexPosition(vi, vj, vk, x, y, z);
				glVertex3f(x, y, z);
			}
			glEnd();
		}
	}
	glLineWidth(1);
}

//
// draw vertex neighboring a vertex in a specified direction
//
void OpenGLRenderer::renderVertexNeighboringVertex() {
	long long i, j, k;
	double x, y, z;

	glEnable(GL_DEPTH_TEST);
	glDepthFunc(GL_LEQUAL);
	glDepthRange(0.0f, 1.0f);
	glClearDepth(1.0f);

	renderIntersectedGridCells();

	// draw the selected point
	grid3DC->get_vertex_coords(vert_id, i, j, k);
	grid3DC->getVertexPosition(i, j, k, x, y, z);
	glPointSize(20.0);
	glEnable(GL_PROGRAM_POINT_SIZE);
	glEnable(GL_POINT_SMOOTH);
	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glBegin(GL_POINTS);
	glColor3f(0.60, 0.0, 0.0);
	glVertex3f(x, y, z);

	long long neighboring_vertex_id = grid3DC->get_vertex_neighboring_vertex(vert_id, vert_dir);
	if (neighboring_vertex_id != -1) {
		grid3DC->get_vertex_coords(neighboring_vertex_id, i, j, k);
		grid3DC->getVertexPosition(i, j, k, x, y, z);
		glColor3f(0.00, 0.60, 0.0);
		glVertex3f(x, y, z);
	} else {
		std::cout << "-WARNING: neighboring vertex is out of range: " << neighboring_vertex_id
		          << std::endl;
	}
	glEnd();
}

void OpenGLRenderer::initializeDegeneracies() {
	are_degeneracies_initialized = true;
	degeneracies = warning_intersector->find_intersection_degeneracies(*grid3DC, *mesh);
	std::cout << " Warnings cout: " << degeneracies.size() << std::endl;
}

void OpenGLRenderer::renderDegeneracyWarnings() {
	if (degeneracy_warning_mode == 0) {
		return;
	}

	if (!are_degeneracies_initialized) {
		initializeDegeneracies();
	}

	GLfloat point_size;
	glGetFloatv(GL_POINT_SIZE, &point_size);
	glPointSize(20.0);
	glEnable(GL_POINT_SMOOTH);
	glColor3f(1.0, 0.0, 0.0);
	glBegin(GL_POINTS);
	for (const auto& degeneracy : degeneracies) {
		if (degeneracy.type == degeneracy.kGridNearTriangleBorder) {
			if (degeneracy.grid_info.type == degeneracy.grid_info.kVertex) {
				Vec3d coords;
				grid3DC->getVertexPosition(degeneracy.grid_info.vertex_id, coords[0], coords[1], coords[2]);
				glVertex3d(coords[0], coords[1], coords[2]);
			}

			if (degeneracy.tri_info.type == degeneracy.tri_info.kVertex) {
				Vec3d coords = degeneracy.tri_info.tri_vertex->getCoords();
				glVertex3d(coords[0], coords[1], coords[2]);
			}
		}
	}
	glEnd();
	glPointSize(point_size);

	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(10.0);
	glBegin(GL_LINES);
	for (const auto& degeneracy : degeneracies) {
		if (degeneracy.type == degeneracy.kGridNearTriangleBorder) {
			if (degeneracy.grid_info.type == degeneracy.grid_info.kEdge) {
				std::vector<long long> verts =
				    grid3DC->get_verts_neighboring_edge(degeneracy.grid_info.edge_id);
				for (int i = 0; i < 2; ++i) {
					Vec3d coords;
					grid3DC->getVertexPosition(verts[i], coords[0], coords[1], coords[2]);
					glVertex3d(coords[0], coords[1], coords[2]);
				}
			}

			if (degeneracy.tri_info.type == degeneracy.tri_info.kEdge) {
				for (auto vertex : degeneracy.tri_info.tri_edge) {
					Vec3d coords = vertex->getCoords();
					glVertex3d(coords[0], coords[1], coords[2]);
				}
			}
		}
	}
	glEnd();
	glLineWidth(width);

	glDisable(GL_POINT_SMOOTH);
	glBegin(GL_POINTS);
	for (const auto& degeneracy : degeneracies) {
		if (degeneracy.type == degeneracy.kTwoCloseIntersections) {
			Vec3d coords = degeneracy.intersection_pair[0].getPosition();
			glVertex3d(coords[0], coords[1], coords[2]);
		}
	}
	glEnd();

	glEnable(GL_POINT_SMOOTH);
}

void OpenGLRenderer::constructCube(const double x, const double y, const double z,
	                          			const double half_side) {
	// draw 12 faces
	// two fronts
	glNormal3f(0.0, -1, 0);
	glVertex3f(x - half_side, y - half_side, z - half_side);
	glVertex3f(x + half_side, y - half_side, z - half_side);
	glVertex3f(x - half_side, y - half_side, z + half_side);

	glNormal3f(0.0, -1, 0);
	glVertex3f(x - half_side, y - half_side, z + half_side);
	glVertex3f(x + half_side, y - half_side, z - half_side);
	glVertex3f(x + half_side, y - half_side, z + half_side);

	// two backs
	glNormal3f(0.0, 1, 0);
	glVertex3f(x - half_side, y + half_side, z - half_side);
	glVertex3f(x - half_side, y + half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);

	glNormal3f(0.0, 1, 0);
	glVertex3f(x - half_side, y + half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);

	// two left
	glNormal3f(-1.0, 0, 0);
	glVertex3f(x - half_side, y - half_side, z - half_side);
	glVertex3f(x - half_side, y - half_side, z + half_side);
	glVertex3f(x - half_side, y + half_side, z - half_side);

	glNormal3f(-1.0, 0, 0);
	glVertex3f(x - half_side, y - half_side, z + half_side);
	glVertex3f(x - half_side, y + half_side, z - half_side);
	glVertex3f(x - half_side, y + half_side, z + half_side);

	// two right
	glNormal3f(1.0, 0, 0);
	glVertex3f(x + half_side, y - half_side, z - half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);
	glVertex3f(x + half_side, y - half_side, z + half_side);

	glNormal3f(1.0, 0, 0);
	glVertex3f(x + half_side, y - half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);
	glVertex3f(x + half_side, y + half_side, z + half_side);

	// two down
	glNormal3f(0, 0, -1);
	glVertex3f(x - half_side, y - half_side, z - half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);
	glVertex3f(x + half_side, y - half_side, z - half_side);

	glNormal3f(0, 0, -1);
	glVertex3f(x - half_side, y - half_side, z - half_side);
	glVertex3f(x - half_side, y + half_side, z - half_side);
	glVertex3f(x + half_side, y + half_side, z - half_side);

	// two top
	glNormal3f(0, 0, 1);
	glVertex3f(x - half_side, y - half_side, z + half_side);
	glVertex3f(x + half_side, y - half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z + half_side);

	glNormal3f(0, 0, 1);
	glVertex3f(x - half_side, y - half_side, z + half_side);
	glVertex3f(x + half_side, y + half_side, z + half_side);
	glVertex3f(x - half_side, y + half_side, z + half_side);
}

// some other helping function, schrink the triangle by a factor
void OpenGLRenderer::shrinkTriangle(const Vec3d& v0, const Vec3d& v1, const Vec3d& v2,
                                    double shrink_factor, Vec3d& sv0, Vec3d& sv1, Vec3d& sv2) {
	double a(sqrt((v1 - v0)[0] * (v1 - v0)[0] + (v1 - v0)[1] * (v1 - v0)[1] +
	              (v1 - v0)[2] * (v1 - v0)[2]));
	double b(sqrt((v2 - v0)[0] * (v2 - v0)[0] + (v2 - v0)[1] * (v2 - v0)[1] +
	              (v2 - v0)[2] * (v2 - v0)[2]));
	double c(sqrt((v2 - v1)[0] * (v2 - v1)[0] + (v2 - v1)[1] * (v2 - v1)[1] +
	              (v2 - v1)[2] * (v2 - v1)[2]));

	double s = 0.5 * (a + b + c);

	// Heron's formula

	double r = sqrt((s - a) * (s - b) * (s - c) / s);

	// schrink distance
	double x = r * shrink_factor;

	// double kappa=r/(r-x);   //kappa=x/r
	double kappa = x / r;

	Vec3d center;

	double l = a + b + c;
	center[0] = (a * v0[0] + c * v1[0] + b * v2[0]) / l;
	center[1] = (a * v0[1] + c * v1[1] + b * v2[1]) / l;
	center[2] = (a * v0[2] + c * v1[2] + b * v2[2]) / l;

	// std::cout<<"kappa: "<<kappa<<" x: "<<x<<" shrink: " << shrink_factor<<" r: "<<r<<std::endl;

	sv0 = v0 + (center - v0) * kappa;
	sv1 = v1 + (center - v1) * kappa;
	sv2 = v2 + (center - v2) * kappa;
}

// get triangle maximal length
double OpenGLRenderer::getTriangleLength(const Vec3d& sv0, const Vec3d& sv1, const Vec3d& sv2) {
	double l1(sqrt(dot(sv1 - sv0, sv1 - sv0)));
	double l2(sqrt(dot(sv2 - sv0, sv2 - sv0)));
	double l3(sqrt(dot(sv2 - sv1, sv2 - sv1)));

	return std::max(std::max(l1, l2), l3);
}

void OpenGLRenderer::setLights() {
	glEnable(GL_DEPTH_TEST);
	glDepthFunc(GL_LEQUAL);
	glDepthRange(0.0f, 1.0f);
	glClearDepth(1.0f);

	glEnable(GL_NORMALIZE);
	glEnable(GL_LIGHTING);
	glEnable(GL_LIGHT0);

	GLfloat mat_diffuse[] = {1.0, 1.0, 1.0, 1.0};
	glMaterialfv(GL_FRONT, GL_DIFFUSE, mat_diffuse);
	GLfloat mat_specular[] = {0.0, 0.0, 0.0, 0.0};
	glMaterialfv(GL_FRONT, GL_SPECULAR, mat_specular);
	GLfloat mat_shininess[] = {20.0};
	glMaterialfv(GL_FRONT, GL_SHININESS, mat_shininess);

	GLfloat light_ambient[] = {0.3, 0.3, 0.3, 1.0};
	glLightfv(GL_LIGHT0, GL_AMBIENT, light_ambient);
	GLfloat light_direction[] = {1.0, 1.0, 1.0, 0.0};
	glLightfv(GL_LIGHT0, GL_SPOT_DIRECTION, light_direction);
}

void OpenGLRenderer::renderFrontFacesGraph() {
	Vec3d coords;
	GLfloat width;
	glGetFloatv(GL_LINE_WIDTH, &width);
	glLineWidth(10.0);
	glBegin(GL_LINES);
	absl::flat_hash_set<Mesh3DVertex*> verts;
	for (long long face_id : grid3DC->getFrontFacesVector()) {
		for (const auto& graph_edge : grid3DC->getGraphOnFace(face_id)) {
			Mesh3DVertex* v1 = graph_edge.first.first;
			Mesh3DVertex* v2 = graph_edge.first.second;
			verts.insert(v1);
			verts.insert(v2);
			coords = v1->getCoords();
			glVertex3f(coords[0], coords[1], coords[2]);
			coords = v2->getCoords();
			glVertex3f(coords[0], coords[1], coords[2]);
		}
	}
	glEnd();
	glLineWidth(width);

	GLfloat point_size;
	glGetFloatv(GL_POINT_SIZE, &point_size);
	glPointSize(20.0);
	glEnable(GL_POINT_SMOOTH);
	glColor3f(1.0, 0.0, 0.0);
	glBegin(GL_POINTS);
	for (Mesh3DVertex* vert : verts) {
		coords = vert->getCoords();
		glVertex3f(coords[0], coords[1], coords[2]);
	}
	// Render Vertices
	glEnd();
	glPointSize(point_size);
}

void OpenGLRenderer::renderPinches() {
	GLfloat point_size;
	glGetFloatv(GL_POINT_SIZE, &point_size);
	glPointSize(30.0);
	glEnable(GL_POINT_SMOOTH);
	glColor3f(1.0, 0.0, 0.0);
	glBegin(GL_POINTS);
	for (Mesh3DVertex* vert : pinches) {
		Vec3d coords = vert->getCoords();
		glVertex3f(coords[0], coords[1], coords[2]);
	}
	// Render Vertices
	glEnd();
	glPointSize(point_size);
}

// Adapted from
// https://stackoverflow.com/questions/3191978/how-to-use-glut-opengl-to-render-to-a-file
// and
// https://stackoverflow.com/questions/31100262/fopen-s-not-resolved-under-ubuntu
#ifdef __unix
#define fopen_s(pFile, filename, mode) ((*(pFile)) = fopen((filename), (mode))) == NULL
#endif
void OpenGLRenderer::screenshotPPM(const std::string& filename, unsigned int width,
                                   unsigned int height) {
	size_t i, j, cur;
	const size_t format_nchannels = 3;
	FILE* f;
	fopen_s(&f, filename.c_str(), "w");
	fprintf(f, "P3\n%d %d\n%d\n", width, height, 255);
	GLubyte* pixels =
	    reinterpret_cast<GLubyte*>(malloc(format_nchannels * sizeof(GLubyte) * width * height));
	glReadPixels(0, 0, width, height, GL_RGB, GL_UNSIGNED_BYTE, pixels);
	for (i = 0; i < height; i++) {
		for (j = 0; j < width; j++) {
			cur = format_nchannels * ((height - i - 1) * width + j);
			fprintf(f, "%3d %3d %3d ", pixels[cur], pixels[cur + 1], pixels[cur + 2]);
		}
		fprintf(f, "\n");
	}
	fclose(f);
}