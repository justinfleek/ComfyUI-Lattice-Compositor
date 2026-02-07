#include "TopoViewer.h"

#include <algorithm>
#include <cmath>
#include <filesystem>
#include <iostream>
#include <memory>

#include "../utilities/string_util.h"
#include "backends/imgui_impl_glfw.h"
#include "backends/imgui_impl_opengl3.h"
#include "geom/Primitives.h"
#include "glad/glad.h"
#include "imgui.h"
#include "include_glfw.h"
#include "logic/AnimationTool.h"
#include "logic/CameraTool.h"
#include "logic/GeometryFactory.h"
#include "logic/VisualizationTool.h"
#include "logic/topo_fixer_calls.h"
#include "misc/cpp/imgui_stdlib.h"
#include "modules/MeshUpkeeper.h"
#include "schemes/TopoFixerSettings.h"

using namespace sdtf::viewer::logic;

namespace sdtf::viewer {
;

TopoViewer::TopoViewer(int width, int height, int num_msaa_samples)
    : canvas_width_(width), canvas_height_(height) {
	// set the static window pointer to "this", so it can receive GLFW events
	TopoViewer::event_window = this;
	// low-level errors are redirected to command line; we don't ever want to see errors from here:)
	glfwSetErrorCallback(&TopoViewer::raw_errorCallback);

	if (!glfwInit())
		exit(EXIT_FAILURE);
	glfw_initialized_ = true;

	// Create window with GLFW, init Imgui
	window_ = createDefaultWindow(width, height, &content_scale_);

	scene_ = std::make_unique<scene::Scene>();
	root_node_ = scene_->addNode(std::make_unique<scene::Node>());

	// Create a mini scene in the corner that will show the coordinate frame
	coordinate_frame_overlay_scene_ = std::make_unique<logic::CoordinateFrameOverlayScene>();

	double ratio = static_cast<double>(width) / height;
	createDefaultCamera(ratio);

	renderer_ = std::make_unique<logic::Renderer>(width, height, num_msaa_samples, scene_.get());
	// this is the OS content scaling to adapt the application to high DPI displays
	renderer_->setContentScale(content_scale_);

	// Add the coordinate frame overlay to the renderer
	Renderer::OverlaySceneParameters param;
	param.bottom_left << 0, 0;
	auto sz = computeCoordinateFrameOverlaySceneSize();
	param.size << sz, sz;
	renderer_->addOverlayScene(coordinate_frame_overlay_scene_->scene(), param);

	resetCameraPosition();
	// Show a test cube so the view is never completely empty. This is remove once a TopoFixer state
	// is loaded.
	addTestCube();

	// Inits the "tools" that encapsulate user interaction (like moving the camera, selecting faces
	// etc)
	initTools();
}

// Load the mesh and grid from a TopoFixer instance
void TopoViewer::setTopoFixer(std::unique_ptr<SDTopoFixer> topofixer) {
	// Unload old data (if it exists)
	resetTopoFixer();
	// Remove test cube that is added by unloading
	removeTestCube();

	// Pause simulation
	topo_fixer_paused_ = true;

	// Save topo fixer
	topo_fixer_ = std::move(topofixer);

	enableTopoFixerTools();

	// Create geometry
	createGeometryVisualisation();

	// Reset camera
	resetCameraPosition();
}

void TopoViewer::createGeometryVisualisation() {
	// Mesh
	mesh_ = std::make_unique<LinearMesh3DView>(topo_fixer_->getMesh3DInterface());
	GeometryFactory factory(*mesh_, *(topo_fixer_->getGrid3DCubical()));

	// Make an instance of the mesh
	topo_mesh_ = factory.makeTriangleMesh(0.03f);
	topo_mesh_inst_ = scene_->addInstance(
	    std::make_unique<scene::TriangleMeshInstance>(topo_mesh_.get(), root_node_));
	topo_line_mesh_ = factory.makeLineMesh();
	topo_line_mesh_inst_ = scene_->addInstance(
	    std::make_unique<scene::LineMeshInstance>(topo_line_mesh_.get(), root_node_));
	topo_line_mesh_inst_->setLineWidth(1.5f);

	// Make an instance of the grid
	std::vector<long long> face_ids;
	factory.makeComplexCellSetBoundaryMeshes(&complex_mesh_, &complex_line_mesh_, &face_ids,
	                                         mesh_->numTriangles());
	complex_mesh_inst_ = scene_->addInstance(
	    std::make_unique<scene::TriangleMeshInstance>(complex_mesh_.get(), root_node_));
	complex_mesh_inst_->setFrontColor(Eigen::Vector3f(0.9f, 0.9f, 0.9f));
	complex_mesh_inst_->setBackColor(Eigen::Vector3f(0.75f, 0.75f, 0.75f));
	complex_mesh_inst_->setClippable(false);
	complex_line_mesh_inst_ = scene_->addInstance(
	    std::make_unique<scene::LineMeshInstance>(complex_line_mesh_.get(), root_node_));
	complex_line_mesh_inst_->setColor(Eigen::Vector3f(0.9f, 0.9f, 0.9f));
	complex_line_mesh_inst_->setLineWidth(1.5f);
	complex_line_mesh_inst_->setClippable(false);

	// Link mesh and grid up to the tools that need it
	visualization_tool_->setMeshes(topo_mesh_inst_, topo_line_mesh_inst_);
	visualization_tool_->setComplexGridMeshes(complex_mesh_inst_, complex_line_mesh_inst_);
	mesh_traversal_tool_->setMesh(*mesh_);
	grid_traversal_tool_->setGrid(*topo_fixer_->getGrid3DCubical(), std::move(face_ids),
	                              mesh_->numTriangles());

	// Compute approximate scene center and diameter (used for scaling camera movements)
	Vec3d bb_min3d, bb_max3d;
	topo_fixer_->getMesh3DInterface()->getMeshBounds(bb_min3d, bb_max3d);
	Eigen::Vector3d bb_min(bb_min3d[0], bb_min3d[1], bb_min3d[2]);
	Eigen::Vector3d bb_max(bb_max3d[0], bb_max3d[1], bb_max3d[2]);
	scene_center_ = (bb_max + bb_min) * 0.5;
	scene_diameter_ = (bb_max - bb_min).norm();
}

void TopoViewer::deleteGeometryVisualisation() {
	visualization_tool_->resetMeshes();
	visualization_tool_->resetComplexGridMeshes();
	mesh_traversal_tool_->resetMesh();
	grid_traversal_tool_->resetGrid();

	scene_->removeInstance(complex_line_mesh_inst_);
	complex_line_mesh_inst_ = nullptr;
	scene_->removeInstance(complex_mesh_inst_);
	complex_mesh_inst_ = nullptr;

	scene_->removeInstance(topo_mesh_inst_);
	topo_mesh_inst_ = nullptr;
	scene_->removeInstance(topo_line_mesh_inst_);
	topo_line_mesh_inst_ = nullptr;

	mesh_ = nullptr;
}

void TopoViewer::updateGeometryVisualisation() {
	// Save clipping plane
	VisualizationTool::ClippingPlane cp = visualization_tool_->getClippingPlane();
	deleteGeometryVisualisation();
	createGeometryVisualisation();
	visualization_tool_->setClippingPlane(cp);
}

void TopoViewer::resetTopoFixer() {
	// Unload everything
	disableTopoFixerTools();
	deleteGeometryVisualisation();
	topo_fixer_ = nullptr;

	addTestCube();
	resetCameraPosition();
}

void TopoViewer::runTopoFixer() {
	const TopoFixerSettings& settings = topo_fixer_->getSettings();
	if (settings.run_mode == TopoFixerSettings::RunMode::Fixer) {
		topo_fixer_->runFixer(settings.should_perturb_grid);
		topo_fixer_->clearNonMeshState();
		topo_fixer_paused_ = true;
		updateGeometryVisualisation();
		// Camera partially resets
	} else if (settings.run_mode == TopoFixerSettings::RunMode::Scene) {
		if (!topo_fixer_->isSimulationFinished()) {
			topo_fixer_->runSteps(settings.interactive_mode_steps);
			updateGeometryVisualisation();
		}
		const bool isFinished = topo_fixer_->isSimulationFinished();
		topo_fixer_paused_ = (topo_fixer_paused_ || isFinished);
		if (isFinished) {
			std::cout << "-Sim finished, pause ON" << std::endl;
		}
	}
}

// This runs a "game loop", which includes polling events from GLFW, drawing the user interface,
// doing the actual logic (like updating the scene graph transforms), and rendering the scene.
void TopoViewer::run() {
	bool show_another_window = true;
	bool first_iteration = true;

	while (!glfwWindowShouldClose(window_)) {
		// Queries GLFW events, and causes any code to fire in response to these events
		glfwPollEvents();

		// ImGui Boilerplate
		ImGui_ImplOpenGL3_NewFrame();
		ImGui_ImplGlfw_NewFrame();
		ImGui::NewFrame();

		// Display Zoom and command line responses at the top of the window
		if (ImGui::BeginMainMenuBar()) {
			double zoom = scene_->activeCamera()->zoom();
			int zoom_percent = static_cast<int>(100. / zoom);
			ImGui::Text("Zoom: %i%%", zoom_percent);
			if (!command_status_.empty()) {
				ImGui::SameLine();
				ImGui::Text("|");
				ImGui::SameLine();
				ImGui::Text("%s", command_status_.data());
			}
			ImGui::EndMainMenuBar();
		}

		// If the user pressed "Enter", open command window
		if (open_command_popup_) {
			open_command_popup_ = false;
			is_open_command_popup_ = true;
			ImGui::OpenPopup("Command Window");
		}

		// Put command popup in the center of the window
		ImVec2 center = ImGui::GetMainViewport()->GetCenter();
		ImGui::SetNextWindowPos(center, ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));

		if (ImGui::BeginPopupModal("Command Window", NULL, ImGuiWindowFlags_AlwaysAutoResize)) {
			ImGuiInputTextFlags input_text_flags = ImGuiInputTextFlags_EnterReturnsTrue;
			ImGui::SetKeyboardFocusHere();
			if (ImGui::InputTextWithHint("##CommandInputText", "Enter command", &command_string_,
			                             input_text_flags)) {
				// If the user pressed enter after typing something in the command window, fire the command
				// event and close the window
				trim(command_string_);
				CommandEvent event(command_string_);
				commandCallback(event, &command_status_);
				command_string_ = "";
				close_command_popup_ = true;
			}

			if (close_command_popup_) {
				ImGui::CloseCurrentPopup();
				is_open_command_popup_ = false;
			}

			ImGui::EndPopup();
		}
		close_command_popup_ = false;

		// Display status messages from the tools
		ImGui::Begin("Status");
		std::string status_string;
		getToolStatusString(&status_string);
		ImGui::Text("%s", status_string.data());
		ImGui::End();

		if (first_iteration) {
			ImGui::SetWindowFocus(NULL);
		}

		// Automatic run of the TopoFixer
		if (!topo_fixer_paused_) {
			runTopoFixer();
		}

		if (!ani_paused_) {
			animation_tool_->advanceFrame();
			if (animation_tool_->isLastFrame()) {
				std::cout << "Animation stopped." << std::endl;
				ani_paused_ = true;
			}
		}

		bool ani_updated = false;
		if (animation_tool_ != nullptr && animation_tool_->isEnabled()) {
			ani_updated = animation_tool_->pollUpdated();
		}

		if (ani_updated) {
			updateGeometryVisualisation();
		}

		// Render command for interface
		ImGui::Render();

		// Scene transform updates
		scene_->updateWorldTransform();
		coordinate_frame_overlay_scene_->mimicCamera(scene_->activeCameraNode());
		coordinate_frame_overlay_scene_->updateWorldTransform();

		// Render our stuff
		renderer_->render();

		const std::string& render_output_path = topo_fixer_->getSettings().render_output_path;
		bool should_render = !render_output_path.empty() && (!topo_fixer_paused_ || ani_updated);
		if (should_render) {
			std::filesystem::path basename;
			if (!topo_fixer_paused_) {
				basename = "out." + std::to_string(topo_fixer_->getCurrentStep()) + ".png";
			}
			if (ani_updated) {
				basename = "out." + std::to_string(animation_tool_->getCurrentFrame()) + ".png";
			}
			renderer_->saveFrameToDisk(std::filesystem::path(render_output_path) / basename);
		}

		// Boilerplate Imgui code
		ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

#ifndef NDEBUG
		GLenum err = glGetError();
		if (err != GL_NO_ERROR)
			std::cerr << "GL Error occurred!";
#endif

		// Switch back and front buffers to display stuff
		glfwSwapBuffers(window_);

		double t1 = glfwGetTime();
		first_iteration = false;
	}
}

void TopoViewer::getToolStatusString(std::string* status_string) {
	std::ostringstream oss;
	bool first = true;
	// Collect status report from all tools and concatenate
	for (const auto& tool : tools_) {
		const auto& tool_status = tool->getToolStatus();
		if (!tool_status.empty()) {
			if (!first) {
				oss << std::endl << std::endl;
			}
			first = false;
			oss << tool_status;
		}
	}
	*status_string = oss.str();
}

TopoViewer::~TopoViewer() {
	if (window_ != nullptr) {
		ImGui_ImplOpenGL3_Shutdown();
		ImGui_ImplGlfw_Shutdown();
		ImGui::DestroyContext();

		glfwDestroyWindow(window_);
	}

	if (glfw_initialized_)
		glfwTerminate();
}

void TopoViewer::clearSelection() {
	mesh_traversal_tool_->clearSelection();
	grid_traversal_tool_->clearSelection();
}

unsigned int TopoViewer::cursorIndex() const {
	if (renderer_) {
		return renderer_->cursorIndex();
	} else {
		return -1;
	}
}

// Store last world position of cursor in "pos", and return true iff this was
// done successfully
bool TopoViewer::cursorWorldPosition(Eigen::Vector3d* pos) const {
	if (renderer_) {
		float depth = renderer_->cursorDepth();
		if (depth != 1.0f) {
			*pos = renderer_->cursorWorldPosition();
			return true;
		} else {
			return false;
		}
	} else
		return false;
}

bool TopoViewer::cursorPixelPosition(Eigen::Vector2d* pos) const {
	*pos << last_xpos_, last_ypos_;
	return true;
}

void TopoViewer::createDefaultCamera(double ratio) {
	auto cam_node = scene_->addNode(std::make_unique<scene::Node>());
	scene_->setActiveCameraNode(cam_node);

	auto cam = std::make_unique<scene::PerspectiveCamera>(1.e-1, 1.e2, 3.14 / 3., ratio);
	default_camera_ = cam.get();
	scene_->addCamera(std::move(cam));
	scene_->setActiveCamera(default_camera_);
}

void TopoViewer::resetCameraPosition() {
	auto node = scene_->activeCameraNode();

	Eigen::Matrix3d cam_frame;
	Eigen::Vector3d cam_pos;

	getDefaultCameraLocation(&cam_pos, &cam_frame);

	node->setPosition(cam_pos);
	node->setFrame(cam_frame);
}

void TopoViewer::getDefaultCameraLocation(Eigen::Vector3d* position, Eigen::Matrix3d* frame) const {
	*frame << 0., 0., 1., 1., 0., 0., 0., 1., 0.;
	*position << 5., 0., 0.;

	if (mesh_) {
		Vec3d bb_min3d, bb_max3d;
		topo_fixer_->getMesh3DInterface()->getMeshBounds(bb_min3d, bb_max3d);
		Eigen::Vector3d bb_min(bb_min3d[0], bb_min3d[1], bb_min3d[2]);
		Eigen::Vector3d bb_max(bb_max3d[0], bb_max3d[1], bb_max3d[2]);
		Eigen::Vector3d center = (bb_max + bb_min) * 0.5;
		double half_diag = (bb_max - center).norm();
		*position = center + Eigen::Vector3d(half_diag * 5., 0., 0.);
	}
}

Eigen::Vector3d TopoViewer::sceneCenter() const {
	if (mesh_) {
		return scene_center_;
	} else {
		return Eigen::Vector3d::Zero();
	}
}

double TopoViewer::sceneDiameter() const {
	if (mesh_) {
		return scene_diameter_;
	} else {
		return 2.;
	}
}

void TopoViewer::addTestCube() {
	if (!test_cube_) {
		geom::Mesh<float> cylinder =
		    geom::MeshPrimitives<float>::getUnitCylinderIndexed(6, true, true, true, true);

		geom::Mesh<float> cube = geom::MeshPrimitives<float>::getUnitCubeTriangles(true, false);
		Eigen::Vector<GLuint, -1> cube_indices(36);
		Eigen::Matrix<float, 3, -1> front_colors(3, 36);
		Eigen::Matrix<float, 3, -1> back_colors(3, 36);
		for (unsigned int i = 0; i < 36; i++) {
			cube_indices(i) = i / 3;
			front_colors.col(i) << 0.1f + ((i / 3) / 12.f) * 0.8f, 0.0f, 0.0f;
			back_colors.col(i) << 0.0f, 0.1f + ((i / 3) / 12.f) * 0.8f, 0.0f;
		}

		test_cube_ = std::make_unique<gl::TriangleMesh>(cube.vertices);
		test_cube_->setIndices(cube_indices);
		test_cube_->setFrontColor(front_colors);
		test_cube_->setBackColor(back_colors);

		// Line Mesh
		geom::Mesh<float> cube_edges =
		    geom::MeshPrimitives<float>::getUnitCubeIndexed(true, false, true);

		test_cube_edges_ = std::make_unique<gl::LineMesh>(cube_edges.vertices, cube_edges.edges);
	}

	if (!test_cube_inst_) {
		test_cube_inst_ = scene_->addInstance(
		    std::make_unique<scene::TriangleMeshInstance>(test_cube_.get(), root_node_));
		test_cube_inst_->setFrontColor(Eigen::Vector3f(1.f, 1.f, 0.5f));

		test_cube_edges_inst_ = scene_->addInstance(
		    std::make_unique<scene::LineMeshInstance>(test_cube_edges_.get(), root_node_));
	}
}

void TopoViewer::removeTestCube() {
	if (test_cube_inst_) {
		scene_->removeInstance(test_cube_inst_);
		test_cube_inst_ = nullptr;
		scene_->removeInstance(test_cube_edges_inst_);
		test_cube_edges_inst_ = nullptr;
	}
}

GLFWwindow* TopoViewer::createDefaultWindow(int width, int height, float* content_scale) {
	glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
	glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);

	auto win = glfwCreateWindow(width, height, "Simple example", NULL, NULL);
	if (!win) {
		glfwTerminate();
		exit(EXIT_FAILURE);
	}

	glfwSetMouseButtonCallback(win, &TopoViewer::raw_mouseButtonCallback);
	glfwSetCursorPosCallback(win, &TopoViewer::raw_cursorCallback);
	glfwSetScrollCallback(win, &TopoViewer::raw_scrollCallback);
	glfwSetKeyCallback(win, &TopoViewer::raw_keyCallback);
	glfwSetWindowSizeCallback(win, &TopoViewer::raw_windowSizeCallback);

	glfwMakeContextCurrent(win);
	gladLoadGL();
	glfwSwapInterval(1);

	// Setup Dear ImGui context
	IMGUI_CHECKVERSION();
	ImGui::CreateContext();
	ImGuiIO& io = ImGui::GetIO();
	io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;  // Enable Keyboard Controls

	// Setup Dear ImGui style
	ImGui::StyleColorsDark();

	// Setup Platform/Renderer backends
	ImGui_ImplGlfw_InitForOpenGL(win, true);
	ImGui_ImplOpenGL3_Init();

	// Load font at correct scale
	float yscale;
	glfwGetWindowContentScale(win, content_scale, &yscale);
	io.Fonts->AddFontFromFileTTF("res/fonts/Roboto-Medium.ttf", std::ceil(14.0f * (*content_scale)));
	ImGui::GetStyle().ScaleAllSizes(*content_scale);

	return win;
}

void TopoViewer::initTools() {
	assert(scene_);

	// Add tool for controlling camera
	tools_.push_back(std::make_unique<logic::CameraTool>(this, scene_->activeCameraNode(),
	                                                     scene_->activeCamera()));
	// Add tool for cylcing between rendering modes (invisible, edge-only, face-only, edge+face) for
	// mesh and grid, and editing the clipping plane
	auto vistool = std::make_unique<logic::VisualizationTool>(this, renderer_.get());
	visualization_tool_ = vistool.get();
	tools_.push_back(std::move(vistool));

	// Add tool for traversing a half-face mesh
	auto travtool = std::make_unique<logic::MeshTraversalTool>(this, scene_.get(), root_node_);
	mesh_traversal_tool_ = travtool.get();
	tools_.push_back(std::move(travtool));

	// Add tool for traversing the different primitives of the grid
	auto gridtool = std::make_unique<logic::GridTraversalTool>(this, scene_.get(), root_node_);
	grid_traversal_tool_ = gridtool.get();
	tools_.push_back(std::move(gridtool));

	animation_tool_ = nullptr;
}

int TopoViewer::computeCoordinateFrameOverlaySceneSize() {
	double canvas_min_sz = std::min(canvas_width_, canvas_height_);
	double sz = std::max(100. * contentScale(), std::min(200. * contentScale(), 0.2 * canvas_min_sz));
	return static_cast<int>(sz);
}

void TopoViewer::enableTopoFixerTools() {
	const TopoFixerSettings& settings = topo_fixer_->getSettings();

	if (settings.run_mode == TopoFixerSettings::RunMode::Render) {
		if (animation_tool_ == nullptr) {
			std::filesystem::path mesh_path = topo_fixer_->getSettings().input_mesh_file;
			auto anitool = std::make_unique<logic::AnimationTool>(this, topo_fixer_->getMesh3DInterface(),
			                                                      mesh_path);
			animation_tool_ = anitool.get();
			tools_.push_back(std::move(anitool));
		} else {
			animation_tool_->setEnabled(true);
		}
	}
}

void TopoViewer::disableTopoFixerTools() {
	if (animation_tool_ == nullptr) {
		return;
	}
	animation_tool_->setEnabled(false);
}

void TopoViewer::cursorCallback(CursorEvent event) {
	// Cancel pending closing operation
	window_close_confirmation_ = false;
	renderer_->setCursorPosition(static_cast<int>(event.xpos), static_cast<int>(event.ypos));
	dispatchEventToTools(&Tool::cursorCallback, event);
}

void TopoViewer::mouseButtonCallback(MouseButtonEvent event) {
	// Cancel pending closing operation
	window_close_confirmation_ = false;
	dispatchEventToTools(&Tool::mouseButtonCallback, event);
}

void TopoViewer::scrollCallback(ScrollEvent event) {
	// Cancel pending closing operation
	window_close_confirmation_ = false;
	dispatchEventToTools(&Tool::scrollCallback, event);
}
void TopoViewer::keyCallback(KeyEvent event) {
	const bool tool_responded = dispatchEventToTools(&Tool::keyCallback, event);
	if (tool_responded || (event.action != GLFW_PRESS) || active_tool_) {
		return;
	}
	// Check closing
	const bool window_is_closing = window_close_confirmation_;
	window_close_confirmation_ = false;
	if (event.key == GLFW_KEY_ENTER) {
		open_command_popup_ = true;
	} else if (event.key == GLFW_KEY_S) {
		std::cout << "-Run steps" << std::endl;
		runTopoFixer();
	} else if (event.key == GLFW_KEY_P) {
		TopoFixerSettings::RunMode run_mode = topo_fixer_->getSettings().run_mode;
		if (run_mode == TopoFixerSettings::RunMode::Scene) {
			topo_fixer_paused_ = !topo_fixer_paused_;
			if (topo_fixer_paused_) {
				std::cout << "-Pause ON" << std::endl;
			} else {
				std::cout << "-Pause OFF" << std::endl;
			}
		}
		if (run_mode == TopoFixerSettings::RunMode::Render) {
			ani_paused_ = !ani_paused_;
			if (ani_paused_) {
				std::cout << "-Pause ON" << std::endl;
			} else {
				std::cout << "-Pause OFF" << std::endl;
			}
		}

	} else if (event.key == GLFW_KEY_ESCAPE) {
		if (!window_is_closing) {
			window_close_confirmation_ = true;
		} else {
			glfwSetWindowShouldClose(window_, GLFW_TRUE);
		}
	}
}

void TopoViewer::commandCallback(logic::CommandEvent event, std::string* command_status) {
	*command_status = "";
	if (active_tool_) {
		return;
	}

	// Offer the command to the tools until a tool is activated or performs an instant action
	for (auto& tool : tools_) {
		auto response = tool->commandCallback(event);
		if (response == logic::ToolResponse::Activate) {
			active_tool_ = tool.get();
			tool->getCommandStatus(command_status);
			return;
		} else if (response == logic::ToolResponse::InstantAction) {
			tool->getCommandStatus(command_status);
			return;
		}
	}

	// If no tool, check for centralized commands like (un)loading a scene.
	auto tokens = tokenize(event.command);
	if (tokens.size() == 0)
		return;

	if (tokens[0] == "unload") {
		if (tokens.size() > 1) {
			*command_status = "The unload command takes no parameters.";
			return;
		}
		resetTopoFixer();
		return;
	} else if (tokens[0] == "load") {
		if (tokens.size() != 2) {
			*command_status = "Usage of load command: load path";
			return;
		}
		auto new_topo_fixer = logic::loadFromFile(tokens[1]);
		if (new_topo_fixer) {
			setTopoFixer(std::move(new_topo_fixer));
		} else {
			*command_status = "File could not be loaded.";
		}
		return;
	} else {
		*command_status = "Command unknown.";
	}

	return;
}

void TopoViewer::windowSizeCallback(WindowSizeEvent event) {
	canvas_width_ = event.width;
	canvas_height_ = event.height;
	renderer_->windowResized(event.width, event.height);
	double ratio = static_cast<double>(event.width) / event.height;
	default_camera_->setProperties(-1, -1, -1, ratio);

	int sz_int = computeCoordinateFrameOverlaySceneSize();
	auto params = renderer_->overlaySceneParameters(coordinate_frame_overlay_scene_->scene());
	params->size << sz_int, sz_int;
}

void TopoViewer::raw_cursorCallback(GLFWwindow* window, double xpos, double ypos) {
	TopoViewer::event_window->last_xpos_ = xpos;
	TopoViewer::event_window->last_ypos_ = ypos;
	if (!ImGui::GetIO().WantCaptureMouse) {
		CursorEvent event(xpos, ypos);
		TopoViewer::event_window->cursorCallback(event);
	}
}

void TopoViewer::raw_mouseButtonCallback(GLFWwindow* window, int button, int action, int mods) {
	if (!ImGui::GetIO().WantCaptureMouse) {
		MouseButtonEvent event(button, action, mods, TopoViewer::event_window->last_xpos_,
		                       TopoViewer::event_window->last_ypos_);
		TopoViewer::event_window->mouseButtonCallback(event);
	}
}

void TopoViewer::raw_scrollCallback(GLFWwindow* window, double xoffset, double yoffset) {
	if (!ImGui::GetIO().WantCaptureMouse) {
		ScrollEvent event(xoffset, yoffset);
		TopoViewer::event_window->scrollCallback(event);
	}
}

void TopoViewer::raw_keyCallback(GLFWwindow* window, int key, int scancode, int action, int mods) {
	if ((action == GLFW_PRESS) && (key == GLFW_KEY_ESCAPE) &&
	    (event_window->is_open_command_popup_)) {
		event_window->close_command_popup_ = true;
	} else if (!ImGui::GetIO().WantCaptureKeyboard) {
		KeyEvent event(key, scancode, action, mods);
		TopoViewer::event_window->keyCallback(event);
	}
}

void TopoViewer::raw_windowSizeCallback(GLFWwindow* window, int width, int height) {
	WindowSizeEvent event(width, height);
	TopoViewer::event_window->windowSizeCallback(event);
}

void TopoViewer::raw_errorCallback(int error, const char* description) {
	fprintf(stderr, "GLFW Error: %s\n", description);
}

TopoViewer* TopoViewer::event_window = nullptr;

}  // namespace sdtf::viewer
