#pragma once

#include "datastructures/Grid3DInterface.h"
#include "datastructures/Mesh3DInterface.h"
#include "gl/LineMesh.h"
#include "gl/TriangleMesh.h"
#include "logic/AnimationTool.h"
#include "logic/CoordinateFrameOverlayScene.h"
#include "logic/GridTraversalTool.h"
#include "logic/LinearMesh3DView.h"
#include "logic/MeshTraversalTool.h"
#include "logic/Renderer.h"
#include "logic/Tool.h"
#include "logic/ViewerInterface.h"
#include "logic/VisualizationTool.h"
#include "logic/events.h"
#include "scene/LineMeshInstance.h"
#include "scene/Scene.h"
#include "scene/TriangleMeshInstance.h"
#include "schemes/SDTopoFixer.h"

struct GLFWwindow;

// Central logic and user interface of the TopoViewer application
// Displays a window in which to view the mesh and grid from the TopoFixer
// application, move around a camera, play with selections etc

namespace sdtf::viewer {
;

class TopoViewer : public logic::ViewerInterface {
 public:
	TopoViewer(int width, int height, int num_msaa_samples);
	~TopoViewer();

	// Load the mesh and grid from an instance of the TopoFixer
	void setTopoFixer(std::unique_ptr<SDTopoFixer> topofixer);
	// Unload all data
	void resetTopoFixer();
	// Call this function to open the application and run the user interface loop
	void run();

	// content scale of the application for high DPI monitors
	virtual float contentScale() const override { return content_scale_; }
	// query the index of the object below the mouse cursor from the renderer
	virtual unsigned int cursorIndex() const override;
	// last known point below the cursor in world position
	virtual bool cursorWorldPosition(Eigen::Vector3d* pos) const override;
	// last known (x,y) position of the cursor in pixel units
	virtual bool cursorPixelPosition(Eigen::Vector2d* pos) const override;
	// main scene which is displayed by the renderer
	virtual const scene::Scene* scene() const override { return scene_.get(); }
	// width of the main framebuffer
	virtual double canvasWidth() const override { return canvas_width_; }
	// height of the main framebuffer
	virtual double canvasHeight() const override { return canvas_height_; }
	// query the default position and orientation of the camera
	virtual void getDefaultCameraLocation(Eigen::Vector3d* position,
	                                      Eigen::Matrix3d* frame) const override;
	// approximate center of the scene (e.g. midpoint of bounding box)
	virtual Eigen::Vector3d sceneCenter() const override;
	// approximate diameter of scene (e.g. diagonal of bounding box)
	virtual double sceneDiameter() const override;
	// clear selection in grid and mesh
	virtual void clearSelection() override;

 private:
	GLFWwindow* window_ = nullptr;
	bool window_close_confirmation_ = false;
	bool glfw_initialized_ = false;
	float content_scale_ = 1.0;
	std::unique_ptr<scene::Scene> scene_;
	std::unique_ptr<logic::Renderer> renderer_;
	std::unique_ptr<logic::CoordinateFrameOverlayScene> coordinate_frame_overlay_scene_;

	std::unique_ptr<SDTopoFixer> topo_fixer_ = nullptr;
	// Call the topo fixer to update the mesh
	void runTopoFixer();
	// Starts paused
	bool topo_fixer_paused_ = true;
	bool ani_paused_ = true;

	std::unique_ptr<logic::LinearMesh3DView> mesh_ = nullptr;
	Eigen::Vector3d scene_center_;
	double scene_diameter_;

	// Tools
	std::vector<std::unique_ptr<logic::Tool>> tools_;
	logic::VisualizationTool* visualization_tool_;
	logic::MeshTraversalTool* mesh_traversal_tool_;
	logic::GridTraversalTool* grid_traversal_tool_;
	logic::AnimationTool* animation_tool_;
	logic::Tool* active_tool_ = nullptr;
	bool open_command_popup_ = false;
	bool is_open_command_popup_ = false;
	bool close_command_popup_ = false;
	std::string command_string_ = "";
	std::string command_status_ = "";

	double last_xpos_ = 0.0, last_ypos_ = 0.0;
	double canvas_width_ = 0.0, canvas_height_ = 0.0;

	scene::PerspectiveCamera* default_camera_;

	scene::Node* root_node_;
	std::unique_ptr<gl::TriangleMesh> test_cube_;
	scene::TriangleMeshInstance* test_cube_inst_ = nullptr;
	std::unique_ptr<gl::LineMesh> test_cube_edges_;
	scene::LineMeshInstance* test_cube_edges_inst_ = nullptr;

	void createGeometryVisualisation();
	void deleteGeometryVisualisation();
	void updateGeometryVisualisation();
	// Mesh visualization
	std::unique_ptr<gl::TriangleMesh> topo_mesh_ = nullptr;
	scene::TriangleMeshInstance* topo_mesh_inst_ = nullptr;
	std::unique_ptr<gl::LineMesh> topo_line_mesh_ = nullptr;
	scene::LineMeshInstance* topo_line_mesh_inst_ = nullptr;

	// Complex cell set visualization
	std::unique_ptr<gl::TriangleMesh> complex_mesh_ = nullptr;
	scene::TriangleMeshInstance* complex_mesh_inst_ = nullptr;
	std::unique_ptr<gl::LineMesh> complex_line_mesh_ = nullptr;
	scene::LineMeshInstance* complex_line_mesh_inst_ = nullptr;

	// Boilerplate code for creating GLFW window with OpenGL context, initializing ImGui, loading
	// fonts
	static GLFWwindow* createDefaultWindow(int width, int height, float* content_scale);
	// Create a node with a camera and activate it in the seen
	void createDefaultCamera(double ratio);
	// Instantiate all user interaction tool (for controlling the camera, selecting faces in the
	// grid/mesh etc)
	void initTools();
	// Add a cube to the scene as a rendering test (calling it while a test cube is active has no
	// effect)
	void addTestCube();
	// Remove the test cube added by addTestCube()
	void removeTestCube();

	// Returns a concatenation of all status messages provided by tools
	void getToolStatusString(std::string* status_string);

	// Set the current camera location to the default camera location
	void resetCameraPosition();
	// Gives a suitable size (in pixels) that the coordinate frame overlay should occupy in the
	// window, scaled to be easily visible but not to occlude too much of the main scene
	int computeCoordinateFrameOverlaySceneSize();

	void enableTopoFixerTools();
	void disableTopoFixerTools();

	// Event callbacks, which are distributed to tools
	void cursorCallback(logic::CursorEvent event);
	void mouseButtonCallback(logic::MouseButtonEvent event);
	void scrollCallback(logic::ScrollEvent event);
	void keyCallback(logic::KeyEvent event);
	void windowSizeCallback(logic::WindowSizeEvent event);
	void commandCallback(logic::CommandEvent event, std::string* command_status);

	static TopoViewer* event_window;

	// Glue between GLFW callback syntax and the callbacks of the application
	// Note: These are static, and redirect the callbacks to the "event_window", which is
	// set to most recently created TopoViewer instance. Therefore, one should only
	// create one TopoViewer instance within an application.
	static void raw_cursorCallback(GLFWwindow* window, double xpos, double ypos);
	static void raw_mouseButtonCallback(GLFWwindow* window, int button, int action, int mods);
	static void raw_windowSizeCallback(GLFWwindow* window, int width, int height);
	static void raw_errorCallback(int error, const char* description);
	static void raw_scrollCallback(GLFWwindow* window, double xoffset, double yoffset);
	static void raw_keyCallback(GLFWwindow* window, int key, int scancode, int action, int mods);

	// Template function distributing an event of a certain type to the corresponding callback
	// function of the tools. If there is an active tool, only this tool will receive the event.
	// Otherwise, the event is offered to all tools in sequence until one tool is activatived
	// by the event.
	template <typename F, typename A>
	bool dispatchEventToTools(F event_func, A event_arg) {
		if (active_tool_) {
			auto response = (active_tool_->*event_func)(event_arg);
			if (response == logic::ToolResponse::Deactivate)
				active_tool_ = nullptr;
			return true;
		} else {
			for (auto& tool : tools_) {
				auto response = (tool.get()->*event_func)(event_arg);
				if (response == logic::ToolResponse::Activate) {
					active_tool_ = tool.get();
					return true;
				}
			}
			return false;
		}
	}
};

}  // namespace sdtf::viewer
