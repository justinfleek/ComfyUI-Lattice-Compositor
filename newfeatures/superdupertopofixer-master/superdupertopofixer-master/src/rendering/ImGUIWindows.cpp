#include "ImGUIWindows.h"

#include "OpenGLRenderer.h"
#include "imgui.h"

void ImGUIWindows::init() const {
	IMGUI_CHECKVERSION();
	ImGui::CreateContext();
	ImGuiIO& io = ImGui::GetIO();
	(void)io;
	io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;  // Enable Keyboard Controls

	// Setup Dear ImGui style
	ImGui::StyleColorsDark();
	// ImGui::StyleColorsClassic();

	// Setup Platform/Renderer backends
	ImGui_ImplGLUT_Init();
	ImGui_ImplOpenGL2_Init();
}

void ImGUIWindows::renderWindows() const {
	ImGui_ImplOpenGL2_NewFrame();
	ImGui_ImplGLUT_NewFrame();
	ImGui::Begin("Grids are greater!");

	ImGui::Text("Complex cell state:");
	ImGui::SliderInt("##complex_cell_visualizer",
	                 &OpenGLRenderer::old_complex_cell_visualizer.current_state_, 0,
	                 OpenGLRenderer::old_complex_cell_visualizer.kMaxStates - 1);
	ImGui::Text("Mesh smoothing");
	ImGui::SliderFloat("##mesh_smoothing_visualizer", &OpenGLRenderer::smoothing_visualizer.alpha_, 0,
	                   1);

	renderGridElementsControls();

	ImGui::Text("Mesh transparency:");
	ImGui::SliderFloat("##selection_colorizer_alpha", &OpenGLRenderer::selection_colorizer.alpha_, 0,
	                   1);

	renderDebugTree();

	ImGui::Text("Velocity scale:");
	float* velocity_scale = &OpenGLRenderer::value_transferrer_visualizer.velocity_scale_;
	ImGui::SliderFloat("##velocity_scale", velocity_scale, 0.0, 1.0);

	ImGui::Text("Nonmanifold edges:");
	ImGui::SameLine();
	ImGui::Checkbox("##nonmanifold", &OpenGLRenderer::nonmanifold_edge_visualizer.enabled_);

	ImGui::End();

	// Rendering
	ImGui::Render();
	// glUseProgram(0); // You may want this if using this code in an OpenGL 3+ context where
	// shaders may be bound, but prefer using the GL3+ code.
	ImGui_ImplOpenGL2_RenderDrawData(ImGui::GetDrawData());
}

void ImGUIWindows::reshape(int w, int h) const { ImGui_ImplGLUT_ReshapeFunc(w, h); }

void ImGUIWindows::keyboard(char c, int x, int y) const { ImGui_ImplGLUT_KeyboardFunc(c, x, y); }

void ImGUIWindows::mouse(int button, int state, int x, int y) const {
	ImGui_ImplGLUT_MouseFunc(button, state, x, y);
}

void ImGUIWindows::motion(int x, int y) const { ImGui_ImplGLUT_MotionFunc(x, y); }
void ImGUIWindows::passiveMotion(int x, int y) const { ImGui_ImplGLUT_MotionFunc(x, y); }

void ImGUIWindows::renderGridElementsControls() const {
	if (ImGui::TreeNode("Grid Elements")) {
		int* grid_state = &OpenGLRenderer::grid_mode;
		ImGui::RadioButton("Nothing", grid_state, 0);
		ImGui::RadioButton("Just grid", grid_state, 1);

		ImGui::RadioButton("Cell", grid_state, 2);
		long long cell_id = OpenGLRenderer::grid3DC->get_cell_id(
		    OpenGLRenderer::cell_x, OpenGLRenderer::cell_y, OpenGLRenderer::cell_z);
		ImGui::SameLine();
		ImGui::Text(":%lld", cell_id);
		ImGui::PushItemWidth(75);
		ImGui::InputInt("x##cell", &OpenGLRenderer::cell_x);
		ImGui::SameLine();
		ImGui::InputInt("y##cell", &OpenGLRenderer::cell_y);
		ImGui::SameLine();
		ImGui::InputInt("z##cell", &OpenGLRenderer::cell_z);
		ImGui::PopItemWidth();

		ImGui::RadioButton("Vertex", grid_state, 3);
		long long vertex_id = OpenGLRenderer::grid3DC->get_vertex_id(
		    OpenGLRenderer::vert_x, OpenGLRenderer::vert_y, OpenGLRenderer::vert_z);
		ImGui::SameLine();
		ImGui::Text(":%lld", vertex_id);
		ImGui::PushItemWidth(75);
		ImGui::InputInt("x##vertex", &OpenGLRenderer::vert_x);
		ImGui::SameLine();
		ImGui::InputInt("y##vertex", &OpenGLRenderer::vert_y);
		ImGui::SameLine();
		ImGui::InputInt("z##vertex", &OpenGLRenderer::vert_z);
		ImGui::PopItemWidth();

		ImGui::RadioButton("Edge", grid_state, 4);
		long long edge_id =
		    OpenGLRenderer::grid3DC->get_edge_id(OpenGLRenderer::edge_x, OpenGLRenderer::edge_y,
		                                         OpenGLRenderer::edge_z, OpenGLRenderer::edge_orient);
		ImGui::SameLine();
		ImGui::Text(":%lld", edge_id);
		ImGui::PushItemWidth(75);
		ImGui::InputInt("x##edge", &OpenGLRenderer::edge_x);
		ImGui::SameLine();
		ImGui::InputInt("y##edge", &OpenGLRenderer::edge_y);
		ImGui::SameLine();
		ImGui::InputInt("z##edge", &OpenGLRenderer::edge_z);
		ImGui::SameLine();
		ImGui::InputInt("o##edge", &OpenGLRenderer::edge_orient);
		ImGui::PopItemWidth();

		ImGui::RadioButton("Face", grid_state, 5);
		long long face_id =
		    OpenGLRenderer::grid3DC->get_face_id(OpenGLRenderer::face_x, OpenGLRenderer::face_y,
		                                         OpenGLRenderer::face_z, OpenGLRenderer::face_orient);
		ImGui::SameLine();
		ImGui::Text(":%lld", face_id);
		ImGui::PushItemWidth(75);
		ImGui::InputInt("x##face", &OpenGLRenderer::face_x);
		ImGui::SameLine();
		ImGui::InputInt("y##face", &OpenGLRenderer::face_y);
		ImGui::SameLine();
		ImGui::InputInt("z##face", &OpenGLRenderer::face_z);
		ImGui::SameLine();
		ImGui::InputInt("o##face", &OpenGLRenderer::face_orient);
		ImGui::PopItemWidth();

		ImGui::RadioButton("V to V", grid_state, 6);
		ImGui::TreePop();
	}
}

void ImGUIWindows::renderDebugTree() const {
	if (ImGui::TreeNode("Debug controls (can crash program)")) {
		int* separation_state = &OpenGLRenderer::cell_separation_colorizer.current_state_;
		ImGui::RadioButton("None##sep_none", separation_state, 0);
		ImGui::SameLine();
		ImGui::RadioButton("Inside tris##sep_inside", separation_state, 1);
		ImGui::SameLine();
		ImGui::RadioButton("Outside##sep_outside", separation_state, 2);
		renderIntersectionElementsTree();
		ImGui::TreePop();
	}
}

void ImGUIWindows::renderIntersectionElementsTree() const {
	if (ImGui::TreeNode("Intersection elements")) {
		int* element_state = &OpenGLRenderer::intersection_elements_visualizer.current_state_;
		ImGui::RadioButton("None##sep_none", element_state, 0);
		ImGui::SameLine();
		ImGui::RadioButton("G. edge <-> M. face", element_state, 1);
		ImGui::SameLine();
		ImGui::RadioButton("G. face <-> M. edge", element_state, 2);
		ImGui::InputInt("Direction",
		                &OpenGLRenderer::intersection_elements_visualizer.current_direction_);
		ImGui::TreePop();
	}
}
