#pragma once

#include <Eigen/Core>
#include <utility>
#include <list>

#include "gl/Framebuffer.h"
#include "gl/Program.h"
#include "scene/Scene.h"

// General purpose OpenGL renderer
// Renders triangles meshes, line meshes, and overlay meshes (which are triangle meshes with a
// dithering pattern) Triangle meshes with an index buffer can be used to indentify the index of an
// element below the mouse cursor. Supports a single clipping plane for the triangle meshes and line
// meshes that have the clipping option enabled. Also supports overlay scenes, which will be
// rendered on the specified portion of the screen, on top of the main scene (used for the little
// coordinate frame in the corner).

namespace sdtf::viewer::logic {
;

class Renderer {
 public:
	Renderer(int width, int height, int num_msaa_samples, const scene::Scene* scene);

	// Called by the main application to resize framebuffers
	void windowResized(int width, int height);

	// Call once per rendering loop iteration
	void render();
	// Saves pixels from the render buffer to disk in PNG format. Does not perform rendering by
	// itself.
	void saveFrameToDisk(const std::string& path);

	auto backgroundColor() const { return background_color_; }
	void setBackgroundColor(Eigen::Vector3f bg) { background_color_ = bg; }

	// Set the clipping plane so only points with world coordinates x that satisfy
	//   <x - point, inside_direction> >= 0
	// will be visible.
	void setClippingPlane(Eigen::Vector3d point, Eigen::Vector3d inside_direction);
	void resetClippingPlane();

	// Call from the application to indicate the current mouse cursor position. This will tell the
	// renderer at which location to read back the scene index and depth to reconstruct the world
	// position of the point below the mouse cursor.
	void setCursorPosition(int x, int y);
	// Disable the functionality to read back the data below the mouse cursor (until setCursorPosition
	// is called again).
	void disableReadIndex();

	// Read back data below the mouse cursor
	unsigned int cursorIndex() const { return cursor_index_; }
	float cursorDepth() const { return cursor_depth_; }
	Eigen::Vector3d cursorWorldPosition() const { return cursor_world_pos_; }

	// The content scale represents the scaling up of everything desired by the OS (e.g. for high-DPI
	// displays). The renderer uses this to scale up the line widths for line drawing.
	void setContentScale(double scale) { content_scale_ = scale; }

	// Represents the location of an overlay scene in pixels
	struct OverlaySceneParameters {
		Eigen::Vector<GLint, 2> bottom_left;
		Eigen::Vector<GLsizei, 2> size;
	};

	void addOverlayScene(const scene::Scene* scene, OverlaySceneParameters parameters);
	OverlaySceneParameters* overlaySceneParameters(const scene::Scene* scene);
	const OverlaySceneParameters* overlaySceneParameters(const scene::Scene* scene) const;

 private:
	void initFramebuffers();
	void initPrograms();  // init shader programs

	void renderSceneClickable(const scene::Scene* scene);
	void renderSceneNonClickable(const scene::Scene* scene);
	void renderTriangleMesh(const scene::TriangleMeshInstance& mesh,
	                        const Eigen::Matrix4d& vp_matrix);
	void renderLineMesh(const scene::LineMeshInstance& inst, const Eigen::Matrix4d& vp_matrix);
	void renderOverlayMesh(const scene::OverlayMeshInstance& inst, const Eigen::Matrix4d& vp_matrix);

	void computeCursorWorldPosition();
	void resizeCanvas();

	void flipFrameForPNG(std::vector<uint8_t>& image, int width, int height, int chan);

	Eigen::Vector3f background_color_ = Eigen::Vector3f(0.5f, 0.5f, 0.5f);

	std::unique_ptr<gl::Framebuffer> main_framebuffer_;
	std::unique_ptr<gl::Texture> color_tex_, depth_tex_, index_tex_;
	std::unique_ptr<gl::Framebuffer> single_index_framebuffer_;
	std::unique_ptr<gl::Texture> single_index_tex_, single_depth_tex_;

	std::unique_ptr<gl::Program> triangle_mesh_program_;
	struct {
		GLint mvp_matrix;
		GLint model_matrix;
		GLint clipping_plane;
		GLint angle_attenuation;
		GLint world_camera;
	} triangle_mesh_program_ul_;
	std::unique_ptr<gl::Program> line_mesh_program_;
	struct {
		GLint mvp_matrix;
		GLint model_matrix;
		GLint clipping_plane;
	} line_mesh_program_ul_;
	std::unique_ptr<gl::Program> overlay_mesh_program_;
	struct {
		GLint mvp_matrix;
		GLint model_matrix;
		GLint color;
		GLint pattern_front;
		GLint pattern_back;
		GLint clipping_plane;
	} overlay_mesh_program_ul_;

	const scene::Scene* scene_ = nullptr;
	Eigen::Vector4f clipping_plane_ = Eigen::Vector4f(0., 0., 0., 1.);

	std::list<std::pair<const scene::Scene*, OverlaySceneParameters>> overlay_scenes_;

	const int num_msaa_samples_;
	int canvas_width_, canvas_height_;
	bool canvas_resized_ = false;
	double content_scale_ = 1.0;

	bool read_index_enabled_ = false;
	int cursor_x_, cursor_y_;
	unsigned int cursor_index_ = -1;
	float cursor_depth_ = 0.0;
	Eigen::Vector3d cursor_world_pos_;
};

}  // namespace sdtf::viewer::logic