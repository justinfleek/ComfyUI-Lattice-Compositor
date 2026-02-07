#include "Renderer.h"

#include <Eigen/Dense>
#include <array>
#include <cmath>
#include <fstream>
#include <iostream>

#include "utilities/fpng/fpng.h"

namespace sdtf::viewer::logic {
;

Renderer::Renderer(int width, int height, int num_msaa_samples, const scene::Scene* scene)
    : canvas_width_(width),
      canvas_height_(height),
      num_msaa_samples_(num_msaa_samples),
      scene_(scene) {
	initFramebuffers();
	initPrograms();
	fpng::fpng_init();
}

void Renderer::windowResized(int width, int height) {
	// std::cout << "window resized" << std::endl;
	if (canvas_width_ != width || canvas_height_ != height) {
		canvas_width_ = width;
		canvas_height_ = height;
		canvas_resized_ = true;
	}
}

void Renderer::resizeCanvas() {
	color_tex_->resize(canvas_width_, canvas_height_);
	depth_tex_->resize(canvas_width_, canvas_height_);
	index_tex_->resize(canvas_width_, canvas_height_);

	// std::cout << "Resized: " << canvas_width_ << ", " << canvas_height_ << std::endl;
}

void Renderer::initFramebuffers() {
	GLsizei width = static_cast<GLsizei>(canvas_width_);
	GLsizei height = static_cast<GLsizei>(canvas_height_);
	color_tex_ = gl::Texture::makeBasic2DMultisample(width, height, GL_RGBA8, num_msaa_samples_);
	depth_tex_ =
	    gl::Texture::makeBasic2DMultisample(width, height, GL_DEPTH_COMPONENT32, num_msaa_samples_);
	index_tex_ = gl::Texture::makeBasic2DMultisample(width, height, GL_R32UI, num_msaa_samples_);

	// Main Framebuffer with color, depth, and index buffers
	main_framebuffer_ = std::make_unique<gl::Framebuffer>();
	main_framebuffer_->attach(color_tex_.get(), GL_COLOR_ATTACHMENT0);
	main_framebuffer_->attach(index_tex_.get(), GL_COLOR_ATTACHMENT1);
	main_framebuffer_->attach(depth_tex_.get(), GL_DEPTH_ATTACHMENT);

	std::array<GLenum, 2> draw_buffers{GL_COLOR_ATTACHMENT0, GL_COLOR_ATTACHMENT1};
	glNamedFramebufferDrawBuffers(main_framebuffer_->name(), 2, draw_buffers.data());

	GLenum fb_status = glCheckNamedFramebufferStatus(main_framebuffer_->name(), GL_DRAW_FRAMEBUFFER);
	if (fb_status != GL_FRAMEBUFFER_COMPLETE)
		std::cout << "Framebuffer not complete!" << std::endl;

	// Single-index FBO
	single_index_tex_ = gl::Texture::makeBasic2D(1, 1, GL_R32UI, GL_RED_INTEGER);
	single_depth_tex_ = gl::Texture::makeBasic2D(1, 1, GL_DEPTH_COMPONENT32, GL_DEPTH_COMPONENT);
	single_index_framebuffer_ = std::make_unique<gl::Framebuffer>();
	single_index_framebuffer_->attach(single_index_tex_.get(), GL_COLOR_ATTACHMENT0);
	single_index_framebuffer_->attach(single_depth_tex_.get(), GL_DEPTH_ATTACHMENT);

	glNamedFramebufferDrawBuffer(single_index_framebuffer_->name(), GL_COLOR_ATTACHMENT0);
	glNamedFramebufferReadBuffer(single_index_framebuffer_->name(), GL_COLOR_ATTACHMENT0);

	fb_status = glCheckNamedFramebufferStatus(single_index_framebuffer_->name(), GL_DRAW_FRAMEBUFFER);
	if (fb_status != GL_FRAMEBUFFER_COMPLETE)
		std::cout << "Framebuffer not complete!" << std::endl;
}

void Renderer::initPrograms() {
	triangle_mesh_program_ = gl::Program::makeStandard(
	    "Triangle Mesh Program", "res/shaders/triangle-mesh.vert", "res/shaders/triangle-mesh.frag");
	triangle_mesh_program_->link();
	triangle_mesh_program_ul_.mvp_matrix = triangle_mesh_program_->getUniformLocation("mvp_matrix");
	triangle_mesh_program_ul_.model_matrix =
	    triangle_mesh_program_->getUniformLocation("model_matrix");
	triangle_mesh_program_ul_.clipping_plane =
	    triangle_mesh_program_->getUniformLocation("clipping_plane");
	triangle_mesh_program_ul_.angle_attenuation =
	    triangle_mesh_program_->getUniformLocation("angle_attenuation");
	triangle_mesh_program_ul_.world_camera =
	    triangle_mesh_program_->getUniformLocation("world_camera");

	line_mesh_program_ = gl::Program::makeStandard("Line Mesh Program", "res/shaders/line-mesh.vert",
	                                               "res/shaders/line-mesh.frag");
	line_mesh_program_->link();
	line_mesh_program_ul_.mvp_matrix = line_mesh_program_->getUniformLocation("mvp_matrix");
	line_mesh_program_ul_.model_matrix = line_mesh_program_->getUniformLocation("model_matrix");
	line_mesh_program_ul_.clipping_plane = line_mesh_program_->getUniformLocation("clipping_plane");

	overlay_mesh_program_ = gl::Program::makeStandard(
	    "Overlay Mesh Program", "res/shaders/overlay-mesh.vert", "res/shaders/overlay-mesh.frag");
	overlay_mesh_program_->link();
	overlay_mesh_program_ul_.mvp_matrix = overlay_mesh_program_->getUniformLocation("mvp_matrix");
	overlay_mesh_program_ul_.model_matrix = overlay_mesh_program_->getUniformLocation("model_matrix");
	overlay_mesh_program_ul_.color = overlay_mesh_program_->getUniformLocation("color");
	overlay_mesh_program_ul_.pattern_front =
	    overlay_mesh_program_->getUniformLocation("pattern_front");
	overlay_mesh_program_ul_.pattern_back = overlay_mesh_program_->getUniformLocation("pattern_back");
	overlay_mesh_program_ul_.clipping_plane =
	    overlay_mesh_program_->getUniformLocation("clipping_plane");
}

void Renderer::render() {
	if (canvas_resized_) {
		resizeCanvas();
		canvas_resized_ = false;
	}

	glViewport(0, 0, canvas_width_, canvas_height_);
	glEnable(GL_DEPTH_TEST);
	glEnable(GL_CLIP_DISTANCE0);

	// Clear depth buffer
	glBindFramebuffer(GL_DRAW_FRAMEBUFFER, main_framebuffer_->name());
	glClear(GL_DEPTH_BUFFER_BIT);

	// Clear color buffer & index buffer of main framebuffer
	Eigen::Vector4f bg_color;
	bg_color << background_color_, 1.0f;
	glClearBufferfv(GL_COLOR, 0, bg_color.data());
	GLuint clear_index = -1;
	glClearBufferuiv(GL_COLOR, 1, &clear_index);

	// Render stuff that the user can click on
	bool camera_ok = scene_->isCameraComplete();
	Eigen::Matrix4d vp_matrix;
	if (camera_ok) {
		renderSceneClickable(scene_);
	}

	// Read the index of the pixel under the mouse cursor
	if (read_index_enabled_) {
		int px = cursor_x_;
		int py = canvas_height_ - 1 - cursor_y_;
		glBindFramebuffer(GL_READ_FRAMEBUFFER, main_framebuffer_->name());
		glReadBuffer(GL_COLOR_ATTACHMENT1);
		glBindFramebuffer(GL_DRAW_FRAMEBUFFER, single_index_framebuffer_->name());
		glBlitFramebuffer(px, py, px + 1, py + 1, 0, 0, 1, 1, GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT,
		                  GL_NEAREST);
		glBindFramebuffer(GL_READ_FRAMEBUFFER, single_index_framebuffer_->name());
		glReadPixels(0, 0, 1, 1, GL_RED_INTEGER, GL_UNSIGNED_INT, &cursor_index_);
		glReadPixels(0, 0, 1, 1, GL_DEPTH_COMPONENT, GL_FLOAT, &cursor_depth_);

		computeCursorWorldPosition();
	} else {
		cursor_index_ = -1;
		cursor_depth_ = 1.0f;
	}

	// Render the rest
	glBindFramebuffer(GL_DRAW_FRAMEBUFFER, main_framebuffer_->name());
	if (camera_ok) {
		renderSceneNonClickable(scene_);
	}

	// Render overlay scenes
	if (!overlay_scenes_.empty()) {
		glDisable(GL_CLIP_DISTANCE0);
		glEnable(GL_SCISSOR_TEST);
		for (const auto& pair : overlay_scenes_) {
			auto scene = pair.first;
			if (scene->isCameraComplete()) {
				const auto& params = pair.second;
				glScissor(params.bottom_left(0), params.bottom_left(1), params.size(0), params.size(1));
				glClear(GL_DEPTH_BUFFER_BIT);

				glViewport(params.bottom_left(0), params.bottom_left(1), params.size(0), params.size(1));

				renderSceneClickable(scene);
				renderSceneNonClickable(scene);
			}
		}
		glDisable(GL_SCISSOR_TEST);
	}

	// Blit anti-aliased color buffer of main framebuffer to default framebuffer
	glBindFramebuffer(GL_READ_FRAMEBUFFER, main_framebuffer_->name());
	glReadBuffer(GL_COLOR_ATTACHMENT0);
	glBindFramebuffer(GL_DRAW_FRAMEBUFFER, 0);
	glBlitFramebuffer(0, 0, canvas_width_, canvas_height_, 0, 0, canvas_width_, canvas_height_,
	                  GL_COLOR_BUFFER_BIT, GL_NEAREST);

	// Bind default framebuffer for ImGui to render.
	glBindFramebuffer(GL_FRAMEBUFFER, 0);
}

void Renderer::saveFrameToDisk(const std::string& path) {
	std::ofstream out(path, std::ios::binary);

	if (!out.is_open()) {
		std::cout << "Error opening file: " << path << " for writing." << std::endl;
	}

	// Needs 4 components for aligned reads, i.e. * 3 and GL_BGR did not work.
	std::vector<uint8_t> image;
	int num_channels = 3;
	image.resize(canvas_width_ * canvas_height_ * 4);
	glReadPixels(0, 0, canvas_width_, canvas_height_, GL_RGBA, GL_UNSIGNED_BYTE, image.data());

	for (size_t pack_id = 1; pack_id < canvas_width_ * canvas_height_; ++pack_id) {
		image[3 * pack_id + 0] = image[4 * pack_id + 0];
		image[3 * pack_id + 1] = image[4 * pack_id + 1];
		image[3 * pack_id + 2] = image[4 * pack_id + 2];
	}
	flipFrameForPNG(image, canvas_width_, canvas_height_, num_channels);

	std::vector<uint8_t> out_buf;
	if (!fpng::fpng_encode_image_to_memory(image.data(), canvas_width_, canvas_height_, num_channels,
	                                       out_buf)) {
		std::cout << "Error during png conversion." << std::endl;
		out.close();
		return;
	}

	out.write(reinterpret_cast<char*>(out_buf.data()), sizeof(uint8_t) * out_buf.size());
	out.close();
}

void Renderer::computeCursorWorldPosition() {
	int px = cursor_x_;
	int py = canvas_height_ - 1 - cursor_y_;

	Eigen::Vector3d ndc((px + 0.5) / canvas_width_, (py + 0.5) / canvas_height_, cursor_depth_);
	Eigen::Vector4d proj;
	proj << 2. * ndc - Eigen::Vector3d(1.0, 1.0, 1.0), 1.0;
	Eigen::Matrix4d ivp_matrix;
	scene_->computeInverseViewProjectionMatrix(&ivp_matrix);
	Eigen::Vector4d world = ivp_matrix * proj;
	cursor_world_pos_ = Eigen::Vector3d(world(0), world(1), world(2)) / world(3);
}

void Renderer::renderSceneClickable(const scene::Scene* scene) {
	Eigen::Matrix4d vp_matrix;
	scene->computeViewProjectionMatrix(&vp_matrix);

	triangle_mesh_program_->use();
	glUniform4fv(triangle_mesh_program_ul_.clipping_plane, 1, clipping_plane_.data());
	const auto& camera_pos = scene->activeCameraNode()->worldPosition();
	glUniform3f(triangle_mesh_program_ul_.world_camera, camera_pos(0), camera_pos(1), camera_pos(2));

	glPolygonMode(GL_FRONT_AND_BACK, GL_FILL);
	glEnable(GL_POLYGON_OFFSET_FILL);
	for (auto& tm : scene->triangleMeshInstances()) {
		renderTriangleMesh(*tm, vp_matrix);
	}

	glBindVertexArray(0);
	glUseProgram(0);
}

void Renderer::renderSceneNonClickable(const scene::Scene* scene) {
	Eigen::Matrix4d vp_matrix;
	scene->computeViewProjectionMatrix(&vp_matrix);

	line_mesh_program_->use();

	glPointSize(1.0f * static_cast<float>(content_scale_) * 0.8f);
	for (auto& lm : scene->lineMeshInstances()) {
		renderLineMesh(*lm, vp_matrix);
	}

	overlay_mesh_program_->use();
	// glUniform4fv(overlay_mesh_program_ul_.clipping_plane, 1, clipping_plane_.data());
	for (auto& om : scene->overlayMeshInstances()) {
		renderOverlayMesh(*om, vp_matrix);
	}

	glBindVertexArray(0);
	glUseProgram(0);
}

void Renderer::renderLineMesh(const scene::LineMeshInstance& inst,
                              const Eigen::Matrix4d& vp_matrix) {
	if (!inst.visible())
		return;

	auto node = inst.node();
	auto mesh = inst.mesh();
	Eigen::Matrix4d model_matrix;
	node->getModelMatrix(&model_matrix);
	Eigen::Matrix4f mvp_matrix = (vp_matrix * model_matrix).cast<float>();
	Eigen::Matrix4f model_matrix_float = model_matrix.cast<float>();
	glUniformMatrix4fv(line_mesh_program_ul_.model_matrix, 1, GL_FALSE, model_matrix_float.data());
	glUniformMatrix4fv(line_mesh_program_ul_.mvp_matrix, 1, GL_FALSE, mvp_matrix.data());
	if (inst.clippable()) {
		glUniform4fv(line_mesh_program_ul_.clipping_plane, 1, clipping_plane_.data());
	} else {
		glUniform4f(line_mesh_program_ul_.clipping_plane, 0.f, 0.f, 0.f, 1.f);
	}

	glBindVertexArray(mesh->vaoName());
	glVertexAttrib3fv(3, inst.color().data());

	float lw = inst.lineWidth() * static_cast<float>(content_scale_);
	glLineWidth(lw);

	if (mesh->hasElements()) {
		glDrawElements(GL_LINES, mesh->numElements() * 2, GL_UNSIGNED_INT, nullptr);
		glDrawArrays(GL_POINTS, 0, mesh->numVertices());
	} else {
		glDrawArrays(GL_LINES, 0, mesh->numVertices());
		glDrawArrays(GL_POINTS, 0, mesh->numVertices());
	}
}

void Renderer::renderTriangleMesh(const scene::TriangleMeshInstance& inst,
                                  const Eigen::Matrix4d& vp_matrix) {
	if (!inst.visible())
		return;

	auto node = inst.node();
	auto mesh = inst.mesh();
	Eigen::Matrix4d model_matrix;
	node->getModelMatrix(&model_matrix);
	Eigen::Matrix4f mvp_matrix = (vp_matrix * model_matrix).cast<float>();
	Eigen::Matrix4f model_matrix_float = model_matrix.cast<float>();
	glUniformMatrix4fv(triangle_mesh_program_ul_.model_matrix, 1, GL_FALSE,
	                   model_matrix_float.data());
	glUniformMatrix4fv(triangle_mesh_program_ul_.mvp_matrix, 1, GL_FALSE, mvp_matrix.data());
	if (inst.clippable()) {
		glUniform4fv(triangle_mesh_program_ul_.clipping_plane, 1, clipping_plane_.data());
	} else {
		glUniform4f(triangle_mesh_program_ul_.clipping_plane, 0.f, 0.f, 0.f, 1.f);
	}
	glUniform1f(triangle_mesh_program_ul_.angle_attenuation, inst.angleAttenuation());

	glBindVertexArray(mesh->vaoName());
	if (!mesh->hasFrontColor()) {
		glVertexAttrib3fv(3, inst.frontColor().data());
	}
	if (!mesh->hasBackColor()) {
		glVertexAttrib3fv(4, inst.backColor().data());
	}

	auto offset = inst.polygonOffset();
	glPolygonOffset(offset[0], offset[1]);

	if (mesh->hasElements()) {
		glDrawElements(GL_TRIANGLES, mesh->numElements() * 3, GL_UNSIGNED_INT, nullptr);
	} else {
		glDrawArrays(GL_TRIANGLES, 0, mesh->numVertices());
	}
}

void Renderer::renderOverlayMesh(const scene::OverlayMeshInstance& inst,
                                 const Eigen::Matrix4d& vp_matrix) {
	if (!inst.visible())
		return;

	auto node = inst.node();
	auto mesh = inst.mesh();

	Eigen::Matrix4d model_matrix;
	node->getModelMatrix(&model_matrix);
	Eigen::Matrix4f mvp_matrix = (vp_matrix * model_matrix).cast<float>();
	Eigen::Matrix4f model_matrix_float = model_matrix.cast<float>();
	glUniformMatrix4fv(overlay_mesh_program_ul_.model_matrix, 1, GL_FALSE, model_matrix_float.data());
	glUniformMatrix4fv(overlay_mesh_program_ul_.mvp_matrix, 1, GL_FALSE, mvp_matrix.data());
	Eigen::Vector3f color = inst.color();
	glUniform3fv(overlay_mesh_program_ul_.color, 1, color.data());
	glUniform1i(overlay_mesh_program_ul_.pattern_front, static_cast<int>(inst.patternFront()));
	glUniform1i(overlay_mesh_program_ul_.pattern_back, static_cast<int>(inst.patternBack()));

	glBindVertexArray(mesh->vaoName());

	auto offset = inst.polygonOffset();
	glPolygonOffset(offset[0], offset[1]);

	if (mesh->hasElements()) {
		glDrawElements(GL_TRIANGLES, mesh->numElements() * 3, GL_UNSIGNED_INT, nullptr);
	} else {
		glDrawArrays(GL_TRIANGLES, 0, mesh->numVertices());
	}
}

void Renderer::setCursorPosition(int x, int y) {
	cursor_x_ = x;
	cursor_y_ = y;
	read_index_enabled_ = true;
}

void Renderer::setClippingPlane(Eigen::Vector3d point, Eigen::Vector3d inside_direction) {
	clipping_plane_ << inside_direction.cast<float>(),
	    static_cast<float>(-point.dot(inside_direction));
}
void Renderer::resetClippingPlane() { clipping_plane_ << 0., 0., 0., 1.; }

void Renderer::disableReadIndex() { read_index_enabled_ = false; }

void Renderer::addOverlayScene(const scene::Scene* scene, OverlaySceneParameters parameters) {
	overlay_scenes_.push_back(std::make_pair(scene, parameters));
}

Renderer::OverlaySceneParameters* Renderer::overlaySceneParameters(const scene::Scene* scene) {
	for (auto& s : overlay_scenes_) {
		if (s.first == scene) {
			return &(s.second);
		}
	}
	return nullptr;
}

const Renderer::OverlaySceneParameters* Renderer::overlaySceneParameters(
    const scene::Scene* scene) const {
	for (auto& s : overlay_scenes_) {
		if (s.first == scene) {
			return &(s.second);
		}
	}
	return nullptr;
}

void Renderer::flipFrameForPNG(std::vector<uint8_t>& image, int width, int height, int chan) {
	for (int h = 0; h < height / 2; ++h) {
		for (int w = 0; w < width; ++w) {
			for (int c = 0; c < chan; ++c) {
				int old_idx = h * width * chan + w * chan + c;
				int new_idx = (height - h - 1) * width * chan + w * chan + c;
				std::swap(image[new_idx], image[old_idx]);
			}
		}
	}
}

}  // namespace sdtf::viewer::logic