#include <Corrade/Containers/Array.h>
#include <Corrade/Containers/Optional.h>
#include <Corrade/Containers/Pair.h>
#include <Corrade/Utility/Arguments.h>
#include <Corrade/Utility/DebugStl.h>
#include <Magnum/GL/DefaultFramebuffer.h>
#include <Magnum/GL/Mesh.h>
#include <Magnum/GL/Renderer.h>
#include <Magnum/ImageView.h>
#include <Magnum/Math/Color.h>
#include <Magnum/Mesh.h>
#include <Magnum/MeshTools/Compile.h>
#include <Magnum/Platform/GlfwApplication.h>
#include <Magnum/Primitives/Cube.h>
#include <Magnum/Primitives/Square.h>
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/Drawable.h>
#include <Magnum/SceneGraph/MatrixTransformation2D.h>
#include <Magnum/SceneGraph/Scene.h>
#include <Magnum/Shaders/PhongGL.h>
#include <Magnum/Trade/MeshData.h>

#include <Magnum/ImGuiIntegration/Context.hpp>
#include <iostream>
#include <memory>
#include <vector>

#include "Cameras/OrthoCamera2D.h"
#include "Drawables/ColoredDrawable.h"
namespace Magnum {
using namespace Math::Literals;

class SceneGraphTest2D : public Platform::Application {
   public:
	explicit SceneGraphTest2D(const Arguments& arguments);

   protected:
	void drawEvent() override;
	void viewportEvent(ViewportEvent& event) override;
	void keyPressEvent(KeyEvent& event) override;
	void keyReleaseEvent(KeyEvent& event) override;
	void mousePressEvent(MouseEvent& event) override;
	void mouseReleaseEvent(MouseEvent& event) override;
	void mouseMoveEvent(MouseMoveEvent& event) override;
	void mouseScrollEvent(MouseScrollEvent& event) override;
	void textInputEvent(TextInputEvent& event) override;

	std::shared_ptr<Shaders::FlatGL2D> mp_coloredShader;

	std::vector<std::shared_ptr<GL::Mesh>> m_meshes;
	Containers::Array<Containers::Optional<GL::Texture2D>> m_textures;

	ImGuiIntegration::Context m_imgui{NoCreate};

	Scene2D m_scene;
	Object2D m_manipulator;
	std::unique_ptr<Camera::OrthoCamera2D> m_camera;

	SceneGraph::DrawableGroup2D m_drawables;
	std::vector<ColoredDrawable2D*> m_drawableVect;
	Vector3 m_previousPosition;
};

SceneGraphTest2D::SceneGraphTest2D(const Arguments& arguments)
	: Platform::Application{
		  arguments,
		  Configuration{}
			  .setTitle("Scene Graph 2D")
			  .setWindowFlags(Configuration::WindowFlag::Resizable)} {
	m_imgui = ImGuiIntegration::Context(Vector2{windowSize()} / dpiScaling(),
										windowSize(), framebufferSize());
	GL::Renderer::setBlendEquation(GL::Renderer::BlendEquation::Add,
								   GL::Renderer::BlendEquation::Add);
	GL::Renderer::setBlendFunction(
		GL::Renderer::BlendFunction::SourceAlpha,
		GL::Renderer::BlendFunction::OneMinusSourceAlpha);

	m_manipulator.setParent(&m_scene);
	m_camera = std::make_unique<Camera::OrthoCamera2D>(
		m_scene, framebufferSize(), 10, Vector2{-1, -1});

	GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
	GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);

	mp_coloredShader = std::make_shared<Shaders::FlatGL2D>();
	(*mp_coloredShader).setColor(0xff0000_rgbf);

	size_t n_meshes = 1;
	for (size_t i = 0; i < n_meshes; ++i) {
		m_meshes.push_back(std::make_shared<GL::Mesh>(NoCreate));
		*m_meshes.back() = MeshTools::compile(Primitives::squareSolid());
	}

	for (int i = -2; i <= 2; i += 1) {
		for (int j = -2; j <= 2; j += 1) {
			Matrix3 m = Matrix3::scaling({0.5, 0.5});
			m = Matrix3::translation({Magnum::Float(i), Magnum::Float(j)}) * m;
			Color4 c{(i + 2) / 4.f, (j + 2) / 4.f, 0};
			m_drawableVect.push_back(
				new ColoredDrawable2D{m_manipulator, mp_coloredShader,
									  m_meshes[0], c, m_drawables, m});
		}
	}
}

void SceneGraphTest2D::drawEvent() {
	GL::defaultFramebuffer.clear(GL::FramebufferClear::Color |
								 GL::FramebufferClear::Depth);
	m_camera->draw(m_drawables);

	/* Enable text input, if needed */
	if (ImGui::GetIO().WantTextInput && !isTextInputActive())
		startTextInput();
	else if (!ImGui::GetIO().WantTextInput && isTextInputActive())
		stopTextInput();
	m_imgui.newFrame();
	ImGui::Begin("Hello");
	ImGui::Text("Hello, this is ImGui");
	ImGui::End();
	// /* Update application cursor */
	m_imgui.updateApplicationCursor(*this);

	/* Set appropriate states. If you only draw ImGui, it is sufficient to
	   just enable blending and scissor test in the constructor. */
	GL::Renderer::enable(GL::Renderer::Feature::Blending);
	GL::Renderer::enable(GL::Renderer::Feature::ScissorTest);
	GL::Renderer::disable(GL::Renderer::Feature::FaceCulling);
	GL::Renderer::disable(GL::Renderer::Feature::DepthTest);

	m_imgui.drawFrame();

	/* Reset state. Only needed if you want to draw something else with
	   different state after. */
	GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
	GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);
	GL::Renderer::disable(GL::Renderer::Feature::ScissorTest);
	GL::Renderer::disable(GL::Renderer::Feature::Blending);

	swapBuffers();
	redraw();
}

void SceneGraphTest2D::viewportEvent(ViewportEvent& event) {
	GL::defaultFramebuffer.setViewport({{}, event.framebufferSize()});
	m_camera->reshape(event.framebufferSize());

	m_imgui.relayout(Vector2{event.windowSize()} / event.dpiScaling(),
					 event.windowSize(), event.framebufferSize());
}

void SceneGraphTest2D::keyPressEvent(KeyEvent& event) {
	if (m_imgui.handleKeyPressEvent(event))
		return;
}

void SceneGraphTest2D::keyReleaseEvent(KeyEvent& event) {
	if (m_imgui.handleKeyReleaseEvent(event))
		return;
}

void SceneGraphTest2D::mousePressEvent(MouseEvent& event) {
	if (m_imgui.handleMousePressEvent(event))
		return;

	m_camera->initTransformation(event.position());
	event.setAccepted();
	redraw();
}

void SceneGraphTest2D::mouseReleaseEvent(MouseEvent& event) {
	if (m_imgui.handleMouseReleaseEvent(event))
		return;
	event.setAccepted();
}

void SceneGraphTest2D::mouseMoveEvent(MouseMoveEvent& event) {
	if (m_imgui.handleMouseMoveEvent(event))
		return;

	if (!event.buttons())
		return;
	m_camera->move(event.position());
	m_camera->update();
	event.setAccepted();
	redraw();
}

void SceneGraphTest2D::mouseScrollEvent(MouseScrollEvent& event) {
	if (m_imgui.handleMouseScrollEvent(event)) {
		return;
	}
	/* Prevent scrolling the page */
	const Float delta = event.offset().y();
	if (Math::abs(delta) < 1.0e-2f)
		return;

	m_camera->zoom(delta);
	m_camera->update();

	redraw(); /* camera has changed, redraw! */
	event.setAccepted();
}

void SceneGraphTest2D::textInputEvent(TextInputEvent& event) {
	if (m_imgui.handleTextInputEvent(event))
		return;
}

}  // namespace Magnum

MAGNUM_APPLICATION_MAIN(Magnum::SceneGraphTest2D)
