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
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/Drawable.h>
#include <Magnum/SceneGraph/MatrixTransformation3D.h>
#include <Magnum/SceneGraph/Scene.h>
#include <Magnum/Shaders/PhongGL.h>
#include <Magnum/Trade/MeshData.h>

#include <Magnum/ImGuiIntegration/Context.hpp>
#include <iostream>
#include <memory>
#include <vector>

#include "Cameras/ArcBallCamera.h"
#include "Drawables/ColoredDrawable.h"
#include "Grids/Grid.h"

namespace Magnum {
using namespace Math::Literals;
typedef SceneGraph::Object<SceneGraph::MatrixTransformation3D> Object3D;
typedef SceneGraph::Scene<SceneGraph::MatrixTransformation3D> Scene3D;

class SceneGraphTest : public Platform::Application {
   public:
	explicit SceneGraphTest(const Arguments& arguments);

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

	std::shared_ptr<Shaders::PhongGL> mp_coloredShader;
	std::shared_ptr<Shaders::FlatGL3D> mp_flatShader;

	// std::vector<GL::Mesh> m_meshes;
	std::vector<std::shared_ptr<GL::Mesh>> m_meshes;
	Containers::Array<Containers::Optional<GL::Texture2D>> m_textures;

	ImGuiIntegration::Context m_imgui{NoCreate};

	Scene3D m_scene;
	Object3D m_selected_cube;
	std::unique_ptr<Camera::ArcBallCamera> mp_acamera;

	SceneGraph::DrawableGroup3D m_drawables;
	std::vector<ColoredDrawable3D*> m_drawableVect;
	std::vector<Vector4> m_lightPositions{{-5, 1, 5, 0},
										  {5, 1, 5, 0},
										  {1, 1, -5, 0}};
	std::vector<Color3> m_lightColors{{1.f, 1.f, 1.f},
									  {0.5f, 0.5f, 0.5f},
									  {2, 2, 2}};
	Vector3 m_previousPosition;
	Vector3i m_selectedDims{0, 0, 0};
	int m_selectedIdx = 0;
	Vector3 m_pos;

	Grid::DenseGrid3D<float> field;
	std::shared_ptr<GL::Mesh> gridMeshGL;
};

SceneGraphTest::SceneGraphTest(const Arguments& arguments)
	: Platform::Application{arguments,
							Configuration{}
								.setTitle("Scene Graph 3D")
								.setWindowFlags(
									Configuration::WindowFlag::Resizable)},
	  field(Magnum::Vector3(-1.0f, -1.0f, -1.0f),
			Magnum::Vector3{1.0f, 1.0f, 1.0f},
			0.25f,
			true) {
	m_imgui = ImGuiIntegration::Context(Vector2{windowSize()} / dpiScaling(),
										windowSize(), framebufferSize());
	GL::Renderer::setBlendEquation(GL::Renderer::BlendEquation::Add,
								   GL::Renderer::BlendEquation::Add);
	GL::Renderer::setBlendFunction(
		GL::Renderer::BlendFunction::SourceAlpha,
		GL::Renderer::BlendFunction::OneMinusSourceAlpha);

	{
		Vector3 eye{10, 10, 8};
		Vector3 up = Vector3::yAxis();
		mp_acamera = std::make_unique<Camera::ArcBallCamera>(
			m_scene, eye, Vector3{}, up, 35.0_degf, windowSize(),
			framebufferSize());
	}

	GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
	GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);

	mp_coloredShader = std::make_shared<Shaders::PhongGL>(
		Shaders::PhongGL::Flags{}, m_lightPositions.size());
	(*mp_coloredShader)
		.setAmbientColor(0x111111_rgbf)
		.setSpecularColor(0xffffff_rgbf)
		.setShininess(80.f);
	mp_flatShader = std::make_shared<Shaders::FlatGL3D>();

	m_meshes.push_back(std::make_shared<GL::Mesh>(NoCreate));
	*m_meshes.back() = MeshTools::compile(Primitives::cubeSolid());
	m_selected_cube.setParent(&m_scene);
	m_selected_cube.scale(
		{0.5f * field.getDx(), 0.5f * field.getDx(), 0.5f * field.getDx()});
	m_selected_cube.translate(
		field.getIJKPos(m_selectedDims) +
		0.5 * Vector3(field.getDx(), field.getDx(), field.getDx()));

	m_drawableVect.push_back(new ColoredDrawable3D{
		m_selected_cube, mp_coloredShader, m_meshes[0], 0x00ff00_rgbf,
		m_drawables, m_lightPositions, m_lightColors});

	gridMeshGL = std::make_shared<GL::Mesh>(NoCreate);
	*gridMeshGL = field.getGLMesh();
	new FlatDrawable3D(m_scene, mp_flatShader, gridMeshGL, 0xffffff_rgbf,
					   m_drawables, m_lightPositions, m_lightColors);
}

void SceneGraphTest::drawEvent() {
	GL::defaultFramebuffer.clear(GL::FramebufferClear::Color |
								 GL::FramebufferClear::Depth);
	mp_acamera->draw(m_drawables);

	/* Enable text input, if needed */
	if (ImGui::GetIO().WantTextInput && !isTextInputActive())
		startTextInput();
	else if (!ImGui::GetIO().WantTextInput && isTextInputActive())
		stopTextInput();
	m_imgui.newFrame();
	ImGui::Begin("Hello");
	if (ImGui::InputInt("x-axis", &m_selectedDims[0]) |
		ImGui::InputInt("y-axis", &m_selectedDims[1]) |
		ImGui::InputInt("z-axis", &m_selectedDims[2])) {
		m_selectedIdx = field.ijk2idx(m_selectedDims);
		m_selected_cube.resetTransformation();
		m_selected_cube.scale(
			{0.5f * field.getDx(), 0.5f * field.getDx(), 0.5f * field.getDx()});
		m_selected_cube.translate(
			field.getIJKPos(m_selectedDims) +
			0.5 * Vector3(field.getDx(), field.getDx(), field.getDx()));
	}
	if (ImGui::InputInt("Select index", &m_selectedIdx)) {
		m_selectedDims = field.idx2ijk(m_selectedIdx);
		m_selected_cube.resetTransformation();
		m_selected_cube.scale(
			{0.5f * field.getDx(), 0.5f * field.getDx(), 0.5f * field.getDx()});
		m_selected_cube.translate(
			field.getIJKPos(m_selectedDims) +
			0.5 * Vector3(field.getDx(), field.getDx(), field.getDx()));
	}
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

void SceneGraphTest::viewportEvent(ViewportEvent& event) {
	GL::defaultFramebuffer.setViewport({{}, event.framebufferSize()});
	mp_acamera->reshape(event.windowSize(), event.framebufferSize());
	// m_coloredShader.setViewportSize(Vector2{framebufferSize()});

	m_imgui.relayout(Vector2{event.windowSize()} / event.dpiScaling(),
					 event.windowSize(), event.framebufferSize());
}

void SceneGraphTest::keyPressEvent(KeyEvent& event) {
	if (m_imgui.handleKeyPressEvent(event))
		return;
}

void SceneGraphTest::keyReleaseEvent(KeyEvent& event) {
	if (m_imgui.handleKeyReleaseEvent(event))
		return;
}

void SceneGraphTest::mousePressEvent(MouseEvent& event) {
	if (m_imgui.handleMousePressEvent(event))
		return;

	mp_acamera->initTransformation(event.position());
	mp_acamera->update();
	event.setAccepted();
	redraw();
}

void SceneGraphTest::mouseReleaseEvent(MouseEvent& event) {
	if (m_imgui.handleMouseReleaseEvent(event))
		return;
	mp_acamera->update();
	event.setAccepted();
}

void SceneGraphTest::mouseMoveEvent(MouseMoveEvent& event) {
	if (m_imgui.handleMouseMoveEvent(event))
		return;

	if (!event.buttons())
		return;
	if (event.buttons() == MouseMoveEvent::Button::Left) {
		mp_acamera->rotate(event.position());
	} else if (event.buttons() == MouseMoveEvent::Button::Middle) {
		mp_acamera->translate(event.position());
	}
	mp_acamera->update();
	event.setAccepted();
	redraw();
}

void SceneGraphTest::mouseScrollEvent(MouseScrollEvent& event) {
	if (m_imgui.handleMouseScrollEvent(event)) {
		return;
	}
	/* Prevent scrolling the page */
	const Float delta = event.offset().y();
	if (Math::abs(delta) < 1.0e-2f)
		return;

	mp_acamera->zoom(delta);
	mp_acamera->update();

	redraw(); /* camera has changed, redraw! */
	event.setAccepted();
}

void SceneGraphTest::textInputEvent(TextInputEvent& event) {
	if (m_imgui.handleTextInputEvent(event))
		return;
}

}  // namespace Magnum

MAGNUM_APPLICATION_MAIN(Magnum::SceneGraphTest)
