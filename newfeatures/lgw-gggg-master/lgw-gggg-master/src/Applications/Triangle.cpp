#include <Magnum/GL/Buffer.h>
#include <Magnum/GL/DefaultFramebuffer.h>
#include <Magnum/GL/Mesh.h>
#include <Magnum/GL/Renderer.h>
#include <Magnum/Math/Color.h>
#include <Magnum/Platform/GlfwApplication.h>
#include <Magnum/Shaders/VertexColorGL.h>

#include <Magnum/ImGuiIntegration/Context.hpp>

namespace Magnum {
class Triangle : public Platform::Application {
   public:
	explicit Triangle(const Arguments& arguments);

   private:
	void drawEvent() override;
	void drawImGuiMenu();

	void viewportEvent(ViewportEvent& event) override;

	void keyPressEvent(KeyEvent& event) override;
	void keyReleaseEvent(KeyEvent& event) override;

	void mousePressEvent(MouseEvent& event) override;
	void mouseReleaseEvent(MouseEvent& event) override;
	void mouseMoveEvent(MouseMoveEvent& event) override;
	void mouseScrollEvent(MouseScrollEvent& event) override;
	void textInputEvent(TextInputEvent& event) override;

	GL::Mesh m_mesh;
	Shaders::VertexColorGL2D m_shader;
	ImGuiIntegration::Context m_imgui{NoCreate};
};

Triangle::Triangle(const Arguments& arguments)
	: Platform::Application{
		  arguments,
		  Configuration{}
			  .setTitle("Circle Example")
			  .setWindowFlags(Configuration::WindowFlag::Resizable)} {
	using namespace Math::Literals;
	m_imgui = ImGuiIntegration::Context(Vector2{windowSize()} / dpiScaling(),
										windowSize(), framebufferSize());
	GL::Renderer::setBlendEquation(GL::Renderer::BlendEquation::Add,
								   GL::Renderer::BlendEquation::Add);
	GL::Renderer::setBlendFunction(
		GL::Renderer::BlendFunction::SourceAlpha,
		GL::Renderer::BlendFunction::OneMinusSourceAlpha);
	// setMinimalLoopPeriod(16);
	struct TriangleVertex {
		Vector2 position;
		Color3 color;
	};
	const TriangleVertex vertices[]{
		{{-0.5f, -0.5f}, 0xff0000_rgbf},
		{{0.5f, -0.5f}, 0x00ff00_rgbf},
		{{0.0f, 0.0f}, 0x0000ff_rgbf},
	};
	m_mesh.setCount(Containers::arraySize(vertices))
		.addVertexBuffer(GL::Buffer{vertices}, 0,
						 Shaders::VertexColorGL2D::Position{},
						 Shaders::VertexColorGL2D::Color3{});
}

void Triangle::drawEvent() {
	GL::defaultFramebuffer.clear(GL::FramebufferClear::Color);

	m_imgui.newFrame();
	if (ImGui::GetIO().WantTextInput && !isTextInputActive())
		startTextInput();
	if (!ImGui::GetIO().WantTextInput && isTextInputActive()) {
		stopTextInput();
	}
	m_shader.draw(m_mesh);
	drawImGuiMenu();

	swapBuffers();
	redraw();
}

void Triangle::drawImGuiMenu() {
	ImGui::Begin("Hello, world!");

	ImGui::Text("It's a bird! It's a plane! It's ImGui!!");
	if (ImGui::Button("Press me")) {
	}

	ImGui::End();
	m_imgui.updateApplicationCursor(*this);

	GL::Renderer::enable(GL::Renderer::Feature::Blending);
	GL::Renderer::enable(GL::Renderer::Feature::ScissorTest);
	GL::Renderer::disable(GL::Renderer::Feature::FaceCulling);
	GL::Renderer::disable(GL::Renderer::Feature::DepthTest);
	m_imgui.drawFrame();
	GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
	GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);
	GL::Renderer::disable(GL::Renderer::Feature::ScissorTest);
	GL::Renderer::disable(GL::Renderer::Feature::Blending);
}

void Triangle::viewportEvent(ViewportEvent& event) {
	GL::defaultFramebuffer.setViewport({{}, event.framebufferSize()});

	m_imgui.relayout(Vector2{event.windowSize()} / event.dpiScaling(),
					 event.windowSize(), event.framebufferSize());
}

void Triangle::keyPressEvent(KeyEvent& event) {
	if (m_imgui.handleKeyPressEvent(event))
		return;
}

void Triangle::keyReleaseEvent(KeyEvent& event) {
	if (m_imgui.handleKeyReleaseEvent(event))
		return;
}

void Triangle::mousePressEvent(MouseEvent& event) {
	if (m_imgui.handleMousePressEvent(event))
		return;
}

void Triangle::mouseReleaseEvent(MouseEvent& event) {
	if (m_imgui.handleMouseReleaseEvent(event))
		return;
}

void Triangle::mouseMoveEvent(MouseMoveEvent& event) {
	if (m_imgui.handleMouseMoveEvent(event))
		return;
}

void Triangle::mouseScrollEvent(MouseScrollEvent& event) {
	if (m_imgui.handleMouseScrollEvent(event)) {
		/* Prevent scrolling the page */
		event.setAccepted();
		return;
	}
}

void Triangle::textInputEvent(TextInputEvent& event) {
	if (m_imgui.handleTextInputEvent(event))
		return;
}

}  // namespace Magnum

MAGNUM_APPLICATION_MAIN(Magnum::Triangle)
