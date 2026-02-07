
#include <Corrade/Containers/Array.h>
#include <Corrade/Containers/Optional.h>
#include <Corrade/Containers/Pair.h>
#include <Corrade/PluginManager/Manager.h>
#include <Corrade/Utility/Arguments.h>
#include <Corrade/Utility/DebugStl.h>
#include <ImGuiFileDialog/ImGuiFileDialog.h>
#include <ImGuizmo/ImGuizmo.h>
#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/GL/DefaultFramebuffer.h>
#include <Magnum/GL/Framebuffer.h>
#include <Magnum/GL/Renderbuffer.h>
#include <Magnum/GL/RenderbufferFormat.h>
#include <Magnum/GL/Renderer.h>
#include <Magnum/Image.h>
#include <Magnum/ImageView.h>
#include <Magnum/Math/Color.h>
#include <Magnum/PixelFormat.h>
#include <Magnum/Platform/GlfwApplication.h>
#include <imgui.h>

#include <Magnum/ImGuiIntegration/Context.hpp>
#include <filesystem>
#include <iostream>
#include <memory>

#include "Cameras/ArcBallCamera.h"
#include "Common/Cores.h"
#include "Common/FiraSans.h"
#include "Common/MatrixTypes.h"
#include "Dynamics/DynamicSystem.h"
#include "IO/FileLoader.h"
#include "IO/FileSaver.h"
#include "UI/ImGUIMenu/Dynamics.h"
#include "UI/ImGUIMenu/ImGUIUtils.h"
#include "UI/ImGUIMenu/Object.h"
#include "UI/ImGUIMenu/Scene.h"
#include "UI/SimulationScene.h"

namespace Magnum {
using namespace Math::Literals;

class HomogenizationGUI : public Platform::Application {
   public:
	explicit HomogenizationGUI(const Arguments& arguments);

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

	void showImGUIMenu();

	GL::Framebuffer m_framebuffer;
	GL::Renderbuffer m_color, m_objectID, m_depth;
	Color3 m_clearColor = Color3{0.125f};

	ImGuiIntegration::Context m_imgui{NoCreate};
	std::string m_sceneFileName = "";
	std::string m_sceneFileDir = ".";
	std::string m_outputFileName = "";
	std::string m_outputFileDir = ".";
	std::filesystem::path m_sceneFilePath;

	Homogenization::UI::SimulationScene m_scene3D;
	Homogenization::IO::FileLoader m_fileLoader;

	std::unique_ptr<Camera::ArcBallCamera> mp_acamera;

	int m_selectedIdx = -1;

	std::string m_collisionOutput = "";
	std::string m_exceptionString = "";

	SceneGraph::DrawableGroup3D m_contactsGroup;
	GL::Buffer m_axisInstanceBuffer;

	bool m_fineZoom = false;
};

HomogenizationGUI::HomogenizationGUI(const Arguments& arguments)
	: Platform::Application{arguments,
                            Configuration{}
                                .setTitle("Homogenization")
                                .setWindowFlags(
									Configuration::WindowFlag::Resizable)},
	  m_framebuffer(GL::defaultFramebuffer.viewport()) {
	std::cout << "Cores: " << FrictionFrenzy::physicalProcessors() << std::endl;
	std::cout << "dpiScaling: " << dpiScaling().x() << " " << dpiScaling().y()
			  << std::endl;
	GL::Renderer::setClearColor(m_clearColor);

	ImGui::CreateContext();
	ImFontConfig fontConfig;
	fontConfig.FontDataOwnedByAtlas = false;
	ImGui::GetIO().Fonts->AddFontFromMemoryCompressedBase85TTF(
		Fira_Sans_compressed_data_base85, 16.0f, &fontConfig);
	m_imgui = ImGuiIntegration::Context(*ImGui::GetCurrentContext(),
	                                    Vector2{windowSize()}, windowSize(),
	                                    framebufferSize());

	GL::Renderer::setBlendEquation(GL::Renderer::BlendEquation::Add,
	                               GL::Renderer::BlendEquation::Add);
	GL::Renderer::setBlendFunction(
		GL::Renderer::BlendFunction::SourceAlpha,
		GL::Renderer::BlendFunction::OneMinusSourceAlpha);

	m_color.setStorage(GL::RenderbufferFormat::RGBA8,
	                   GL::defaultFramebuffer.viewport().size());
	m_objectID.setStorage(GL::RenderbufferFormat::R32UI,
	                      GL::defaultFramebuffer.viewport().size());
	m_depth.setStorage(GL::RenderbufferFormat::DepthComponent24,
	                   GL::defaultFramebuffer.viewport().size());
	m_framebuffer
		.attachRenderbuffer(GL::Framebuffer::ColorAttachment{0}, m_color)
		.attachRenderbuffer(GL::Framebuffer::ColorAttachment{1}, m_objectID)
		.attachRenderbuffer(GL::Framebuffer::BufferAttachment::Depth, m_depth)
		.mapForDraw({{Shaders::PhongGL::ColorOutput,
	                  GL::Framebuffer::ColorAttachment{0}},
	                 {Shaders::PhongGL::ObjectIdOutput,
	                  GL::Framebuffer::ColorAttachment{1}}});

	{
		Vector3 eye{10, 10, 8};
		Vector3 up = Vector3::yAxis();
		mp_acamera = std::make_unique<Camera::ArcBallCamera>(
			m_scene3D.magnumScene(), eye, Vector3{}, up, 20.0_degf,
			windowSize(), framebufferSize());
	}

	GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
	GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);
}

void HomogenizationGUI::drawEvent() {
	m_framebuffer.clearColor(0, m_clearColor)
		.clearColor(1, Vector4ui{})
		.clearDepth(1.0f)
		.bind();
	m_scene3D.advanceOneFrame();
	m_scene3D.drawScene(*mp_acamera);
	GL::defaultFramebuffer.clear(GL::FramebufferClear::Color |
	                             GL::FramebufferClear::Depth);
	GL::AbstractFramebuffer::blit(m_framebuffer, GL::defaultFramebuffer,
	                              m_framebuffer.viewport(),
	                              GL::FramebufferBlit::Color);

	/* Enable text input, if needed */
	if (ImGui::GetIO().WantTextInput && !isTextInputActive())
		startTextInput();
	else if (!ImGui::GetIO().WantTextInput && isTextInputActive())
		stopTextInput();
	showImGUIMenu();

	swapBuffers();
	redraw();
}

void HomogenizationGUI::viewportEvent(ViewportEvent& event) {
	GL::defaultFramebuffer.setViewport({{}, event.framebufferSize()});
	m_framebuffer.setViewport({{}, event.framebufferSize()});
	m_color.setStorage(GL::RenderbufferFormat::RGBA8,
	                   GL::defaultFramebuffer.viewport().size());
	m_objectID.setStorage(GL::RenderbufferFormat::R32UI,
	                      GL::defaultFramebuffer.viewport().size());
	m_depth.setStorage(GL::RenderbufferFormat::DepthComponent24,
	                   GL::defaultFramebuffer.viewport().size());
	mp_acamera->reshape(event.windowSize(), event.framebufferSize());

	m_imgui.relayout(Vector2{event.windowSize()}, event.windowSize(),
	                 event.framebufferSize());
}

void HomogenizationGUI::keyPressEvent(KeyEvent& event) {
	if (m_imgui.handleKeyPressEvent(event)) {
		return;
	}

	if (event.key() == KeyEvent::Key::LeftShift) {
		m_fineZoom = true;
	}
}

void HomogenizationGUI::keyReleaseEvent(KeyEvent& event) {
	if (event.key() == KeyEvent::Key::LeftShift) {
		m_fineZoom = false;
	}
	if (m_imgui.handleKeyReleaseEvent(event)) {
		return;
	}
	if (event.key() == KeyEvent::Key::Esc) {
		m_scene3D.setSimulate(false);
	}
}

void HomogenizationGUI::mousePressEvent(MouseEvent& event) {
	if (m_imgui.handleMousePressEvent(event))
		return;

	mp_acamera->initTransformation(event.position());
	mp_acamera->update();
	event.setAccepted();
	redraw();
}

void HomogenizationGUI::mouseReleaseEvent(MouseEvent& event) {
	if (m_imgui.handleMouseReleaseEvent(event))
		return;

	const Vector2i position =
		event.position() * Vector2{framebufferSize()} / Vector2{windowSize()};
	const Vector2i fbPosition{
		position.x(),
		GL::defaultFramebuffer.viewport().sizeY() - position.y() - 1};

	if (event.button() == MouseEvent::Button::Right) {
		m_framebuffer.mapForRead(GL::Framebuffer::ColorAttachment{1});
		Image2D data = m_framebuffer.read(
			Range2Di::fromSize(fbPosition, {1, 1}), {PixelFormat::R32UI});
		m_framebuffer.mapForRead(GL::Framebuffer::ColorAttachment{0});

		UnsignedInt id = data.pixels<UnsignedInt>()[0][0];
		if (id >= 1 && id <= m_scene3D.dynamicSystem().nObjects()) {
			m_selectedIdx = id - 1;
		} else {
			m_selectedIdx = -1;
		}
	}

	mp_acamera->update();
	event.setAccepted();
}

void HomogenizationGUI::mouseMoveEvent(MouseMoveEvent& event) {
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

void HomogenizationGUI::mouseScrollEvent(MouseScrollEvent& event) {
	if (m_imgui.handleMouseScrollEvent(event)) {
		return;
	}
	/* Prevent scrolling the page */
	const Float delta = event.offset().y() * (m_fineZoom ? 0.05 : 1);
	if (Math::abs(delta) < 1.0e-2f)
		return;

	mp_acamera->zoom(delta);
	mp_acamera->update();

	redraw(); /* camera has changed, redraw! */
	event.setAccepted();
}

void HomogenizationGUI::textInputEvent(TextInputEvent& event) {
	if (m_imgui.handleTextInputEvent(event))
		return;
}

void HomogenizationGUI::showImGUIMenu() {
	m_imgui.newFrame();
	ImGuizmo::BeginFrame();
	ImGuizmo::SetRect(0, 0, ImGui::GetIO().DisplaySize.x,
	                  ImGui::GetIO().DisplaySize.y);
	ImGuizmo::AllowAxisFlip(false);

	const auto loadYamlFile = [&]() {
		try {
			m_selectedIdx = -1;
			m_fileLoader.loadFile(m_scene3D, m_sceneFileName, true);

			FrictionFrenzy::Vector3 centerEigen;
			FrictionFrenzy::Scalar radius;
			std::tie(centerEigen, radius) =
				m_scene3D.dynamicSystem().getApproxBoundingSphere();
			Vector3 center(centerEigen[0], centerEigen[1], centerEigen[2]);
			Float rad = std::atan(
				std::tan(M_PI * 17.5 / 180) *
				std::min(Float(windowSize().y()) / windowSize().x(), Float(1)));
			Vector3 camDir =
				Vector3(10, 4, 8).normalized() * radius / std::sin(rad);
			mp_acamera->setViewParameters(center + camDir, center,
			                              Vector3::yAxis());
			mp_acamera->update();
			redraw();

		} catch (const std::exception& e) {
			m_scene3D.clearAll();
			ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(),
			                        ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
			ImGui::OpenPopup("Input file parse error");
			m_exceptionString = e.what();
			m_sceneFileName = "";
			m_sceneFileDir = ".";
		}
	};

	ImGui::SetNextWindowSizeConstraints(
		ImVec2(0, windowSize().y()),
		ImVec2(windowSize().x(), windowSize().y()));
	ImGui::Begin("Simulation", NULL, ImGuiWindowFlags_AlwaysAutoResize);
	if (ImGui::Button("Open file")) {
		IGFD::FileDialogConfig igfdConfig;
		igfdConfig.path = m_sceneFileDir;
		ImGui::SetNextWindowPos(ImGui::GetMainViewport()->GetCenter(),
		                        ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
		ImGuiFileDialog::Instance()->OpenDialog(
			"ChooseFile", "Choose Scene File", ".yaml", igfdConfig);
	}
	ImGui::SameLine();
	if (ImGui::Button("Reload file")) {
		loadYamlFile();
	}
	ImVec2 maxSize = ImVec2((float)windowSize().x(),
	                        (float)windowSize().y());  // The full display area
	ImVec2 minSize = maxSize * 0.5f;                   // Half the display area
	if (ImGuiFileDialog::Instance()->Display(
			"ChooseFile", ImGuiWindowFlags_None, minSize, maxSize)) {
		ImVec2 windowSize = ImGui::GetWindowSize();
		ImGui::SetWindowPos(minSize - windowSize);
		if (ImGuiFileDialog::Instance()->IsOk()) {
			m_sceneFileName = ImGuiFileDialog::Instance()->GetFilePathName();
			m_sceneFileDir = ImGuiFileDialog::Instance()->GetCurrentPath();
			loadYamlFile();
		}
		ImGuiFileDialog::Instance()->Close();
	}
	ImGui::GetWindowSize();
	if (ImGui::BeginPopupModal("Input file parse error")) {
		ImGui::Text("Error: %s", m_exceptionString.c_str());
		ImVec2 button_size = ImGui::CalcTextSize("Close");
		float width = ImGui::GetWindowSize().x;
		float centre_position_for_button = (width - button_size.x) / 2;
		ImGui::SetCursorPosX(centre_position_for_button);
		if (ImGui::Button("Close")) {
			ImGui::CloseCurrentPopup();
		}
		ImGui::EndPopup();
	}
	ImGui::Text("%s",
	            std::filesystem::path(m_sceneFileName).filename().c_str());
	if (m_selectedIdx >= 0) {
		Homogenization::UI::showImGUIMenu(
			m_scene3D.dynamicSystem().getObject(m_selectedIdx));
		auto& obj = m_scene3D.dynamicSystem().getObject(m_selectedIdx);
		Eigen::Matrix4f configMat =
			obj.getRigidTransMatrix().matrix().cast<float>();
		ImGuizmo::Manipulate(mp_acamera->getMatrix().data(),
		                     mp_acamera->getProjection().data(),
		                     ImGuizmo::ROTATE | ImGuizmo::TRANSLATE,
		                     ImGuizmo::WORLD, configMat.data());
		FrictionFrenzy::Affine configMatEigen(
			configMat.cast<FrictionFrenzy::Scalar>());
		obj.setConfiguration(configMatEigen);
		m_scene3D.dynamicSystem().updateFCLObject(m_selectedIdx);
		m_scene3D.updateDrawable(m_selectedIdx);
	}

	if (ImGui::CollapsingHeader("Camera settings")) {
		if (ImGui::SliderFloatType("Clip near", &mp_acamera->clipNear(), 0.001,
		                           100)) {
			mp_acamera->updateCameraProjection();
		}
		if (ImGui::SliderFloatType("Clip far", &mp_acamera->clipFar(), 1,
		                           1000)) {
			mp_acamera->updateCameraProjection();
		}
		Magnum::Float fov = Magnum::Float(Magnum::Deg(mp_acamera->fov()));
		if (ImGui::SliderFloatType("FOV", &fov, 10, 90)) {
			mp_acamera->fov() = Magnum::Deg(fov);
			mp_acamera->updateCameraProjection();
		}
	}

	Homogenization::UI::showImGUIMenu(m_scene3D);

	ImGui::Checkbox("Show collisions", &m_scene3D.showContacts());
	if (m_scene3D.showContacts()) {
		ImGui::SliderFloatType("Axis scale", &m_scene3D.contactAxisScale(), 0.0,
		                       0.3);
		Homogenization::UI::showImGUICollisionMenu(m_scene3D.dynamicSystem());
	}
	ImGui::End();
	ImGui::SetWindowPos("Simulation", ImVec2(0, 0));
	ImGui::SetWindowSize("Simulation",
	                     ImVec2(ImGui::GetWindowSize().x, windowSize().y()));
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
}

}  // namespace Magnum

MAGNUM_APPLICATION_MAIN(Magnum::HomogenizationGUI)
