#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/GL/RenderbufferFormat.h>
#include <Magnum/Primitives/Cube.h>
#include <Magnum/Trade/ImageData.h>
#include <MagnumPlugins/PngImporter/PngImporter.h>
#include <imgui.h>
#include <Magnum/ImGuiIntegration/Context.hpp>
#include <iomanip>
#include <sstream>
#include <string>

#include "Drawables/ColoredDrawable.h"
#include "Drawables/MagnumTypes.h"
#include "Drawables/MagnumUtils.hpp"
#include "IO/ParticlePLYExport.hpp"
#include "IO/SimulationGenerator.hpp"
#include "Magnum/GL/DefaultFramebuffer.h"
#include "Magnum/GL/Framebuffer.h"
#include "Magnum/MeshTools/Transform.h"
#include "mpm3DApp.hpp"

#define USE_TIMER
#include "Common/debug.hpp"
#include "Common/timer.hpp"

namespace Magnum {
using namespace Math::Literals;

Mpm3DApp::Mpm3DApp(const Arguments& arguments, ConfigFileLoader& config)
    : Platform::Application{arguments,
                            Configuration{}
                                .setTitle(config.gui.name)
                                .setSize(config.gui.size)
                                .setWindowFlags(
                                    Configuration::WindowFlag::Resizable)},
      // Save fields that need reusing(?)
      m_framebuffer(GL::defaultFramebuffer.viewport()),
      m_lightPositions(config.gui.lightPositions),
      m_lightColors(config.gui.lightColors),
      m_particleSaveFreq(config.output.freq),
      m_cameraInit(config.gui.cameraPosition),
      m_lookAtInit(config.gui.cameraLookAt),
	  m_outputDirectory(config.output.fsPath) {
    // Prepare the output repository
    TIMER_MS_START("[Init]", 0);
    SimulationGenerator<true> sim;
    m_mpmSimPtr = sim.initializeSimulation(config);
    TIMER_MS_PRINT_CP("Simulation");

    // Viewer configuration
    m_imgui = ImGuiIntegration::Context(
        Vector2{windowSize()} /* / dpiScaling()*/, windowSize(),
        framebufferSize()
    );

    // Initialize OpenGL features
    GL::Renderer::enable(GL::Renderer::Feature::ProgramPointSize);
    GL::Renderer::enable(GL::Renderer::Feature::Blending);
    GL::Renderer::enable(GL::Renderer::Feature::DepthTest);
    GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);
    GL::Renderer::setBlendEquation(GL::Renderer::BlendEquation::Add);
    GL::Renderer::setBlendFunction(
        GL::Renderer::BlendFunction::SourceAlpha,
        GL::Renderer::BlendFunction::OneMinusSourceAlpha
    );

    // Create arcball camera and attach to scenegraph
    const Vec3f up = Vec3f::zAxis();
    m_camera = std::make_shared<Camera::ArcBallCamera>(
        m_scene, m_cameraInit, m_lookAtInit, up, 35.0_degf, windowSize(),
        framebufferSize()
    );

    // Framebuffer
    m_color.setStorage(
        GL::RenderbufferFormat::RGBA8, GL::defaultFramebuffer.viewport().size()
    );
    m_particleID.setStorage(
        GL::RenderbufferFormat::R32UI, GL::defaultFramebuffer.viewport().size()
    );
    m_depth.setStorage(
        GL::RenderbufferFormat::DepthComponent24,
        GL::defaultFramebuffer.viewport().size()
    );
    m_framebuffer
        .attachRenderbuffer(GL::Framebuffer::ColorAttachment{0}, m_color)
        .attachRenderbuffer(GL::Framebuffer::ColorAttachment{1}, m_particleID)
        .attachRenderbuffer(GL::Framebuffer::BufferAttachment::Depth, m_depth)
        .mapForDraw(
            {{0, GL::Framebuffer::ColorAttachment{0}},
             {1, GL::Framebuffer::ColorAttachment{1}}}
        );

    // Shader
    m_flatShader = std::make_shared<Shaders::FlatGL3D>();
    (*m_flatShader).setColor(0xff0000_rgbf);
    m_glPhongShader = std::make_shared<Shaders::PhongGL>(
        Shaders::PhongGL::Configuration().setLightCount(m_lightPositions.size())
    );

    /// Create the graph node
    m_mpmObj.setParent(&m_scene);
    m_obstacleObj.setParent(&m_scene);

    /// Create MPM/surface drawables
    m_mpmDrawPtr = std::make_shared<MPM::MPM3DDrawable>(
        m_mpmSimPtr, config.gui.pRender, m_mpmObj, m_drawables,
        m_lightPositions, m_lightColors  //, config.gui.surface
    );
    // Initialise particle data
    m_mpmSimPtr->updateDebugData();
    m_mpmDrawPtr->update();

    Params::DisplayValue dv = m_mpmSimPtr->getDebugParameters();
    if (dv == Params::DisplayValue::PlasticVolume) {
        current_item = items[1];
    } else if (dv == Params::DisplayValue::ParticleAltitude) {
        current_item = items[2];
    } else if (dv == Params::DisplayValue::PackingFraction) {
        current_item = items[3];
    } else if (dv == Params::DisplayValue::ParticleSpeed) {
        current_item = items[4];
    } else if (dv == Params::DisplayValue::ParticlePressure) {
        current_item = items[5];
    }
    Type::Vec3f start = m_mpmSimPtr->getGridMass().getStartPos().cast<float>();
    m_cuttingPlanes = Vector3(start);
    m_cuttingPlanes[2] = m_mpmSimPtr->getGridMass().getEndPos()[2];
    (*m_mpmDrawPtr->getParticleShader())
        .setGamma(m_debugGamma)
        .setCuttingPlanes(m_cuttingPlanes)
        .setInvertPlanes(
            m_invertPlanes[0], m_invertPlanes[1], m_invertPlanes[2]
        );

    /// Create obstacle drawables
    for (int i = 0; i < sim.getRigidMeshes().size(); ++i) {
        auto mesh = sim.getRigidMeshes()[i];
        m_obstacleMeshesGL.push_back(mesh);
        m_obstacleObjs.push_back(std::make_unique<Object3D>(&m_scene));
        m_obstacleDrawables.push_back(std::make_unique<RigidDrawable3D>(
            m_obstacleObjs.back().get(), m_glPhongShader,
            m_obstacleMeshesGL.back(),
            &(m_mpmSimPtr->getRigidBodyWorld()->getObject(i)),
            Color4(0.8, 0.8, 0.8, 1.0), m_rigidDrawable, m_lightPositions,
            m_lightColors, i
        ));
    }
    sim.freeAllData();

    // Create MPM grids / bounds
    /// Mesh
    m_gridMeshGL = std::make_shared<GL::Mesh>(NoCreate);
    *(m_gridMeshGL) = gridToGLMesh(m_mpmSimPtr->getGridVel());
    new FlatDrawable3D(
        m_scene, m_flatShader, m_gridMeshGL, 0x999999_rgbf, m_gridDrawable,
        m_lightPositions, m_lightColors
    );
    // Bounds
    const Type::Vec3 size = m_mpmSimPtr->getGridParameters().gridEnd;
    const Vec3 scale(0.5f * size[0], 0.5f * size[1], 0.5f * size[2]);
    auto cubeWire = Primitives::cubeWireframe();  // 2x2x2, center in 0
    Matrix4 transform = Matrix4::translation(scale) * Matrix4::scaling(scale);
    auto cubeWireTr = MeshTools::transform3D(cubeWire, transform);
    m_boundsMeshGL = std::make_shared<GL::Mesh>(NoCreate);
    *m_boundsMeshGL = MeshTools::compile(cubeWireTr);
    new FlatDrawable3D(
        m_boundsObj, m_flatShader, m_boundsMeshGL, 0xff9900_rgbf, m_drawables,
        m_lightPositions, m_lightColors
    );
    /// Create the graph node
    m_boundsObj.setParent(&m_scene);

    TIMER_MS_PRINT_CP("Scene generation");

    TIMER_MS_END;
}

void Mpm3DApp::drawEvent() {
    // Update particles and so on here
    updateSystem();
    updateRigidDrawables();
    if (m_selectedParticle >= 0) {
        m_particleData = m_mpmSimPtr->getParticleData(m_selectedParticle);
    }
    // Clear buffer
    GL::defaultFramebuffer.clearColor(0x666666_rgbf);
    GL::defaultFramebuffer.clear(
        GL::FramebufferClear::Color | GL::FramebufferClear::Depth
    );

    if (m_simulationPaused && (m_forceRedraw > m_maxForceRedraw)) {
        // force redraw
        m_mpmDrawPtr->update();
        m_forceRedraw = 0;
    } else if (!m_simulationPaused) {
        m_forceRedraw = 0;
    }

    // Renderer state
    GL::Renderer::enable(GL::Renderer::Feature::ScissorTest);
    GL::Renderer::enable(GL::Renderer::Feature::Blending);
    GL::Renderer::enable(GL::Renderer::Feature::FaceCulling);
    GL::Renderer::enable(GL::Renderer::Feature::DepthTest);

    // Draw commons
    m_framebuffer.clearColor(0, 0x444444_rgbf)
        .clearColor(1, Vector4i{-1, -1, -1, -1})
        .clearDepth(1.0f)
        .bind();

    GL::Renderer::setLineWidth(3.0);
    m_camera->draw(m_drawables);
    // Draw grid
    if (m_displayGrid) {
        GL::Renderer::setLineWidth(0.5);
        m_camera->draw(m_gridDrawable);
    }
    GL::Renderer::setBlendFunction(
        GL::Renderer::BlendFunction::ConstantAlpha,
        GL::Renderer::BlendFunction::OneMinusConstantAlpha
    );
    if (m_rigidOpacity > 0) {
        m_camera->draw(m_rigidDrawable);
    }
    GL::AbstractFramebuffer::blit(
        m_framebuffer, GL::defaultFramebuffer, m_framebuffer.viewport(),
        GL::FramebufferBlit::Color
    );
    GL::defaultFramebuffer.bind();

    /// Enable text input, if needed
    if (ImGui::GetIO().WantTextInput && !isTextInputActive())
        startTextInput();
    else if (!ImGui::GetIO().WantTextInput && isTextInputActive())
        stopTextInput();

    // Create frame
    m_imgui.newFrame();

    // Display Menu
    ImGui::Begin("Options");

    const Params::DisplayValue& mpmDebugParams =
        m_mpmSimPtr->getDebugParameters();

    if (m_mpmSimPtr->getRigidBodyWorld()->nObjects() > 0) {
        const float oldObsAlpha = m_rigidOpacity;
        ImGui::SliderFloat("Obstacle alpha", &m_rigidOpacity, 0.0f, 1.0f);
        GL::Renderer::setBlendColor(Color4(1.0, 1.0, 1.0, m_rigidOpacity));
        m_forceRedraw += (m_rigidOpacity != oldObsAlpha);
    }
    NumT sliderMin = 0, sliderMax = 1000;
    ImGui::SliderScalar(
        "Simulation Time: ", ImGuiDataType_Double,
        &(m_mpmSimPtr->getPhysParameters().tMax), &sliderMin, &sliderMax
    );
    if (!m_simulationPaused || m_mpmSimPtr->getCurrentSimTime() != 0) {
        ImGui::Text(
            "Current time: %f / %f", m_mpmSimPtr->getCurrentSimTime(),
            m_mpmSimPtr->getPhysParameters().tMax
        );
    }

    if (ImGui::CollapsingHeader(
            "Particle visualization", ImGuiTreeNodeFlags_DefaultOpen
        )) {
        if (ImGui::TreeNode("Cutting plane")) {
            for (int i = 0; i < 3; ++i) {
                std::string axisName = "X";
                axisName[0] += i;
                if (ImGui::SliderFloat(
                        axisName.c_str(), &m_cuttingPlanes[i],
                        m_mpmSimPtr->getGridMass().getStartPos()[i],
                        m_mpmSimPtr->getGridMass().getEndPos()[i]
                    )) {
                    m_mpmDrawPtr->getParticleShader()->setCuttingPlanes(
                        m_cuttingPlanes
                    );
                }
                ImGui::SameLine();
                if (ImGui::Checkbox(
                        ("Invert " + axisName).c_str(), &m_invertPlanes[i]
                    )) {
                    m_mpmDrawPtr->getParticleShader()->setInvertPlanes(
                        m_invertPlanes[0], m_invertPlanes[1], m_invertPlanes[2]
                    );
                }
            }
            ImGui::TreePop();
        }
        if (ImGui::BeginCombo("Data", current_item)) {
            for (int n = 0; n < items.size(); ++n) {
                bool is_selected = (current_item == items[n]);
                if (ImGui::Selectable(items[n], is_selected)) {
                    current_item = items[n];
                    switch (n) {
                    case 0:
                        m_mpmDrawPtr->setDebugData(Params::DisplayValue::None);
                        break;
                    case 1:
                        m_mpmDrawPtr->setDebugData(
                            Params::DisplayValue::PlasticVolume
                        );
                        break;
                    case 2:
                        m_mpmDrawPtr->setDebugData(
                            Params::DisplayValue::ParticleAltitude
                        );
                        break;
                    case 3:
                        m_mpmDrawPtr->setDebugData(
                            Params::DisplayValue::PackingFraction
                        );
                        break;
                    case 4:
                        m_mpmDrawPtr->setDebugData(
                            Params::DisplayValue::ParticleSpeed
                        );
                        break;
                    case 5:
                        m_mpmDrawPtr->setDebugData(
                            Params::DisplayValue::ParticlePressure
                        );
                        break;
                    }
                }
                if (is_selected) {
                    ImGui::SetItemDefaultFocus();
                }
            }
            ImGui::EndCombo();
        }
        if (ImGui::SliderFloat("Gamma: ", &m_debugGamma, 0.1, 4)) {
            m_mpmDrawPtr->getParticleShader()->setGamma(m_debugGamma);
        }
    }
    if (m_selectedParticle > 0) {
        std::stringstream partSS;
        partSS << "Particle " << m_selectedParticle << ":";
        if (ImGui::CollapsingHeader(
                partSS.str().c_str(), ImGuiTreeNodeFlags_DefaultOpen
            )) {
            std::stringstream ss;
            ss << "Position: " << m_particleData.pos.transpose() << "\n";
            ss << "Velocity: " << m_particleData.vel.transpose() << "\n";
            ss << "Velocity gradient:\n" << m_particleData.C << "\n";
            ss << "Deformation gradient:\n" << m_particleData.F << "\n";
            ss << "Kirchhoff stress:\n" << m_particleData.stress << "\n";
            ss << "Plastic volume change: " << m_particleData.Jp << "\n";
            ss << "Packing fraction: " << m_particleData.pack << "\n";
            ss << "Hardening: " << m_particleData.harden << "\n";
            ImGui::Text("%s", ss.str().c_str());
        }
    }
    ImGui::End();
    //    GL::Renderer::setBlendFunction(GL::Renderer::BlendFunction::One,
    //                                   GL::Renderer::BlendFunction::Zero);
    GL::Renderer::setBlendEquation(
        GL::Renderer::BlendEquation::Add, GL::Renderer::BlendEquation::Add
    );
    GL::Renderer::setBlendFunction(
        GL::Renderer::BlendFunction::SourceAlpha,
        GL::Renderer::BlendFunction::OneMinusSourceAlpha
    );
    // Update application cursor
    m_imgui.updateApplicationCursor(*this);

    /* Set appropriate states. If you only draw ImGui, it is sufficient to
       just enable blending and scissor test in the constructor. */
    // Set state for ImGui interface
    GL::Renderer::disable(GL::Renderer::Feature::FaceCulling);
    GL::Renderer::disable(GL::Renderer::Feature::DepthTest);

    m_imgui.drawFrame();

    swapBuffers();
    redraw();

    // Write image
    if (!m_simulationPaused) {
        // if ((m_imageWriteFreq > 0) && (!(m_frameCounter % m_imageWriteFreq)))
        // {
        //     // Read from framebuffer
        //     const Image2D image = GL::defaultFramebuffer.read(
        //         GL::defaultFramebuffer.viewport(), {PixelFormat::RGBA8Unorm}
        //     );
        //     // File name
        //     std::stringstream numberStream;
        //     numberStream << std::setw(8) << std::setfill('0') <<
        //     m_imageCounter; const std::string outputFile =
        //     m_outputDirectory.string() +
        //                                    "/out_" + numberStream.str() +
        //                                    ".png";
        //     // Write
        //     DEBUG_OUT << "Write " << outputFile << std::endl;
        //     m_imgWriter.convertToFile(image, outputFile);
        //
        //     // Advance
        //     ++m_imageCounter;
        //
        //     if (m_mpmSimPtr->isFinished()) {
        //         exit();
        //     }
        // }
        // ++m_frameCounter;
    }  // m_simulationPaused
}

void Mpm3DApp::viewportEvent(ViewportEvent& event) {
    GL::defaultFramebuffer.setViewport({{}, event.framebufferSize()});
    m_framebuffer.setViewport({{}, event.framebufferSize()});
    m_color.setStorage(
        GL::RenderbufferFormat::RGBA8, GL::defaultFramebuffer.viewport().size()
    );
    m_particleID.setStorage(
        GL::RenderbufferFormat::R32I, GL::defaultFramebuffer.viewport().size()
    );
    m_depth.setStorage(
        GL::RenderbufferFormat::DepthComponent24,
        GL::defaultFramebuffer.viewport().size()
    );

    m_camera->reshape(event.windowSize(), event.framebufferSize());

    m_imgui.relayout(
        Vector2{event.windowSize()} /* / event.dpiScaling()*/,
        event.windowSize(), event.framebufferSize()
    );
}
void Mpm3DApp::keyPressEvent(KeyEvent& event) {
    const auto cameraDist = m_camera->viewDistance();

    if (m_imgui.handleKeyPressEvent(event)) {
        return;
    }

    // Close app
    // if (event.key() == KeyEvent::Key::Esc) {
    //     exit();
    // }

    // Move camera with key
    else if (event.key() == KeyEvent::Key::NumTwo) {
        // Custom
        m_camera->setViewParameters(
            {0.4f, 0.2f, 0.7f}, {0.3f, 0.6f, 0.6f}, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumThree) {
        // Init
        m_camera->setViewParameters(
            m_cameraInit, m_lookAtInit, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumFour) {
        // From +x
        m_camera->setViewParameters(
            {0.5f + cameraDist, 0.5f, 0.5f}, m_lookAtInit, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumSeven) {
        // From -x
        m_camera->setViewParameters(
            {0.5f - cameraDist, 0.5f, 0.5f}, m_lookAtInit, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumFive) {
        // From +y
        m_camera->setViewParameters(
            {0.5f, 0.5f + cameraDist, 0.5f}, m_lookAtInit, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumEight) {
        // From -y
        m_camera->setViewParameters(
            {0.5f, 0.5f - cameraDist, 0.5f}, m_lookAtInit, Vector3::zAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumSix) {
        // From +z
        m_camera->setViewParameters(
            {0.5f, 0.5f, 0.5f + cameraDist}, m_lookAtInit, Vector3::xAxis()
        );
        m_camera->update();
    } else if (event.key() == KeyEvent::Key::NumNine) {
        // From +z
        m_camera->setViewParameters(
            {0.5f, 0.5f, 0.5f - cameraDist}, m_lookAtInit, Vector3::xAxis()
        );
        m_camera->update();
    }

    // Pause simulation
    else if (event.key() == KeyEvent::Key::Space) {
        m_simulationPaused = !m_simulationPaused;
        m_simulationOneStep = false;
    }

    // Simulation step
    else if ((event.key() == KeyEvent::Key::N) && m_simulationPaused) {
        m_simulationOneStep = true;
    }

    // Display grid
    else if (event.key() == KeyEvent::Key::G) {
        m_displayGrid = !m_displayGrid;
    }

    // Change gravity
    else if (event.key() == KeyEvent::Key::Right) {
        m_mpmSimPtr->incGravity(1, 0, 0);
    } else if (event.key() == KeyEvent::Key::Left) {
        m_mpmSimPtr->incGravity(-1, 0, 0);
    } else if (event.key() == KeyEvent::Key::NumOne) {
        m_mpmSimPtr->incGravity(0, 1, 0);
    } else if (event.key() == KeyEvent::Key::NumZero) {
        m_mpmSimPtr->incGravity(0, -1, 0);
    } else if (event.key() == KeyEvent::Key::Down) {
        m_mpmSimPtr->incGravity(0, 0, -1);
    } else if (event.key() == KeyEvent::Key::Up) {
        m_mpmSimPtr->incGravity(0, 0, 1);
    }

    // Control obstacle
    else if (m_mpmSimPtr->getRigidBodyWorld()->nObjects()
             //&& !(m_mpmSimPtr->getObstaclePtr()->isStatic())
    ) {
        // auto obstaclePtr = m_mpmSimPtr->getObstaclePtrNC();
        auto& ffObstaclePtr = m_mpmSimPtr->getRigidBodyWorld()->getObject(0);
        const NumT obsDX = 0.5 * m_mpmSimPtr->getGridMass().getDx().maxCoeff();
        const NumT obsDTheta = M_PI / 50.;
        // Translation
        if (event.key() == KeyEvent::Key::A) {
            // obstaclePtr->displace(Type::Vec3(-obsDX, 0., 0.));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(-obsDX, 0, 0)
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::Q) {
            // obstaclePtr->displace(Type::Vec3(obsDX, 0., 0.));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(obsDX, 0, 0)
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::W) {
            // obstaclePtr->displace(Type::Vec3(0., obsDX, 0.));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(0, obsDX, 0)
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::S) {
            // obstaclePtr->displace(Type::Vec3(0., -obsDX, 0.));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(0, -obsDX, 0)
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::E) {
            // obstaclePtr->displace(Type::Vec3(0., 0., obsDX));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(0, 0, obsDX)
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::D) {
            // obstaclePtr->displace(Type::Vec3(0., 0., -obsDX));
            ffObstaclePtr.setTranslation(
                ffObstaclePtr.getTranslation() + Type::Vec3(0, 0, -obsDX)
            );
            ++m_forceRedraw;
        }
        // Rotation
        else if (event.key() == KeyEvent::Key::J) {
            // obstaclePtr->rotate(Type::Vec3(obsDTheta, 0., 0.));
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(obsDTheta, Type::Vec3(1, 0, 0)) *
                ffObstaclePtr.getRotation()
            );
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::U) {
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(-obsDTheta, Type::Vec3(1, 0, 0)) *
                ffObstaclePtr.getRotation()
            );
            // obstaclePtr->rotate(Type::Vec3(-obsDTheta, 0., 0.));
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::I) {
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(obsDTheta, Type::Vec3(0, 1, 0)) *
                ffObstaclePtr.getRotation()
            );
            // obstaclePtr->rotate(Type::Vec3(0., obsDTheta, 0.));
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::K) {
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(-obsDTheta, Type::Vec3(0, 1, 0)) *
                ffObstaclePtr.getRotation()
            );
            // obstaclePtr->rotate(Type::Vec3(0., -obsDTheta, 0.));
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::O) {
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(obsDTheta, Type::Vec3(0, 0, 1)) *
                ffObstaclePtr.getRotation()
            );
            // obstaclePtr->rotate(Type::Vec3(0., 0., obsDTheta));
            ++m_forceRedraw;
        } else if (event.key() == KeyEvent::Key::L) {
            ffObstaclePtr.setRotation(
                Eigen::AngleAxis<Type::NumT>(-obsDTheta, Type::Vec3(0, 0, 1)) *
                ffObstaclePtr.getRotation()
            );
            // obstaclePtr->rotate(Type::Vec3(0., 0., -obsDTheta));
            ++m_forceRedraw;
        }
    }

    event.setAccepted();
}

void Mpm3DApp::keyReleaseEvent(KeyEvent& event) {
    if (m_imgui.handleKeyReleaseEvent(event))
        return;

    // Force redraw after ending key event
    if (m_simulationPaused && m_forceRedraw) {
        m_forceRedraw = m_maxForceRedraw + 1;
    }

    event.setAccepted();
}

void Mpm3DApp::mousePressEvent(MouseEvent& event) {
    if (m_imgui.handleMousePressEvent(event))
        return;

    if ((event.button() == MouseEvent::Button::Left) ||
        (event.button() == MouseEvent::Button::Middle)) {
        m_camera->initTransformation(event.position());
        m_camera->update();
    }

    event.setAccepted();
    redraw();
}
void Mpm3DApp::mouseReleaseEvent(MouseEvent& event) {
    if (m_imgui.handleMouseReleaseEvent(event))
        return;
    m_camera->update();
    if (event.button() == MouseEvent::Button::Right) {
        const Vector2i position = event.position() *
                                  Vector2{framebufferSize()} /
                                  Vector2{windowSize()};
        const Vector2i fbPosition{
            position.x(),
            GL::defaultFramebuffer.viewport().sizeY() - position.y() - 1};

        m_framebuffer.mapForRead(GL::Framebuffer::ColorAttachment{1});
        Image2D data = m_framebuffer.read(
            Range2Di::fromSize(fbPosition, {1, 1}), {PixelFormat::R32UI}
        );
        m_framebuffer.mapForRead(GL::Framebuffer::ColorAttachment{0});

        m_selectedParticle = data.pixels<Int>()[0][0];
        m_mpmDrawPtr->setSelectedParticle(m_selectedParticle);
        m_particleData = m_mpmSimPtr->getParticleData(m_selectedParticle);
    }
    event.setAccepted();
}

void Mpm3DApp::mouseMoveEvent(MouseMoveEvent& event) {
    if (m_imgui.handleMouseMoveEvent(event))
        return;

    if (!event.buttons())
        return;

    if (event.buttons() == MouseMoveEvent::Button::Left) {
        m_camera->rotate(event.position());
    } else if (event.buttons() == MouseMoveEvent::Button::Middle) {
        m_camera->translate(event.position());
    }
    m_camera->update();

    event.setAccepted();
    redraw();
}

void Mpm3DApp::mouseScrollEvent(MouseScrollEvent& event) {
    if (m_imgui.handleMouseScrollEvent(event)) {
        return;
    }
    /* Prevent scrolling the page */
    // const Float delta = 0.5f * event.offset().y();
    const Float delta = 5.e-2f * event.offset().y();
    // if (Math::abs(delta) < 1.0e-2f) return;

    m_camera->zoom(delta);
    m_camera->update();

    redraw(); /* camera has changed, redraw! */
    event.setAccepted();
}

void Mpm3DApp::textInputEvent(TextInputEvent& event) {
    if (m_imgui.handleTextInputEvent(event))
        return;
}

void Mpm3DApp::updateSystem() {
    if (m_simulationPaused && !m_simulationOneStep) {
        return;
    }

    // Compute
    TIMER_MS_START("[App]", 0);
    auto saveFile = [&]() {
        std::vector<Type::NumT> data;
        NumT time;

        m_mpmSimPtr->dumpParticleData(data, time, true);
        std::stringstream ss;
        ss << m_outputDirectory.string() << "/out_" << std::setw(4)
           << std::setfill('0') << m_stepCounter << ".ply";
        std::string outputFile = ss.str();

        exportDataToPLY(outputFile, false, true, data);
        std::cout << "Saved result to: " << outputFile << std::endl;

        if (m_mpmSimPtr->getRigidBodyWorld()) {
            data.clear();
            m_mpmSimPtr->dumpRigidData(data, time);
            ss.str("");
            ss << m_outputDirectory.string() << "/out_rigid_" << std::setw(4)
               << std::setfill('0') << m_stepCounter << ".ply";
            outputFile = ss.str();
            exportDataToPLY(outputFile, false, true, data);
            std::cout << "Saved rigid body result to: " << outputFile
                      << std::endl;
        }
    };
    if (!m_simulationPaused && !m_mpmSimPtr->isFinished()) {
        if (m_mpmSimPtr->getCurrentSimTime() == 0 && m_particleSaveFreq) {
            saveFile();
        }
        // for (size_t n = 0; n < m_stepsPerFrame; ++n) {
        m_mpmSimPtr->step();
        m_stepCounter++;
        if ((m_particleSaveFreq > 0) &&
            (!(m_stepCounter % m_particleSaveFreq))) {
            saveFile();
        }
        // }  // n
        if (m_mpmSimPtr->isFinished()) {
            m_simulationPaused = true;
        }
    } else {
        m_mpmSimPtr->step();
        m_simulationOneStep = false;
    }
    TIMER_MS_PRINT_CP("Simulation loop");

    // Update visualisation
    m_mpmSimPtr->updateDebugData();
    m_mpmDrawPtr->update();
    TIMER_MS_PRINT_CP("Visualisation");

    TIMER_MS_END;
}

void Mpm3DApp::updateRigidDrawables() {
    for (auto& rigid : m_obstacleDrawables) {
        rigid->updateTransformation();
    }
}

}  // namespace Magnum

int main(int argc, char** argv) {
    CORRADE_RESOURCE_INITIALIZE(MPM_Shaders);
    // Look for a config file argument
    std::string confFilename = "";
    for (int i = 0; i < argc; ++i) {
        std::string arg(argv[i]);
        if (arg.ends_with(".json") || arg.ends_with(".jsonc")) {
            confFilename = arg;
            break;
        }
    }  // i
    if (confFilename == "") {
        std::cerr << "No configuration file provided" << std::endl;
        return EXIT_FAILURE;
    }

    // Load config
    ConfigFileLoader config(confFilename, true);

    // if (!config.gui.useGUI) {
    //     std::cerr << "CLI only does nothing for now" << std::endl;
    //     return EXIT_SUCCESS;
    // }

    // Create GUI App
    Magnum::Mpm3DApp app({argc, argv}, config);

    return app.exec();
}
