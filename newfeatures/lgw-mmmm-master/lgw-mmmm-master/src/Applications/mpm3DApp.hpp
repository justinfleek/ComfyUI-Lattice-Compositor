#ifndef MPM_3D_APP
#define MPM_3D_APP

#include <ctime>
#include <filesystem>
#include <memory>
#include <vector>

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
#include <Magnum/Primitives/Grid.h>
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/Drawable.h>
#include <Magnum/SceneGraph/MatrixTransformation3D.h>
#include <Magnum/SceneGraph/Scene.h>
#include <Magnum/Shaders/PhongGL.h>
#include <Magnum/Trade/MeshData.h>

#include <Magnum/ImGuiIntegration/Context.hpp>

#include <Magnum/Image.h>
#include <Magnum/PixelFormat.h>
#include <MagnumPlugins/PngImageConverter/PngImageConverter.h>

#include "Drawables/ColoredDrawable.h"
#include "Magnum/GL/Framebuffer.h"
#include "Magnum/GL/Renderbuffer.h"
#include "Physics/Mpm3d.hpp"

#include "Cameras/ArcBallCamera.h"
#include "Drawables/MagnumTypes.h"
#include "Drawables/Mpm3dDrawable.hpp"

#include "IO/ConfigFileLoader.hpp"

namespace Magnum {

using namespace Math::Literals;
using namespace Type;

class Mpm3DApp : public Platform::Application {
public:
    /**
     * @brief Application constructor
     *        Default build + init simulation
     * @param arguments
     */
    explicit Mpm3DApp(const Arguments& arguments, ConfigFileLoader& config);

protected:
    ///! Viewer primitives

    /// @brief Draw
    void drawEvent() override;
    /// @brief Viewport event handling
    void viewportEvent(ViewportEvent& event) override;
    /// @brief Key press event handling
    void keyPressEvent(KeyEvent& event) override;
    /// @brief Key release event handling
    void keyReleaseEvent(KeyEvent& event) override;
    /// @brief Mouse press event handling
    void mousePressEvent(MouseEvent& event) override;
    /// @brief Mouse release event handling
    void mouseReleaseEvent(MouseEvent& event) override;
    /// @brief Mouse move event handling
    void mouseMoveEvent(MouseMoveEvent& event) override;
    /// @brief Mouse scroll event handling
    void mouseScrollEvent(MouseScrollEvent& event) override;
    /// @brief Text event handling
    void textInputEvent(TextInputEvent& event) override;

    /// @brief Update movable stuff
    void updateSystem();
    void updateRigidDrawables();

    // Shaders
    std::shared_ptr<Shaders::FlatGL3D> m_flatShader;
    std::shared_ptr<Shaders::PhongGL> m_glPhongShader;
    /// @brief Imgui viewer
    ImGuiIntegration::Context m_imgui{Magnum::NoCreate};

    /// @brief Scene node
    Scene3D m_scene;
    /// @brief MPM node
    Object3D m_mpmObj;
    Object3D m_obstacleObj;
    /// @brief Bounds node
    Object3D m_boundsObj;

    /// @brief 3D Camera
    std::shared_ptr<Camera::ArcBallCamera> m_camera;
    /// @brief Lights - directions to light source
    std::vector<Magnum::Vec4f> m_lightPositions;
    /// @brief Lights
    std::vector<Color3> m_lightColors;

    /// @brief Set of common drawables
    SceneGraph::DrawableGroup3D m_drawables;
    /// @brief Grid drawable
    SceneGraph::DrawableGroup3D m_gridDrawable;
    SceneGraph::DrawableGroup3D m_rigidDrawable;

    /// @brief Bounds mesh
    std::shared_ptr<GL::Mesh> m_boundsMeshGL;
    /// @brief Grid mesh
    std::shared_ptr<GL::Mesh> m_gridMeshGL;
    /// @brief Grid mesh
    std::shared_ptr<GL::Mesh> m_obstacleMeshGL;
    std::vector<std::shared_ptr<GL::Mesh>> m_obstacleMeshesGL;
    std::vector<std::unique_ptr<Object3D>> m_obstacleObjs;
    std::vector<std::unique_ptr<RigidDrawable3D>> m_obstacleDrawables;

    GL::Framebuffer m_framebuffer;
    GL::Renderbuffer m_color, m_particleID, m_depth;
    Int m_selectedParticle = -1;
    MPM::ParticleData m_particleData;

    /// @brief Simulation
    std::shared_ptr<MPM::MPM3D> m_mpmSimPtr;

    /// @brief Drawable
    std::shared_ptr<MPM::MPM3DDrawable> m_mpmDrawPtr;

    float m_rigidOpacity = 1.0f;
    float m_debugGamma = 1.0f;
    Magnum::Vector3 m_cuttingPlanes = {0.0, 0.0, 1.0};
    bool m_invertPlanes[3] = {false, false, true};

    std::array<const char*, 6> items = {"None",
                                        "Plastic volume",
                                        "Particle altitude",
                                        "Packing fraction",
                                        "Particle speed",
                                        "Particle pressure"};

    const char* current_item = items[0];

    /// @brief Image writer
    Trade::PngImageConverter m_imgWriter;

    /// @brief Output directory
    std::filesystem::path m_outputDirectory;
    /// @brief Frame counter
    // size_t m_stepsPerFrame = 0;
    /// @brief Step counter
    size_t m_stepCounter = 0;
    /// @brief Save frequency
    size_t m_particleSaveFreq = 0;

    ///! Callback helpers
    /// @brief Scene center
    const Vec3f m_cameraInit{0.1f, -0.1f, 0.9f};
    /// @brief Scene center
    const Vec3f m_lookAtInit{0.5f, 0.5f, 0.5f};

    /// @brief Pause simulation
    bool m_simulationPaused = true;
    /// @brief Step by step
    bool m_simulationOneStep = false;
    /// @brief Display grid
    bool m_displayGrid = false;
    /// @brief
    int m_forceRedraw = 0;
    /// @brief
    const int m_maxForceRedraw = 3;
};

}  // namespace Magnum

#endif  //  MPM_3D_APP
