#ifndef CONFIG_FILE_LOADER_HPP
#define CONFIG_FILE_LOADER_HPP

#include <Magnum/GL/Mesh.h>
#include <filesystem>
#include <memory>
#include <vector>
#include "Common/CustomTypes.hpp"
#include "Common/Utils.hpp"
#include "Drawables/ColoredDrawable.h"
#include "Drawables/MagnumTypes.h"
#include "Geometry/Base3dSurface.hpp"
#include "Geometry/GeometryParams.hpp"
#include "Geometry/MeshLevelSet3d.hpp"
#include "Grids/Grid.h"
#include "IO/jsonHelper.hpp"
#include "Physics/Mpm3d.hpp"

// Use nested structs for easier access to the data
namespace Params {
struct GUI {
    std::string name = "MPM sim";                        //! Name
    Magnum::Vec2i size = {1000, 1000};                   //! GUI size
    Magnum::Vec3 cameraPosition = {-0.1f, -0.2f, 0.9f};  //! Camera position
    Magnum::Vec3 cameraLookAt = {0.5f, 0.5f, 0.5f};      //! Camera lookat
    std::vector<Magnum::Vec4f> lightPositions = {
        {-1.0f, -1.0f, 0.25f, 0},
        {1.0f, 1.f, 0.55f, 0}};  //! Lights positions/directions?
    std::vector<Magnum::Color3> lightColors = {
        Magnum::Color3(0.75f, 0.75f, 0.75f),
        Magnum::Color3(1.f, 1.f, 1.f)};  //! Lights colors
    Params::Rendering pRender;
};

struct Output {
    std::filesystem::path fsPath;
    std::string path = "./out";  //! Used only for screenshots for now
    size_t freq = 0;
};  // output
}  // namespace Params

struct ConfigFileLoader {
    // using namespace Settings;
public:
    //! Methods
    /**
     * @brief Constructor
     * @param filename JSON file to load
     */
    ConfigFileLoader(std::string filename, bool gui);

    /**
     * @brief Create the output directory - only if screenshots are required
     */
    std::filesystem::path createOutputDir();

    /**
     * @brief Free all data so that they don't hog resources while simulation is
     * running.
     */
    void freeAllData();

    //! Raw data

    //! GUI if used
    Params::GUI gui;

    Params::Output output;

    //! Initial volumes to fill with particles
    std::vector<std::shared_ptr<Params::Volume>> initVolumesPtrs;

    //! Obstacle is a mesh volume that can move
    std::vector<Params::ObstacleMesh> obstacleMeshes;

    FrictionFrenzy::Params::DynamicSystem rigidBody;
    Params::Physics physics;

private:
    //! Helper functions and data
    std::vector<std::shared_ptr<Base3DSurface>> m_initialSurfacePtrs;

    MPM::ParticleInitialData m_particlesInitial;
    std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem>
        mp_rigidBodyDynamics = nullptr;
    std::shared_ptr<MPM::MPM3D> m_mpmSimPtr = nullptr;
    std::filesystem::path m_configFileFolder;

    std::vector<std::shared_ptr<Magnum::GL::Mesh>> m_rigidMeshes;
    bool m_gui = true;
    /**
     * @brief Load obstacle for sim
     */
    void generateObstacles();

    /**
     * @brief
     */
    void loadGUIData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadOutputData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadVolumeData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadOneObstacle(const rapidjson::Value& obstacleValue);
    void loadObstacleData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadParticlesData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadGeometryData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadPhysicsData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadRigidBodyData(const rapidjson::Document& document);
    /**
     * @brief
     */
    void loadRenderData(const rapidjson::Document& document);

};  // ConfigFileLoader

#endif  // CONFIG_FILE_LOADER_HPP
