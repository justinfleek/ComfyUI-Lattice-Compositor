#ifndef MPM_3D_APP
#define MPM_3D_APP

#include <filesystem>
#include <memory>

#include "IO/ConfigFileLoader.hpp"
#include "Physics/Mpm3d.hpp"

class CLIMpm3DApp {
public:
    /**
     * @brief Application constructor
     *        Default build + init simulation
     * @param arguments
     */
    explicit CLIMpm3DApp(ConfigFileLoader& config);
    ~CLIMpm3DApp(){};
    int run() { return exec(); }

protected:
    ///! Viewer primitives
    int exec();

    /// @brief Update movable stuff
    void updateSystem();

    /// @brief Simulation
    std::shared_ptr<MPM::MPM3D> m_mpmSimPtr;

    /// @brief Output directory
    std::filesystem::path m_outputDirectory;
    // /// @brief Frame counter
    // size_t m_stepsPerFrame = 0;
    /// @brief Step counter
    size_t m_stepCounter = 0;
    /// @brief Save frequency
    size_t m_particleSaveFreq = 0;
};

#endif  //  MPM_3D_APP
