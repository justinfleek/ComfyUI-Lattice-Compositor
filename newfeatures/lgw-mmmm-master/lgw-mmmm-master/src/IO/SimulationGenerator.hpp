#ifndef SIMULATIONGENERATOR_HPP
#define SIMULATIONGENERATOR_HPP

#include <Magnum/GL/Mesh.h>
#include <type_traits>
#include "IO/ConfigFileLoader.hpp"
#include "Physics/Elasticity/ElasticityBase.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Mpm3d.hpp"

template <bool GUI>
class SimulationGenerator {
public:
    std::shared_ptr<MPM::MPM3D> initializeSimulation(ConfigFileLoader& config);
    void generateInitialSurface(ConfigFileLoader& config);
    void generateParticles(ConfigFileLoader& config);
    void generateObstacles(ConfigFileLoader& config);
    void generateMaterials(ConfigFileLoader& config);
    std::shared_ptr<MPM::MPM3D> generateMPMSim(ConfigFileLoader& config);
    std::filesystem::path createOutputDir(const ConfigFileLoader& config);
    std::vector<std::shared_ptr<Magnum::GL::Mesh>>& getRigidMeshes();

    void freeAllData();

private:
    //! Helper functions and data
    std::vector<std::shared_ptr<Base3DSurface>> m_initialSurfacePtrs;

    MPM::Material m_materials;
    // std::unique_ptr<MPM::Elastic::ElasticityBase> mp_elastic;
    // std::unique_ptr<MPM::Plastic::YieldSurfaceBase> mp_plastic;
    // std::unique_ptr<MPM::Hardening::HardeningBase> mp_hardening;

    MPM::ParticleInitialData m_particlesInitial;
    std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem>
        mp_rigidBodyDynamics = nullptr;
    std::shared_ptr<MPM::MPM3D> m_mpmSimPtr = nullptr;
    std::filesystem::path m_configFileFolder;

    std::conditional_t<
        GUI, std::vector<std::shared_ptr<Magnum::GL::Mesh>>, char>
        m_rigidMeshes;
    // std::vector<std::shared_ptr<Magnum::GL::Mesh>> m_rigidMeshes;
    bool m_gui = true;
    /**
     * @brief Load obstacle for sim
     */
};

#include "SimulationGenerator.cpp"

#endif
