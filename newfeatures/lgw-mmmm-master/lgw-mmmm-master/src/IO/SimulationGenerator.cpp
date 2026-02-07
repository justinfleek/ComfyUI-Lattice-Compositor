#ifndef SIMULATIONGENERATOR_CPP
#define SIMULATIONGENERATOR_CPP

#include "SimulationGenerator.hpp"
#include <Corrade/Containers/Optional.h>
#include <FrictionFrenzy.h>
#include <Magnum/Trade/AbstractImporter.h>
#include <memory>
#include "Dynamics/DynamicSystem.h"
#include "Dynamics/RigidBodyWorld.h"
#include "IO/ConfigFileLoader.hpp"
#include "Magnum/MeshTools/Compile.h"
#include "Magnum/Trade/MeshData.h"
#include "Physics/MpmParams.hpp"
#include "Sampling/PoissonDisk.h"

#include "Physics/Elasticity/ElasticityBase.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Elasticity/HenckyMeasured.hpp"
#include "Physics/Elasticity/HenckyStVK.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/DruckerPragerYield.hpp"
#include "Physics/Plasticity/FluidYield.hpp"
#include "Physics/Plasticity/MeasuredMohrCoulombYield.hpp"
#include "Physics/Plasticity/MohrCoulombYield.hpp"
#include "Physics/Plasticity/SnowYield.hpp"

#define USE_TIMER
#include "Common/debug.hpp"
#include "Common/timer.hpp"

template <bool GUI>
std::shared_ptr<MPM::MPM3D> SimulationGenerator<GUI>::initializeSimulation(
    ConfigFileLoader& config
) {
    TIMER_MS_START("[Sim init]", 1);
    TIMER_MS_PRINT_CP("Generating simulation...");
    generateInitialSurface(config);
    TIMER_MS_PRINT_CP("Initial surface");
    generateParticles(config);
    TIMER_MS_PRINT_CP("Particle sampling");
    generateObstacles(config);
    TIMER_MS_PRINT_CP("Obstacles");
    generateMaterials(config);
    TIMER_MS_PRINT_CP("Materials");
    generateMPMSim(config);
    TIMER_MS_PRINT_CP("Simulation");
    TIMER_MS_END;

    return m_mpmSimPtr;
}

template <bool GUI>
void SimulationGenerator<GUI>::generateInitialSurface(ConfigFileLoader& config
) {
    // Grid and surface parameters
    Params::Grid initGridParams;
    Params::Surface initSurfParams;
    initGridParams = config.physics.gridParams;

    // Create
    for (const auto& volPtr : config.initVolumesPtrs) {
        initGridParams = volPtr->calculateGridParameters();
        m_initialSurfacePtrs.push_back(
            std::make_shared<Base3DSurface>(initGridParams, initSurfParams)
        );

        // Reset
        Grid::DenseGrid3D<Type::NumT>& sdfGrid =
            m_initialSurfacePtrs.back()->getImplGridNC();
        sdfGrid.setConst(1e12);

        // Fill with objects
        volPtr->fillGrid(sdfGrid);
    }

    return;  // m_initialSurfacePtrs;
}

template <bool GUI>
void SimulationGenerator<GUI>::generateParticles(ConfigFileLoader& config) {
    const Vec3i gr = config.physics.gridParams.gridResolution;

    // Sample
    NumT volTot = 0;
    for (size_t surfIdx = 0; surfIdx < m_initialSurfacePtrs.size(); ++surfIdx) {
        const auto& surface = m_initialSurfacePtrs[surfIdx];
        VectorVec3 positions;

        Sampling::poissonDiskSampling3DSurf(
            positions, surface, config.physics.particles.size,
            surface->getImplGridNC().getEndPos(), 0, false
        );
        NumT padding =
            2 * config.physics.gridParams.gridSize()
                    .cwiseQuotient((config.physics.gridParams.gridResolution -
                                    Vec3i::Ones())
                                       .cast<NumT>())
                    .maxCoeff();
        for (auto pos : positions) {
            m_particlesInitial.positions.push_back(pos);
            m_particlesInitial.velocities.push_back(
                config.initVolumesPtrs[surfIdx]->velocity
            );
        }
        volTot += m_initialSurfacePtrs[surfIdx]->getVolume();
    }
    const size_t nbPart = m_particlesInitial.positions.size();
    std::cout << "Number of particles: " << nbPart << std::endl;

    // Compute volume
    const NumT particleBoxVolume = volTot / nbPart;
    config.physics.particles.radius = std::cbrt(particleBoxVolume) / 2.;
    if (config.physics.particles.areSpheres) {
        config.physics.particles.volume =
            (4. * M_PI / 3.) * std::pow(config.physics.particles.radius, 3);
    } else {
        config.physics.particles.volume = particleBoxVolume;
    }
    config.gui.pRender.pRadius = config.physics.particles.radius;
    std::cout << "Shape volume: " << volTot << std::endl;
    std::cout << "Particle volume: " << config.physics.particles.volume * nbPart
              << std::endl;

    const NumT pPerCell = (config.physics.gridParams.gridSize()).prod() /
                          (particleBoxVolume * static_cast<NumT>(gr.prod()));
    config.physics.partPerCell = pPerCell;
    std::cout << "Average part per cell " << pPerCell << std::endl;

    return;  // m_particlesPositions;
}

template <bool GUI>
void SimulationGenerator<GUI>::generateObstacles(ConfigFileLoader& config) {
    using FrictionFrenzy::CollisionObject::CPUMeshData;
    auto convertMagnumMeshData = [](const Magnum::Trade::MeshData& data,
                                    std::unique_ptr<CPUMeshData>& meshData) {
        meshData = std::make_unique<CPUMeshData>();
        for (size_t i = 0; i < data.attributeCount(); ++i) {
            if (data.attributeName(i) ==
                Magnum::Trade::MeshAttribute::Position) {
                const auto pArray =
                    Magnum::Containers::arrayCast<1, const Magnum::Vector3, 2>(
                        data.attribute(i)
                    );
                meshData->positions_Eigen.resize(pArray.size(), 3);
                for (size_t j = 0; j < pArray.size(); ++j) {
                    meshData->positions_Eigen.row(j) << pArray[j].x(),
                        pArray[j].y(), pArray[j].z();
                }
            }
        }
        auto iArrayRaw = data.indicesAsArray();
        auto iArray =
            Magnum::Containers::arrayCast<Magnum::Vector3ui>(iArrayRaw);
        meshData->indices_Eigen =
            std::make_shared<FrictionFrenzy::MatrixX3i>(iArray.size(), 3);
        for (size_t j = 0; j < iArray.size(); ++j) {
            (*meshData->indices_Eigen)(j, 0) = iArray[j][0];
            (*meshData->indices_Eigen)(j, 1) = iArray[j][1];
            (*meshData->indices_Eigen)(j, 2) = iArray[j][2];
        }
    };

    mp_rigidBodyDynamics =
        std::make_unique<FrictionFrenzy::Dynamics::DynamicSystem>(
            std::make_shared<unsigned int>(0)
        );
    mp_rigidBodyDynamics->fillFromParams(config.rigidBody);

    for (auto& obstacleMesh : config.obstacleMeshes) {
        if (obstacleMesh.filename != "") {
            Magnum::PluginManager::Manager<Magnum::Trade::AbstractImporter>
                manager;
            Corrade::Containers::Pointer<Magnum::Trade::AbstractImporter>
                importer = manager.loadAndInstantiate("ObjImporter");
            if (!importer || !importer->openFile(obstacleMesh.filename)) {
                throw std::runtime_error(
                    "Error while reading obj: " + obstacleMesh.filename
                );
            };
            std::unique_ptr<CPUMeshData> ffMeshData;
            convertMagnumMeshData(*(importer->mesh(0)), ffMeshData);

            std::unique_ptr<FrictionFrenzy::CollisionObject::Mesh> p_mesh =
                std::make_unique<FrictionFrenzy::CollisionObject::Mesh>(
                    mp_rigidBodyDynamics->nObjects(), ffMeshData.get(),
                    ffMeshData.get()
                );
            p_mesh->setGridSDF(obstacleMesh.resolution.maxCoeff());
            mp_rigidBodyDynamics->addMesh(std::move(ffMeshData));
            mp_rigidBodyDynamics->addObject(std::move(p_mesh));

            if constexpr (GUI) {
                std::shared_ptr<Magnum::GL::Mesh> rigidPtr =
                    std::make_shared<Magnum::GL::Mesh>(Magnum::NoCreate);
                *rigidPtr = Magnum::MeshTools::compile(
                    *(importer->mesh(0)),
                    Magnum::MeshTools::CompileFlags{
                        Magnum::MeshTools::CompileFlag::GenerateSmoothNormals}
                );
                m_rigidMeshes.push_back(rigidPtr);
            }
        }
    }
    mp_rigidBodyDynamics->initialize();
    for (int objIt = 0; objIt < mp_rigidBodyDynamics->nObjects(); ++objIt) {
        auto& obj = mp_rigidBodyDynamics->getObject(objIt);
        obj.setTranslation(
            obj.getTranslation() + config.obstacleMeshes[objIt].offset
        );
        obj.velocity() = config.obstacleMeshes[objIt].velocity;
        obj.angularVel() = config.obstacleMeshes[objIt].angVel;
        obj.setStatic(!config.obstacleMeshes[objIt].active);
        obj.updateDensity(config.obstacleMeshes[objIt].density);
    }
}

template <bool GUI>
void SimulationGenerator<GUI>::generateMaterials(ConfigFileLoader& config) {
    const Params::Physics& physParams = config.physics;
    if (physParams.elasticity.type == Params::ElasticityType::FixedCorotated) {
        m_materials.elastic = std::make_unique<MPM::Elastic::FixedCorotated>(
            physParams.elasticity.E, physParams.elasticity.nu
        );
    } else if (physParams.elasticity.type == Params::ElasticityType::HenckyStVK) {
        m_materials.elastic = std::make_unique<MPM::Elastic::HenckyStVK>(
            physParams.elasticity.E, physParams.elasticity.nu
        );
    } else if (physParams.elasticity.type == Params::ElasticityType::HenckyStVKCutting) {
        m_materials.elastic = std::make_unique<MPM::Elastic::HenckyStVKCutting>(
            physParams.elasticity.E, physParams.elasticity.nu
        );
    } else if (physParams.elasticity.type == Params::ElasticityType::HenckyMeasured) {
        m_materials.elastic = std::make_unique<MPM::Elastic::HenckyMeasured>(
            physParams.elasticity.filename, physParams.elasticity.scale
        );
    }

    if (physParams.plasticity.type == Params::PlasticityType::Snow) {
        m_materials.hardening =
            std::make_unique<MPM::Hardening::ExpHardening>();
        m_materials.plastic = std::make_unique<MPM::Plastic::SnowYield>();
    } else {
        m_materials.hardening = std::make_unique<MPM::Hardening::NoHardening>();
        if (physParams.plasticity.type == Params::PlasticityType::Fluid) {
            m_materials.plastic = std::make_unique<MPM::Plastic::FluidYield>();
        } else if (physParams.plasticity.type == Params::PlasticityType::SandMC) {
            m_materials.plastic =
                std::make_unique<MPM::Plastic::MohrCoulombYield>(
                    physParams.plasticity.mu
                );
        } else if (physParams.plasticity.type == Params::PlasticityType::SandDP) {
            m_materials.plastic =
                std::make_unique<MPM::Plastic::DruckerPragerYield>(
                    physParams.plasticity.mu
                );
        } else if (physParams.plasticity.type == Params::PlasticityType::MeasuredMC) {
            m_materials.plastic =
                std::make_unique<MPM::Plastic::MeasuredMohrCoulombYield>(
                    physParams.plasticity.filename, physParams.plasticity.scale
                );
        } else {
            m_materials.plastic =
                std::make_unique<MPM::Plastic::YieldSurfaceBase>();
        }
    }
}

template <bool GUI>
std::shared_ptr<MPM::MPM3D> SimulationGenerator<GUI>::generateMPMSim(
    ConfigFileLoader& config
) {
    // Geometry grid parameters
    // Params::Surface mpmSurfParams;

    m_mpmSimPtr = std::make_shared<MPM::MPM3D>(
        config.physics, std::move(m_materials), std::move(m_particlesInitial),
        mp_rigidBodyDynamics, /*mpmSurfParams,*/ config.gui.pRender.displayType
    );

    return m_mpmSimPtr;
}

template <bool GUI>
std::vector<std::shared_ptr<Magnum::GL::Mesh>>&
SimulationGenerator<GUI>::getRigidMeshes() {
    return m_rigidMeshes;
}

template <bool GUI>
void SimulationGenerator<GUI>::freeAllData() {
    m_initialSurfacePtrs.clear();
    m_rigidMeshes.clear();
}

#endif
