#include "IO/ConfigFileLoader.hpp"
#include "Physics/MpmParams.hpp"
#include "Solver/PrimalDual/NonSmoothForces/NonSmoothContactForce.h"
#include "rapidjson/document.h"

#define USE_TIMER
#include "Common/debug.hpp"
#include "Common/timer.hpp"

#include "Grids/DenseGrid3d.cpp"
#include "IO/jsonHelper.hpp"
#include "Physics/Mpm3d.hpp"
#include "Sampling/PoissonDisk.h"

#include <Corrade/Containers/Optional.h>
#include <Magnum/MeshTools/Compile.h>
#include <Magnum/Trade/AbstractImporter.h>
#include <Magnum/Trade/MeshData.h>
#include <igl/readOBJ.h>
#include <cmath>
#include <memory>
#include <stdexcept>

ConfigFileLoader::ConfigFileLoader(std::string filename, bool gui) {
    m_gui = gui;

    const rapidjson::Document document = getJSONDocumentFromFilename(filename);
    if (!document.IsObject()) {
        throw std::invalid_argument(
            "JSON reader - Error: failed parsing the JSON"
        );
    }
    m_configFileFolder = std::filesystem::path(filename).parent_path();

    if (m_gui) {
        loadGUIData(document);
        loadRenderData(document);
    }
    loadPhysicsData(document);
    loadRigidBodyData(document);
    loadOutputData(document);
    loadVolumeData(document);
    loadObstacleData(document);
    loadParticlesData(document);
    // loadGeometryData(document);
}

std::filesystem::path ConfigFileLoader::createOutputDir() {
    size_t directoryNumber = 0;
    std::filesystem::path outputDir;
    if (/*gui.screenshotFreq > 0 ||*/ output.freq > 0) {
        const std::string outputDirectoryBase = output.path;
        do {
            outputDir = std::filesystem::path(
                outputDirectoryBase + std::to_string(directoryNumber)
            );
            ++directoryNumber;
        } while (std::filesystem::is_directory(outputDir));
        std::filesystem::create_directories(outputDir);
        std::cout << "Output dir: " << outputDir << std::endl;
    }

    return outputDir;
}

void ConfigFileLoader::freeAllData() {
    initVolumesPtrs.clear();
    obstacleMeshes.clear();
    m_initialSurfacePtrs.clear();
    m_rigidMeshes.clear();
}

void ConfigFileLoader::loadGUIData(const rapidjson::Document& document) {
    const rapidjson::Value& guiValue = jsonGetValue(document, "GUI");

    // gui.useGUI = jsonRequireBool(guiValue, "Use GUI");
    gui.name = jsonOptionalString(guiValue, "Name", gui.name);
    const rapidjson::Value& sizeArray = jsonRequireArrayCheck(guiValue, "Size");
    for (size_t cmp = 0u; cmp < 2u; ++cmp) {
        gui.size[cmp] = sizeArray[cmp].GetUint();
    }
    // gui.stepsPerFrame = jsonRequireUint(guiValue, "Steps per frame");
    // gui.screenshotFreq =
    //     jsonOptionalUint(guiValue, "Screenshot freq", gui.screenshotFreq);
    const rapidjson::Value& cameraPosArray =
        jsonRequireArrayCheck(guiValue, "Camera position");
    const rapidjson::Value& cameraLookatArray =
        jsonRequireArrayCheck(guiValue, "Camera lookat");
    for (size_t cmp = 0u; cmp < 3u; ++cmp) {
        gui.cameraPosition[cmp] = cameraPosArray[cmp].GetDouble();
        gui.cameraLookAt[cmp] = cameraLookatArray[cmp].GetDouble();
    }

    auto ParseDisplayString = [](const std::string& val
                              ) -> Params::DisplayValue {
        if (val == "None") {
            return Params::DisplayValue::None;
        } else if (val == "ParticleVolume") {
            return Params::DisplayValue::Volume;
        } else if (val == "ParticlePlasticVolume") {
            return Params::DisplayValue::PlasticVolume;
        } else if (val == "ParticleAltitude") {
            return Params::DisplayValue::ParticleAltitude;
        } else if (val == "ParticlePackingFraction") {
            return Params::DisplayValue::PackingFraction;
        } else if (val == "ParticleSpeed") {
            return Params::DisplayValue::ParticleSpeed;
        } else if (val == "ParticlePressure") {
            return Params::DisplayValue::ParticlePressure;
        } else {
            throw std::invalid_argument("Unknown display " + val);
        }
    };

    // Take first particle mode only
    Params::DisplayValue& displayType = gui.pRender.displayType;
    const rapidjson::Value& displayArray =
        jsonGetValue(guiValue, "MPM display");
    if (displayArray.IsArray()) {
        displayType = Params::DisplayValue::None;
        if (displayArray.Begin() != displayArray.End()) {
            const std::string val = displayArray.Begin()->GetString();
            displayType = ParseDisplayString(val);
        }
    } else if (displayArray.IsString()) {
        const std::string val = displayArray.GetString();
        displayType = ParseDisplayString(val);
    }
    gui.pRender.particleScale = jsonOptionalDouble(
        guiValue, "Particle scale", gui.pRender.particleScale
    );
}

void ConfigFileLoader::loadOutputData(const rapidjson::Document& document) {
    const rapidjson::Value& outputValue = jsonGetValue(document, "Output");

    output.path = m_configFileFolder /
                  jsonOptionalString(outputValue, "Directory", output.path);
    output.freq = jsonOptionalUint(outputValue, "Frequency", output.freq);
    output.fsPath = createOutputDir();
}

void ConfigFileLoader::loadVolumeData(const rapidjson::Document& document) {
    const rapidjson::Value& volumesArray =
        jsonRequireArrayCheck(document, "Initial volume");

    for (auto volIt = volumesArray.Begin(); volIt != volumesArray.End();
         ++volIt) {
        const std::string volType = jsonRequireString(*volIt, "Type");

        if (volType == "Box") {
            const rapidjson::Value& minCornerArray =
                jsonRequireArrayCheck(*volIt, "Min corner");
            const rapidjson::Value& maxCornerArray =
                jsonRequireArrayCheck(*volIt, "Max corner");
            const rapidjson::Value& resolutionArray =
                jsonRequireArrayCheck(*volIt, "Resolution");
            Type::Vec3 minCorner, maxCorner;
            Type::Vec3i resolution;
            for (size_t cmp = 0u; cmp < 3u; ++cmp) {
                minCorner[cmp] = minCornerArray[cmp].GetDouble();
                maxCorner[cmp] = maxCornerArray[cmp].GetDouble();
                resolution[cmp] = resolutionArray[cmp].GetInt();
            }
            std::shared_ptr<Params::VolumeCuboid> cubePtr =
                std::make_shared<Params::VolumeCuboid>(
                    minCorner, maxCorner, resolution
                );
            initVolumesPtrs.push_back(cubePtr);
        } else if (volType == "Mesh") {
            // if (jsonOptionalBool(*volIt, "Disabled", false)) {
            //     continue;
            // }
            const std::string filename =
                m_configFileFolder / jsonRequireString(*volIt, "Filename");
            const rapidjson::Value& resolutionArray =
                jsonRequireArrayCheck(*volIt, "Resolution");
            const rapidjson::Value& offsetArray =
                jsonRequireArrayCheck(*volIt, "Offset");
            Type::Vec3i resolution;
            Type::Vec3 offset;
            for (size_t cmp = 0u; cmp < 3u; ++cmp) {
                resolution[cmp] = resolutionArray[cmp].GetInt();
                offset[cmp] = offsetArray[cmp].GetDouble();
            }
            std::shared_ptr<Params::VolumeMesh> meshPtr =
                std::make_shared<Params::VolumeMesh>(
                    filename, resolution, offset
                );
            initVolumesPtrs.push_back(meshPtr);
        } else {
            throw std::invalid_argument("Unknown type " + volType);
        }

        Type::Vec3 vel;
        try {
            const rapidjson::Value& velArray =
                jsonRequireArrayCheck(*volIt, "Velocity");
            for (size_t cmp = 0u; cmp < 3u; ++cmp) {
                vel[cmp] = velArray[cmp].GetDouble();
            }
        } catch (const std::invalid_argument& e) {
            vel.setZero();
        }
        initVolumesPtrs.back()->velocity = vel;
    }  // volIT
}

void ConfigFileLoader::loadObstacleData(const rapidjson::Document& document) {
    const rapidjson::Value::ConstMemberIterator obstacleIt =
        document.FindMember("Obstacle");
    if (obstacleIt == document.MemberEnd()) {
        return;
    }
    const rapidjson::Value& obstacleValue = obstacleIt->value;
    // const rapidjson::Value& obstacleValue = jsonGetValue(document,
    // "Obstacle");
    if (obstacleValue.IsArray()) {
        const rapidjson::Value& obstacleArray =
            jsonRequireArrayCheck(document, "Obstacle");
        for (auto volIt = obstacleArray.Begin(); volIt != obstacleArray.End();
             ++volIt) {
            loadOneObstacle(*volIt);
        }
    } else {
        loadOneObstacle(obstacleValue);
    }
}
void ConfigFileLoader::loadOneObstacle(const rapidjson::Value& obstacleValue) {
    try {
        // if (jsonOptionalBool(obstacleValue, "Disabled", false)) {
        //     return;
        // }
        const std::string filename =
            m_configFileFolder / jsonRequireString(obstacleValue, "Filename");

        const rapidjson::Value& resolutionArray =
            jsonRequireArrayCheck(obstacleValue, "Resolution");
        const rapidjson::Value& offsetArray =
            jsonRequireArrayCheck(obstacleValue, "Offset");
        Type::Vec3i resolution;
        Type::Vec3 offset;
        for (size_t cmp = 0u; cmp < 3u; ++cmp) {
            resolution[cmp] = resolutionArray[cmp].GetInt();
            offset[cmp] = offsetArray[cmp].GetDouble();
        }
        Type::Vec3 vel, angVel;
        try {
            const rapidjson::Value& velArray =
                jsonRequireArrayCheck(obstacleValue, "Velocity");
            for (size_t cmp = 0u; cmp < 3u; ++cmp) {
                vel[cmp] = velArray[cmp].GetDouble();
            }
        } catch (const std::invalid_argument& e) {
            vel.setZero();
        }
        try {
            const rapidjson::Value& angVelArray =
                jsonRequireArrayCheck(obstacleValue, "AngularVelocity");
            for (size_t cmp = 0u; cmp < 3u; ++cmp) {
                angVel[cmp] = angVelArray[cmp].GetDouble();
            }
        } catch (const std::invalid_argument& e) {
            angVel.setZero();
        }
        const Type::NumT density =
            jsonOptionalDouble(obstacleValue, "Density", 1000);
        obstacleMeshes.emplace_back(
            filename, resolution, offset, vel, angVel, density
        );
        obstacleMeshes.back().active =
            jsonOptionalBool(obstacleValue, "Active", false);

    } catch (const std::invalid_argument& e) {
        // No obstacle
        return;
    }
}

void ConfigFileLoader::loadParticlesData(const rapidjson::Document& document) {
    const rapidjson::Value& particlesValue =
        jsonGetValue(document, "Particles");
    physics.particles.size = jsonRequireDouble(particlesValue, "Size");
}

void ConfigFileLoader::loadGeometryData(const rapidjson::Document& document) {
    const rapidjson::Value& geometryValue =
        jsonGetValue(document, "Geometry grid");
    const rapidjson::Value& resolutionArray =
        jsonRequireArrayCheck(geometryValue, "Resolution");
    // for (size_t cmp = 0u; cmp < 3u; ++cmp) {
    //     geometryResolution[cmp] = resolutionArray[cmp].GetInt();
    // }
}

void ConfigFileLoader::loadRigidBodyData(const rapidjson::Document& document) {
    rigidBody.forceSolverType =
        FrictionFrenzy::Solver::ForceSolverType::PrimalDual;
    rigidBody.worldType = FrictionFrenzy::Dynamics::RigidWorldType::EUCLIDEAN;
    rigidBody.gravity = FrictionFrenzy::Vector3(0, 0, -9.81);
    rigidBody.p_solver =
        std::make_unique<FrictionFrenzy::Params::PrimalDualForceSolver>();
    rigidBody.p_rigidWorld =
        std::make_unique<FrictionFrenzy::Params::RigidBodyWorld>();
    auto& solver = *static_cast<FrictionFrenzy::Params::PrimalDualForceSolver*>(
        rigidBody.p_solver.get()
    );
    solver.nonSmoothForceType =
        FrictionFrenzy::Solver::NonSmoothForceType::NON_SMOOTH_CONTACTS;
    solver.p_nonSmoothForce =
        std::make_unique<FrictionFrenzy::Params::NonSmoothContactForce>();
    auto& nonSmoothForce =
        *static_cast<FrictionFrenzy::Params::NonSmoothContactForce*>(
            solver.p_nonSmoothForce.get()
        );
    try {
        const rapidjson::Value& physicsValue =
            jsonGetValue(document, "Rigid body solver");
        rigidBody.adaptiveTimestep = false;
        rigidBody.timestep = physics.dt;
        solver.maxIteration =
            jsonOptionalDouble(physicsValue, "Max iterations", 50);
        solver.tolerance = jsonOptionalDouble(physicsValue, "Tolerance", 1e-4);
        nonSmoothForce.springBasedForce =
            jsonOptionalBool(physicsValue, "Spring-based", false);
        if (nonSmoothForce.springBasedForce) {
            nonSmoothForce.areaBasedSpring =
                jsonOptionalBool(physicsValue, "Area-weighted", false);
            nonSmoothForce.springK = jsonOptionalDouble(
                physicsValue, "Spring K",
                nonSmoothForce.areaBasedSpring ? 1e11 : 1e7
            );
            nonSmoothForce.springDamp =
                jsonOptionalDouble(physicsValue, "Spring damp", 0.01);
        } else {
            nonSmoothForce.restitution =
                jsonOptionalDouble(physicsValue, "Restitution", 0.0);
        }
        nonSmoothForce.frictionCoeff =
            jsonOptionalDouble(physicsValue, "Friction", 0.6);
    } catch (std::invalid_argument& what) {
        std::cout << "No rigid body configuration found! Using default "
                     "configuration.\n";
        rigidBody.adaptiveTimestep = false;
        rigidBody.timestep = physics.dt;
        solver.maxIteration = 50;
        solver.tolerance = 1e-4;
        nonSmoothForce.springBasedForce = false;
        nonSmoothForce.restitution = 0.0;
        nonSmoothForce.frictionCoeff = 0.6;
    }
}

void ConfigFileLoader::loadPhysicsData(const rapidjson::Document& document) {
    const rapidjson::Value& physicsValue = jsonGetValue(document, "Physics");
    const rapidjson::Value& sizeArray =
        jsonRequireArrayCheck(physicsValue, "Size");
    const rapidjson::Value& resolutionArray =
        jsonRequireArrayCheck(physicsValue, "Resolution");
    for (size_t cmp = 0u; cmp < 3u; ++cmp) {
        physics.gridParams.gridEnd[cmp] = sizeArray[cmp].GetDouble();
        physics.gridParams.gridResolution[cmp] = resolutionArray[cmp].GetInt();
    }
    Vec3 resNum =
        (physics.gridParams.gridResolution - Vec3i::Ones()).cast<NumT>();
    NumT smallestX = (physics.gridParams.gridEnd - physics.gridParams.gridStart)
                         .cwiseQuotient(resNum)
                         .minCoeff();
    physics.gridParams.gridEnd = smallestX * resNum;
    std::cout << "New grid size: " << physics.gridParams.gridEnd.transpose()
              << std::endl;

    physics.rho = jsonRequireDouble(physicsValue, "rho");
    physics.dt = jsonRequireDouble(physicsValue, "dt");
    physics.tMax = jsonOptionalDouble(physicsValue, "T max", physics.tMax);
    physics.cfl = jsonOptionalDouble(physicsValue, "CFL", physics.cfl);
    physics.ASFLIP = jsonOptionalDouble(physicsValue, "ASFLIP", physics.ASFLIP);

    // const std::string physFileName =
    //     jsonOptionalString(physicsValue, "Rigid config", "");
    // physics.rigidConfig =
    //     physFileName == "" ? "" : m_configFileFolder / physFileName;

    const rapidjson::Value& elasticityValue =
        jsonGetValue(physicsValue, "Elasticity");
    const std::string elasticityType =
        jsonRequireString(elasticityValue, "Type");
    if (elasticityType == "HenckyStVK") {
        physics.elasticity.type = Params::ElasticityType::HenckyStVK;
        physics.elasticity.E = jsonRequireDouble(elasticityValue, "E");
        physics.elasticity.nu = jsonRequireDouble(elasticityValue, "nu");
    } else if (elasticityType == "HenckyStVKCutting") {
        physics.elasticity.type = Params::ElasticityType::HenckyStVKCutting;
        physics.elasticity.E = jsonRequireDouble(elasticityValue, "E");
        physics.elasticity.nu = jsonRequireDouble(elasticityValue, "nu");
    } else if (elasticityType == "FixedCorotated") {
        physics.elasticity.type = Params::ElasticityType::FixedCorotated;
        physics.elasticity.E = jsonRequireDouble(elasticityValue, "E");
        physics.elasticity.nu = jsonRequireDouble(elasticityValue, "nu");
    } else if (elasticityType == "HenckyMeasured") {
        physics.elasticity.type = Params::ElasticityType::HenckyMeasured;
        physics.elasticity.scale = jsonOptionalDouble(
            elasticityValue, "Scale", physics.elasticity.scale
        );
        physics.elasticity.filename =
            m_configFileFolder / jsonRequireString(elasticityValue, "Filename");
    } else {
        throw std::invalid_argument("Unknown elastic model " + elasticityType);
    }

    const rapidjson::Value& plasticityValue =
        jsonGetValue(physicsValue, "Plasticity");
    const std::string plasticityType =
        jsonRequireString(plasticityValue, "Type");
    if (plasticityType == "Fluid") {
        physics.plasticity.type = Params::PlasticityType::Fluid;
    } else if (plasticityType == "Snow") {
        physics.plasticity.type = Params::PlasticityType::Snow;
    } else if (plasticityType == "SandDP") {
        physics.plasticity.type = Params::PlasticityType::SandDP;
        physics.plasticity.mu =
            jsonOptionalDouble(plasticityValue, "mu", physics.plasticity.mu);
    } else if (plasticityType == "SandMC") {
        physics.plasticity.type = Params::PlasticityType::SandMC;
        physics.plasticity.mu =
            jsonOptionalDouble(plasticityValue, "mu", physics.plasticity.mu);
    } else if (plasticityType == "MeasuredMC") {
        physics.plasticity.type = Params::PlasticityType::MeasuredMC;
        physics.plasticity.scale = jsonOptionalDouble(
            plasticityValue, "Scale", physics.plasticity.scale
        );
        physics.plasticity.filename =
            m_configFileFolder / jsonRequireString(plasticityValue, "Filename");
    } else if (plasticityType == "Test") {
        physics.plasticity.type = Params::PlasticityType::Test;
    } else {
        throw std::invalid_argument("Uknown plastic model " + plasticityType);
    }

    const rapidjson::Value& viscosityValue =
        jsonGetValue(physicsValue, "Viscosity");
    if (!viscosityValue.IsNull() && viscosityValue.IsObject()) {
        physics.viscosity.eta = jsonRequireDouble(viscosityValue, "eta");
        if (physics.viscosity.eta != 0) {
            physics.viscosity.isActive = true;
        }
    } else {
        physics.viscosity.eta = 0.0;
        physics.viscosity.isActive = false;
    }
    std::string volCorrect =
        jsonOptionalString(physicsValue, "Volume correction", "Tampubolon");
    if (volCorrect == "None") {
        physics.volCorrection = Params::VolumeCorrection::None;
    } else if (volCorrect == "Gao") {
        physics.volCorrection = Params::VolumeCorrection::Gao;
    } else if (volCorrect == "Mystery") {
        physics.volCorrection = Params::VolumeCorrection::Mystery;
    } else if (volCorrect == "Tampubolon") {
        physics.volCorrection = Params::VolumeCorrection::Tampubolon;
    }

    const rapidjson::Value& boundariesValue =
        jsonGetValue(physicsValue, "Boundaries");
    physics.boundaries.muWall = jsonOptionalDouble(
        boundariesValue, "mu wall", physics.boundaries.muWall
    );
    physics.boundaries.collisionParticles =
        jsonOptionalBool(boundariesValue, "Wall particles", true);
}

void ConfigFileLoader::loadRenderData(const rapidjson::Document& document) {
    const rapidjson::Value::ConstMemberIterator renderValue =
        document.FindMember("Render");
    if (renderValue != document.MemberEnd()) {
        throw std::invalid_argument(
            "\"Render\" option is now merged with \"GUI\". Adjust the input "
            "file accordingly."
        );
    }
}
