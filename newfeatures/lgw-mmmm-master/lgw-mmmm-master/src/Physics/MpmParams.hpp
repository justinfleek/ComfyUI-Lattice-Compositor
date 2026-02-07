#ifndef _MPM_PARAMS_HPP
#define _MPM_PARAMS_HPP

#include <filesystem>
#include "Common/CustomTypes.hpp"
#include "Grids/GridParameters.hpp"
// #include "Physics/MpmTypes.hpp"

namespace Params {
enum class ElasticityType {
    None,
    HenckyStVK,
    HenckyStVKCutting,
    FixedCorotated,
    HenckyMeasured,
    N_TYPES
};

struct Elasticity {
    ElasticityType type = ElasticityType::HenckyStVK;
    std::filesystem::path filename;
    Type::NumT scale = 1.0;
    Type::NumT E = 2.e4;  /// @brief Young Modulus (Pa)
    Type::NumT nu = 0.4;  /// @brief Poisson ratio (.)
};                        // Elasticity

enum class PlasticityType {
    None,
    Fluid,
    Snow,
    SandDP,
    SandMC,
    MeasuredMC,
    Test
};

enum class VolumeCorrection { None, Tampubolon, Gao, Mystery, N_SCHEMES };

// Change if more parameters
struct Plasticity {
    PlasticityType type = PlasticityType::None;
    std::filesystem::path filename;
    Type::NumT scale = 1.0;
    Type::NumT mu = 0.6;  // Friction for sand
};                        // Elasticity

struct Viscosity {
    bool isActive = false;
    Type::NumT eta = 1.e2;  /// @brief Dynamic viscosity
};                          // Elasticity

struct Boundaries {
    bool collisionParticles = false;
    // Wall friction
    Type::NumT muWall = 0.2;
};

// /// @brief Color scheme for the particles
enum class DisplayValue : u_int8_t {
    None,
    Volume,
    PlasticVolume,
    ParticleAltitude,
    PackingFraction,
    ParticleSpeed,
    ParticlePressure,
    ParticleValueMask
};

struct Particles {
    Type::NumT size = 1.5e-2;  //! Sampling parameter
    bool areSpheres = true;    //! if false, the particle volume is
                               //! Vb=totalVolume/nbParts, if true = volume of
                               //! the sphere inscribed in a cube of volume Vb
    Type::NumT radius = 0.0;   //! tbc
    Type::NumT volume = 0.0;   //! tbc
};                             // Particles

//! Physical parameters
struct Physics {
    Grid gridParams;
    Particles particles;
    Type::NumT rho = 5.e2;     //! Mass density of the particles
    Type::NumT dt = 5.e-4;     //! Timestep
    Type::NumT cfl = 0.85;     //! Timestep
    Type::NumT tMax = 0.0;     //! max time
    Type::NumT ASFLIP = 0.95;  //! Aspic coeff
    Type::NumT partPerCell;
    Elasticity elasticity;
    Plasticity plasticity;
    Viscosity viscosity;
    Boundaries boundaries;
    // std::string rigidConfig;

    VolumeCorrection volCorrection = VolumeCorrection::Tampubolon;
};  // Physics

struct Surface {
    bool enable = false;
};

struct Rendering {
    /// @brief Radius for the particle rendering
    Type::NumT particleScale = 1.0;
    Type::NumT pRadius = 5.e-3;
    DisplayValue displayType = DisplayValue::None;
};
}  // namespace Params

#endif  // _MPM_PARAMS_HPP
