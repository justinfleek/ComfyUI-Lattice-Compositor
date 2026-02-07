#ifndef _MPM3D_HPP
#define _MPM3D_HPP

// Uncomment the following macro to use spase grids for MPM. No further
// adjustment should be necessary!

#define USE_SPARSE_GRID

#include "Common/CustomTypes.hpp"
#include "Geometry/Base3dSurface.hpp"
#include "Grids/Grid.h"
#include "Physics/Elasticity/ElasticityBase.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/YieldSurfaceBase.hpp"

#include <FrictionFrenzy.h>
#include <memory>
#include <vector>

namespace MPM {

using namespace Type;

struct ParticleInitialData {
    VectorVec3 positions;
    VectorVec3 velocities;
};

struct ParticleDebugData {
    std::vector<NumT> data;
    NumT min, max;
};

// Data for single particle. Only used for debug visualization
struct ParticleData {
    Vec3 pos;
    Vec3 vel;
    Mat3 C;
    Mat3 F;
    Mat3 stress;
    NumT Jp;
    NumT harden;
    NumT pack;
};

struct Material {
    std::unique_ptr<Elastic::ElasticityBase> elastic;
    std::unique_ptr<Plastic::YieldSurfaceBase> plastic;
    std::unique_ptr<Hardening::HardeningBase> hardening;
};

#ifdef USE_SPARSE_GRID
static constexpr int BlockPow = 4;

using MassGridType = Grid::BlockGrid3D<NumT, BlockPow>;
using VelGridType = Grid::BlockGrid3D<Vec3, BlockPow>;

#else
using MassGridType = Grid::DenseGrid3D<NumT>;
using VelGridType = Grid::DenseGrid3D<Vec3>;

#endif

class MPM3D {
public:
    /**
     * @brief Constructor
     * @param pPositionsPtr Initial particle positions
     * @param surfInitPtr
     * @param gridResolution Size of the grid
     * @param gridScale Size of the domain to simulate, default 1mx1m
     * @param surfParams
     * @param debugParams
     */
    MPM3D(
        const Params::Physics physParams, Material&& material,
        ParticleInitialData&& pInitialData,
        std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem>
            rigidBodyDynamics = nullptr,
        const Params::DisplayValue debugParams = Params::DisplayValue::None
    );

    /// @brief Destructor
    virtual ~MPM3D();

    /**
     * @brief
     * @return
     */
    bool isFinished() const;

    /**
     * @brief Read the physical parameters
     * @return const ref
     */
    const Params::Physics& getPhysParameters() const;
    Params::Physics& getPhysParameters();
    /**
     * @brief Read the grid parameters
     * @return const ref
     */
    const Params::Grid& getGridParameters() const;
    /**
     * @brief Read the debug parameters
     * @return const ref
     */
    const Params::DisplayValue& getDebugParameters() const;
    Params::DisplayValue& getDebugParameters();
    /**
     * @brief Read the debug parameters
     * @return const ref
     */
    // const Params::Surface& getSurfParameters() const;

    /**
     * @brief Read the positions
     * @return const ptr
     */
    const VectorVec3& getPartPosPtr() const;

    /**
     * @brief Read the particles volumes
     * @return const ref
     */
    const VectorNumT& getPartPlasticVolumes() const;

    /**
     * @brief Get the debug tracked value
     * @return const ref
     */
    const ParticleDebugData& getPartDebugData() const;

    /**
     * @brief Access to the grid mass
     * @return
     */
    const MassGridType& getGridMass() const;
    /**
     * @brief Access to the grid mass - non const version
     * @return
     */
    MassGridType& getGridMassNC();
    /**
     * @brief Access to the grid mass gradient
     * @return
     */
    // const Grid::DenseGrid2D<Vec2>& getGridMassGrad() const;

    /**
     * @brief Access to the grid velocities
     * @return
     */
    const VelGridType& getGridVel() const;

    /**
     * @brief Access to the initial surface
     * @return
     */
    const std::shared_ptr<Base3DSurface> getSurfaceInitPtr() const;

    std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem> getRigidBodyWorld(
    ) {
        return mp_rigidBodyDynamics;
    }

    const VectorI& getParticleIDArray() const { return m_pPartOrder; }

    /**
     * @brief Access to the surface tracking
     * @return
     */
    // const MPM3DSurface* getSurfaceTracker() const;

    NumT getCurrentSimTime() const { return m_t; }

    ParticleData getParticleData(int pId) const;

    /// @brief Compute a timestep
    void step();

    /// @brief Update debug datas
    void updateDebugData();

    /// Callbacks

    /**
     * @brief Increase gravity
     * @param gx  Difference in g along x
     * @param gy  Difference in g along y
     */
    void incGravity(int gx, int gy, int gz);

    /**
     * @brief Dump particle data for output
     */
    void dumpParticleData(
        std::vector<NumT>& data, NumT& currTime, bool rotationOnly = false
    );
    void dumpRigidData(std::vector<NumT>& data, NumT& currTime);

private:
    static constexpr int particleSortPow = 2;

    /// @brief Pre-sim
    void preStep();
    void sortParticles();
    /// @brief Sim
    void coreStep();
    /// @brief Sim - helper
    void coreStepP2GWithAtomic();
    void coreStepP2G();

    /// P2G per-particle steps
    inline void projectParticle(
        Mat3& Fp, Mat3& U, Vec3& sig, Mat3& V, NumT& Jp, NumT& hard
    );
    inline void enforceVolumePreservation(
        Mat3& Fp, Mat3& U, Vec3& sig, Mat3& V, Mat3& Cp, NumT& J, NumT mass,
        bool nearRigid
    );
    NumT particleP2G(
        const Vec3& pos, const Vec3& vel, const Mat3& Cp, const Mat3& affine,
        const Mat3& stress
    );
    template <int N>
    inline NumT particleP2GNoAtomic(
        const Vec3i& blockOffset, const Vec3& pos, const Vec3& vel,
        const Mat3& affine, const Mat3& stress,
        Grid::DenseGrid3D<NumT, N>& massGrid,
        Grid::DenseGrid3D<Vec3, N>& velGrid,
        Grid::DenseGrid3D<Vec3, N>& velOldGrid
    );
    inline void timestepLimits(
        const Vec3& vel, const Mat3& U, const Vec3& sig, const Mat3& Cp,
        const Mat3& kStress, const NumT hard, NumT& waveSpeed, NumT& Vmin,
        NumT& Cmin
    );

    /// @brief Sim - helper
    void determineTimeStep();
    /// @brief Sim - helper
    /// @brief Sim - helper
    void coupleRigidBodies();
    void coreStepGridStep();
    void coreStepGridMirror();
    void coreStepGridEnforce();
    inline std::pair<Vec3, Vec3i> pointToGridPos(const Vec3& pos) {
        Vec3 mPos = m_grid.pos2fracijk(pos);
        Vec3i base = (mPos.array() - 0.5).cast<int>();
        return {mPos, base};
    }
    inline Vec3i pointToKernelLowerBound(const Vec3& pos) {
        Vec3 mPos = m_grid.pos2fracijk(pos);
        Vec3i base = (mPos.array() - 0.5).cast<int>();
        return base;
    }

    std::vector<std::pair<size_t, Vec3>> getRigidBodiesToucingPoint(Vec3 point);

    bool resolveCollision(
        const Vec3& normal, const NumT mu, Vec3& velocity,
        const Vec3& refVel = Vec3::Zero()
    );

    /// @brief Sim - helper
    void coreStepG2P();
    /// @brief Post-sim
    void postStep();

    /// @brief Helper
    void clampPos(Vec3& pos, Vec3& vel);

    /**
     * @brief
     */
    Vec3 externalForces(const Vec3& pos, NumT mass, NumT time);

    std::tuple<Vec3i, Vec3, Vec3, Vec3, Vec3> getP2GCoordinates(const Vec3& pos
    );

    //// Particles data
    /// @brief Number of particles
    const size_t m_nPart;
    /// @brief Particle positions
    VectorVec3 m_pPos;
    VectorNumT m_pG2PMass;
    /// @brief Particle velocities
    VectorVec3 m_pVel;
    /// @brief Affine velocity field
    VectorMat3 m_pC;
    /// @brief Deformation Gradient
    VectorMat3 m_pF;
    /// @brief Plastic volume
    VectorNumT m_pJp;
    /// @brief Sand: Volume correction
    // VectorNumT m_pDPVolumeCorrection;
    VectorNumT m_pHard;
    VectorI m_pNearRigid;
    VectorI m_pPartOrder;
    VectorI m_pInvPartOrder;

    /// @brief Particle ordering
    std::vector<std::pair<size_t, size_t>> m_pOrder;
    std::vector<size_t> m_pBlockOffset;
    std::array<size_t, 9> m_pBlockGroupOffset;
    int m_orderingIter;

    //// Grid data
    /// @brief Grid parameters
    Params::Grid m_gridParams;

    /// @brief Grid masses
    MassGridType m_gMass;
    /// @brief Grid velocities
    VelGridType m_gVel;
    /// @brief Grid velocities before forces. Used for ASFLIP and FLIP
    VelGridType m_gVelOld;
    /// @brief Dummy grid reference to extract grid parameters from, e.g. grid
    /// dimensions, dx, etc. Makes code a bit more readable.
    const MassGridType& m_grid;
    /// @brief Empty cells for the border
    static constexpr int m_border = 2;

    /// Physical parameters
    Params::Physics m_physParams;  /// @brief User set parameters
    const NumT m_pMass;            /// @brief Particle mass

    int m_gX = 0;                /// @brief Gravity (int) in x
    int m_gY = 0;                /// @brief Gravity (int) in y
    int m_gZ = -1;               /// @brief Gravity (int) in y
    Vec3 m_g = {0., 0., -9.81};  /// @brief Gravity

    double m_t;  /// @brief Time
    NumT m_dt;  /// @brief Time step size. Can be different from m_physParams.dt
                /// due to adaptive timestepping.
    NumT m_dtOld;
    NumT m_dtRemain;
    NumT m_maxWaveSpeed;
    NumT m_dtCLim, m_dtVLim, m_dtPart;
    NumT m_hardMax;
    NumT m_asflipCoeff;
    unsigned int m_iter = 0;  /// @brief Iteration

    /// @brief Debug
    Params::DisplayValue m_debugParams;
    /// @brief Additional tracked value
    ParticleDebugData m_partDebugData;
    // VectorNumT m_colorValue;

    /// Surface
    /// @brief Init surface
    // const std::shared_ptr<Base3DSurface> m_surfInitPtr;

    /// @brief
    std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem>
        mp_rigidBodyDynamics;

    /// @brief Surface tracker
    // std::unique_ptr<MPM3DSurface> mp_surfTracker;

    /// @brief Controls
    // Grid::DenseGrid3D<int> m_gControlGroup;

    /// @brief Elasticity
    std::unique_ptr<Elastic::ElasticityBase> mp_elasticity;
    std::unique_ptr<Plastic::YieldSurfaceBase> mp_yield;
    std::unique_ptr<Hardening::HardeningBase> mp_hardening;

};  // class MPM3D

}  // namespace MPM

#endif  // #MPM3D_HPP
