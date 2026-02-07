#include "Mpm3d.hpp"
#include <Eigen/src/Core/util/Constants.h>
#include <Eigen/src/Geometry/Quaternion.h>
#include <Eigen/src/SVD/JacobiSVD.h>
#include <omp.h>

// #define USE_TIMER
#include "Common/CustomTypes.hpp"
#include "Common/Utils.tpp"
#include "Common/timer.hpp"

// #define USE_DEBUG_OUTSTREAM
#include "Common/debug.hpp"
#include "Physics/Elasticity/ElasticityBase.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Elasticity/HenckyMeasured.hpp"
#include "Physics/Elasticity/HenckyStVK.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/MpmParams.hpp"
#include "Physics/Plasticity/DruckerPragerYield.hpp"
#include "Physics/Plasticity/FluidYield.hpp"
#include "Physics/Plasticity/MeasuredMohrCoulombYield.hpp"
#include "Physics/Plasticity/MohrCoulombYield.hpp"
#include "Physics/Plasticity/SnowYield.hpp"

#include <Eigen/SVD>
#include <algorithm>
#include <cmath>
#include <iostream>
#include <memory>
#include <numeric>
#include <stdexcept>

namespace MPM {

using namespace Type;

MPM3D::MPM3D(
    const Params::Physics physParams, Material&& material,
    ParticleInitialData&& pInitialData,
    std::shared_ptr<FrictionFrenzy::Dynamics::DynamicSystem> rigidBodySystem,
    const Params::DisplayValue debugParams
)
    : m_nPart(pInitialData.positions.size()),
      m_pPos(std::move(pInitialData.positions)),
      m_pVel(std::move(pInitialData.velocities)),
      m_gridParams(physParams.gridParams),
      m_gMass(m_gridParams),
      m_gVel(m_gridParams),
      m_gVelOld(m_gridParams),
      m_grid(m_gMass),
      m_physParams(physParams),
      m_pMass(physParams.rho * physParams.particles.volume),
      m_asflipCoeff(physParams.ASFLIP),
      m_t(0.),
      m_debugParams(debugParams),
      mp_rigidBodyDynamics(rigidBodySystem),
      mp_elasticity(std::move(material.elastic)),
      mp_yield(std::move(material.plastic)),
      mp_hardening(std::move(material.hardening)) {
    TIMER_MS_START("[SimInit]", 1);

    // Initialize particle arrays
    m_pC.resize(m_nPart, Zero3x3);
    m_pF.resize(m_nPart, Id3x3);
    m_pJp.resize(m_nPart, 1.f);
    m_pHard.resize(m_nPart, 0.f);
    m_pG2PMass.resize(m_nPart, 0);
    m_pOrder.resize(m_nPart);
    m_pNearRigid.resize(m_nPart, 0);
    m_pPartOrder.resize(m_nPart);
    m_pInvPartOrder.resize(m_nPart);
    m_partDebugData.data.resize(m_nPart, 1);
    std::iota(m_pPartOrder.begin(), m_pPartOrder.end(), 0);
    std::iota(m_pInvPartOrder.begin(), m_pInvPartOrder.end(), 0);

    // Initialize grids
    m_gMass.setConst(0);
    m_gVel.setConst(Zero3);
    m_gVelOld.setConst(Zero3);

    // Set stuff to zero
    m_orderingIter = 0;
    m_dt = 0;
    mp_rigidBodyDynamics->gravity() = m_g;

    // Clamp initial data
#pragma omp parallel for
    for (size_t pId = 0; pId < m_nPart; ++pId) {
        Vec3& pos = m_pPos[pId];
        Vec3& vel = m_pVel[pId];
        clampPos(pos, vel);
        m_pHard[pId] = mp_hardening->initialParam();
    }  // pId

    TIMER_MS_PRINT_CP("Load data");

    TIMER_MS_END;
}

MPM3D::~MPM3D() {}

bool MPM3D::isFinished() const {
    return (m_physParams.tMax > 0) && (m_t >= m_physParams.tMax);
}

Params::Physics& MPM3D::getPhysParameters() {
    return m_physParams;
}
const Params::Physics& MPM3D::getPhysParameters() const {
    return m_physParams;
}
const Params::Grid& MPM3D::getGridParameters() const {
    return m_gridParams;
}
const Params::DisplayValue& MPM3D::getDebugParameters() const {
    return m_debugParams;
}
Params::DisplayValue& MPM3D::getDebugParameters() {
    return m_debugParams;
}

const VectorVec3& MPM3D::getPartPosPtr() const {
    return m_pPos;
}

const VectorNumT& MPM3D::getPartPlasticVolumes() const {
    return m_pJp;
}

const ParticleDebugData& MPM3D::getPartDebugData() const {
    return m_partDebugData;
}

const MassGridType& MPM3D::getGridMass() const {
    return m_gMass;
}
MassGridType& MPM3D::getGridMassNC() {
    return m_gMass;
}

const VelGridType& MPM3D::getGridVel() const {
    return m_gVel;
}

ParticleData MPM3D::getParticleData(int _pId) const {
    int pId = m_pInvPartOrder[_pId];
    ParticleData ret;
    ret.pos = m_pPos[pId];
    ret.vel = m_pVel[pId];
    ret.C = m_pC[pId];
    ret.F = m_pF[pId];
    ret.Jp = m_pJp[pId];
    ret.stress = mp_elasticity->KirchhoffStress(ret.F, ret.Jp, *mp_hardening);
    ret.harden = m_pHard[pId];
    ret.pack = m_pG2PMass[pId] / (m_physParams.partPerCell * m_pMass);

    return ret;
}

void MPM3D::step() {
    if (isFinished()) {
        return;
    }

    m_dtRemain = m_physParams.dt;
    // Simulation
    m_t += m_physParams.dt;
    if (!(m_iter % 100)) {
        DEBUG_OUT << "It: " << m_iter << std::endl;
    }
    m_iter++;

    if (mp_rigidBodyDynamics) {
        mp_rigidBodyDynamics->fillForces(m_physParams.dt);
        for (int i = 0; i < mp_rigidBodyDynamics->nObjects(); ++i) {
            auto& obj = mp_rigidBodyDynamics->getObject(i);
            obj.velocity() += obj.acceleration() * m_physParams.dt;
            obj.angularVel() += obj.angularAcc() * m_physParams.dt;
            obj.acceleration().setZero();
            obj.angularAcc().setZero();
        }
    }
    while (m_dtRemain > 0) {
        TIMER_MS_START("[SimStep]", 1);
        preStep();
        TIMER_MS_PRINT_CP("Pre");
        coreStep();
        TIMER_MS_PRINT_CP("Core");
        postStep();
        TIMER_MS_PRINT_CP("Post");
        TIMER_MS_END;
        m_dtRemain -= m_dt;
    }
}

void MPM3D::preStep() {
    m_hardMax = 0;
    /// Clean grid
    m_gMass.setConst(0);
    m_gVel.setConst(Zero3);
    m_gVelOld.setConst(Zero3);

#ifdef USE_SPARSE_GRID
    std::vector<size_t> gridBlocks = m_gMass.positionsToGridBlock(m_pPos, 3);
    m_gMass.reserveGridBlocks(gridBlocks);
    m_gVel.reserveGridBlocks(gridBlocks);
    m_gVelOld.reserveGridBlocks(gridBlocks);
#endif

    m_maxWaveSpeed = 0;
    m_dtVLim = m_physParams.dt;
    m_dtCLim = m_physParams.dt;
    m_dtPart = m_physParams.dt;
}

template <typename T>
void sortArray(
    std::vector<T>& toSort, const std::vector<std::pair<size_t, size_t>>& order
) {
    std::vector<T> temp(toSort.size());
#pragma omp parallel for
    for (size_t i = 0; i < temp.size(); ++i) {
        if (i != order[i].second)
            temp[i] = toSort[order[i].second];
    }

#pragma omp parallel for
    for (size_t i = 0; i < temp.size(); ++i) {
        if (i != order[i].second)
            toSort[i] = temp[i];
    }
    return;
}

void MPM3D::sortParticles() {
    auto gridIJKBase = [this](const Vec3& pos) -> Vec3i {
        // const Vec3 mPos = m_grid.pos2fracijk(pos);
        // Vec3i      base = (mPos.array() - 0.5).cast<int>();
        Vec3i base = pointToKernelLowerBound(pos);
        base[0] >>= particleSortPow;
        base[1] >>= particleSortPow;
        base[2] >>= particleSortPow;
        return base;
    };
    auto cellId = [this](Vec3i cell) -> int {
        return ((cell[0] & 1) + ((cell[1] & 1) << 1) + ((cell[2] & 1) << 2));
    };

#pragma omp parallel for
    for (size_t i = 0; i < m_pOrder.size(); ++i) {
        const Vec3& pos = m_pPos[i];
        Vec3i base = gridIJKBase(pos);
        size_t id = cellId(base);
        size_t hash = (id << 60) + (size_t(base[2]) << 40) +
                      (size_t(base[1]) << 20) + size_t(base[0]);
        m_pOrder[i] = {hash, i};
    }

    std::sort(m_pOrder.begin(), m_pOrder.end());

    if (m_orderingIter == 0) {
        sortArray(m_pPos, m_pOrder);
        sortArray(m_pVel, m_pOrder);
        sortArray(m_pC, m_pOrder);
        sortArray(m_pF, m_pOrder);
        sortArray(m_pJp, m_pOrder);
        sortArray(m_pG2PMass, m_pOrder);
        sortArray(m_pHard, m_pOrder);
        sortArray(m_pNearRigid, m_pOrder);
        sortArray(m_pPartOrder, m_pOrder);
#pragma omp parallel for
        for (size_t i = 0; i < m_pOrder.size(); ++i) {
            m_pInvPartOrder[m_pPartOrder[i]] = i;
            m_pOrder[i] = {0, i};
        }
    }
    m_orderingIter = (m_orderingIter + 1) % 8;

    m_pBlockOffset.clear();
    m_pBlockGroupOffset.fill(0);
    m_pBlockOffset.push_back(0);
    m_pBlockGroupOffset[0] = 0;

    Vec3i prevCell = gridIJKBase(m_pPos[m_pOrder[0].second]);
    int prevCellId = cellId(prevCell);
    size_t blockGroupOffset = 1;
    for (size_t i = 1; i < m_pOrder.size(); ++i) {
        Vec3i currCell = gridIJKBase(m_pPos[m_pOrder[i].second]);
        int currCellId = cellId(currCell);
        if (currCellId != prevCellId) {
            m_pBlockGroupOffset[blockGroupOffset] = m_pBlockOffset.size();
            blockGroupOffset++;
        }
        if (currCell != prevCell) {
            m_pBlockOffset.push_back(i);
        }
        prevCell = currCell;
        prevCellId = currCellId;
    }
    for (size_t i = blockGroupOffset; i <= 8; ++i) {
        m_pBlockGroupOffset[i] = m_pBlockOffset.size();
    }
    m_pBlockOffset.push_back(m_pOrder.size());

    // For debugging only!!!
    // for (int blockGroup = 0; blockGroup < 8; ++blockGroup) {
    //     size_t blockGroupStart = m_pBlockGroupOffset[blockGroup];
    //     size_t blockGroupEnd   = m_pBlockGroupOffset[blockGroup + 1];
    //     Vec3i  cellGroup =
    //         gridIJKBase(m_pPos[m_pOrder[m_pBlockOffset[blockGroupStart]].second]
    //         );
    //     int prevCellId = cellId(cellGroup);
    //     for (size_t block = blockGroupStart; block < blockGroupEnd; ++block)
    //     {
    //         size_t partStart = m_pBlockOffset[block];
    //         size_t partEnd   = m_pBlockOffset[block + 1];
    //
    //         Vec3i prevCell = gridIJKBase(m_pPos[m_pOrder[partStart].second]);
    //         for (int j = partStart + 1; j < partEnd; ++j) {
    //             Vec3i currCell   = gridIJKBase(m_pPos[m_pOrder[j].second]);
    //             int   currCellId = cellId(currCell);
    //             if (currCell != prevCell) {
    //                 throw std::runtime_error("Cell index does not match!");
    //             }
    //             if (currCellId != prevCellId) {
    //                 throw std::runtime_error("Cell id does not match!");
    //             }
    //         }
    //     }
    // }
}

void MPM3D::coreStep() {
    coreStepP2G();
    // coreStepP2GWithAtomic();
    determineTimeStep();
    if (mp_rigidBodyDynamics) {
        mp_rigidBodyDynamics->updateAllObjects(m_dt);
    }
    coupleRigidBodies();
    coreStepGridStep();
    coreStepG2P();
}

void MPM3D::coreStepP2G() {
    const Params::Plasticity& plasticity = m_physParams.plasticity;
    const Params::Viscosity& viscosity = m_physParams.viscosity;
    const NumT pVol = m_physParams.particles.volume;

    const Elastic::IsotropicElasticity* isoElas =
        dynamic_cast<Elastic::IsotropicElasticity*>(mp_elasticity.get());

    const Elastic::ElasticityBase* elastic = mp_elasticity.get();

    // auto particleMidCell = [this](const Vec3& pos) {
    //     const Vec3  mPos = m_grid.pos2fracijk(pos);
    //     const Vec3i base = (mPos.array() - 0.5).cast<int>();
    //     return base;
    // };

    static constexpr int blockSize = (1 << particleSortPow) + 2;
    static constexpr int blockMask = (1 << particleSortPow) - 1;

    const Vec3 DMat =
        -pVol * 4 * m_grid.getInvDx().cwiseProduct(m_grid.getInvDx());

    sortParticles();

    for (int blockGroup = 0; blockGroup < 8; ++blockGroup) {
        size_t blockGroupStart = m_pBlockGroupOffset[blockGroup];
        size_t blockGroupEnd = m_pBlockGroupOffset[blockGroup + 1];
#pragma omp parallel
        {
            // initialize cfl stuff
            NumT waveSpeedLocal = 0, VminLocal = m_physParams.dt,
                 CminLocal = m_physParams.dt;
#pragma omp for schedule(dynamic)
            for (size_t block = blockGroupStart; block < blockGroupEnd;
                 ++block) {
                Grid::DenseGrid3D<NumT, blockSize> tempMassGrid(
                    Vec3(0, 0, 0), m_grid.getDx() * (blockSize - 1)
                );
                Grid::DenseGrid3D<Vec3, blockSize> tempVelGrid(
                    Vec3(0, 0, 0), m_grid.getDx() * (blockSize - 1)
                );
                Grid::DenseGrid3D<Vec3, blockSize> tempVelOldGrid(
                    Vec3(0, 0, 0), m_grid.getDx() * (blockSize - 1)
                );
                tempMassGrid.setConst(0);
                tempVelGrid.setConst(Zero3);
                tempVelOldGrid.setConst(Zero3);

                size_t partStart = m_pBlockOffset[block];
                size_t partEnd = m_pBlockOffset[block + 1];
                Vec3i blockOffset =
                    pointToKernelLowerBound(m_pPos[m_pOrder[partStart].second]);
                // particleMidCell(m_pPos[m_pOrder[partStart].second]);
                blockOffset[0] = blockOffset[0] & (~blockMask);
                blockOffset[1] = blockOffset[1] & (~blockMask);
                blockOffset[2] = blockOffset[2] & (~blockMask);

                for (size_t part = partStart; part < partEnd; ++part) {
                    size_t pId = m_pOrder[part].second;

                    // Grid cell
                    const Vec3& pos = m_pPos[pId];
                    const Vec3& vel = m_pVel[pId];

                    // Deformation gradient update
                    Mat3& Cp = m_pC[pId];
                    NumT& Jp = m_pJp[pId];
                    Mat3& Fp = m_pF[pId];
                    NumT& hard = m_pHard[pId];

                    Fp = (Id3x3 + m_dt * Cp) * Fp;
                    NumT J = Fp.determinant();

                    auto svd = Eigen::JacobiSVD<Mat3>(
                        Fp, Eigen::ComputeFullU | Eigen::ComputeFullV
                    );
                    Mat3 U = svd.matrixU();
                    Vec3 sig = svd.singularValues();
                    Mat3 V = svd.matrixV();

                    // Volume preservation
                    enforceVolumePreservation(
                        Fp, U, sig, V, Cp, J, m_pG2PMass[pId], m_pNearRigid[pId]
                    );

                    projectParticle(Fp, U, sig, V, Jp, hard);

                    // Viscous stress
                    Mat3 viscousStress = Zero3x3;
                    if (viscosity.isActive) {
                        viscousStress =
                            viscosity.eta / 2 * (Cp + Cp.transpose());
                    }

                    // "Stress"
                    const Mat3 affine = m_pMass * Cp;
                    const Mat3 kStress = (isoElas)
                                             ? isoElas->KirchhoffStress(
                                                   U, sig, hard, *mp_hardening
                                               )
                                             : mp_elasticity->KirchhoffStress(
                                                   Fp, hard, *mp_hardening
                                               );
                    const Mat3 stress =
                        DMat.asDiagonal() * (kStress + viscousStress);

                    // P2G Splatting
                    NumT VminP2G;
                    VminP2G = particleP2GNoAtomic(
                        blockOffset, pos, vel, affine, stress, tempMassGrid,
                        tempVelGrid, tempVelOldGrid
                    );
                    // Wave speed
                    NumT waveSpeed, Cmin, Vmin;
                    timestepLimits(
                        vel, U, sig, Cp, kStress, hard, waveSpeed, Vmin, Cmin
                    );
                    waveSpeedLocal = std::max(waveSpeedLocal, waveSpeed);
                    CminLocal = std::min(CminLocal, Cmin);
                    VminLocal = std::min(VminLocal, Vmin);
                    VminLocal = std::min(VminLocal, VminP2G);
                }
                // Add grid to main grid

                Grid::forEachSerial(
                    std::function([this, &blockOffset](
                                      const Vec3i& ijk, NumT& gMass, Vec3& gVel,
                                      Vec3& gVelOld
                                  ) {
                        if (!gMass) {
                            return;
                        }
#ifdef USE_SPARSE_GRID
                        Vec3i idx = blockOffset + ijk;
                        m_gMass.ref(idx) += gMass;
                        m_gVel.ref(idx) += gVel;
                        m_gVelOld.ref(idx) += gVelOld;
#else
                        size_t idx = m_grid.ijk2idx(blockOffset + ijk);
                        m_gMass(idx) += gMass;
                        m_gVel(idx) += gVel;
                        m_gVelOld(idx) += gVelOld;
#endif
                    }),
                    tempMassGrid, tempVelGrid, tempVelOldGrid
                );
                // Reduce CFL stuff
            }
            atomicMax(m_maxWaveSpeed, waveSpeedLocal);
            atomicMin(m_dtCLim, CminLocal);
            atomicMin(m_dtVLim, VminLocal);
        }
    }
}

void MPM3D::coreStepP2GWithAtomic() {
    // Shortcuts
    const Params::Plasticity& plasticity = m_physParams.plasticity;
    const Params::Viscosity& viscosity = m_physParams.viscosity;
    const NumT pVol = m_physParams.particles.volume;

    const Elastic::IsotropicElasticity* isoElas =
        dynamic_cast<Elastic::IsotropicElasticity*>(mp_elasticity.get());

    const Elastic::ElasticityBase* elastic = mp_elasticity.get();

    const Vec3 DMat =
        -pVol * 4 * m_grid.getInvDx().cwiseProduct(m_grid.getInvDx());

#pragma omp parallel
    {
        NumT waveSpeedLocal = 0, VminLocal = m_physParams.dt,
             CminLocal = m_physParams.dt;
#pragma omp for schedule(dynamic, 1)
        for (size_t pId = 0; pId < m_nPart; ++pId) {
            // Grid cell
            const Vec3& pos = m_pPos[pId];
            const Vec3& vel = m_pVel[pId];

            // Deformation gradient update
            Mat3& Cp = m_pC[pId];
            NumT& Jp = m_pJp[pId];

            Mat3& Fp = m_pF[pId];
            Fp = (Id3x3 + m_dt * Cp) * Fp;
            NumT J = Fp.determinant();

            auto svd = Eigen::JacobiSVD<Mat3>(
                Fp, Eigen::ComputeFullU | Eigen::ComputeFullV
            );
            Mat3 U = svd.matrixU();
            Vec3 sig = svd.singularValues();
            Mat3 V = svd.matrixV();

            // Volume preservation
            enforceVolumePreservation(
                Fp, U, sig, V, Cp, J, m_pG2PMass[pId], m_pNearRigid[pId]
            );

            projectParticle(Fp, U, sig, V, Jp, m_pHard[pId]);

            // Viscous stress
            Mat3 viscousStress = Zero3x3;
            if (viscosity.isActive) {
                viscousStress = viscosity.eta / 2 * (Cp + Cp.transpose());
            }

            // "Stress"
            const Mat3 affine = m_pMass * Cp;
            const Mat3 kStress = (isoElas)
                                     ? isoElas->KirchhoffStress(
                                           U, sig, m_pHard[pId], *mp_hardening
                                       )
                                     : mp_elasticity->KirchhoffStress(
                                           Fp, m_pHard[pId], *mp_hardening
                                       );
            const Mat3 stress = DMat.asDiagonal() * (kStress + viscousStress);

            NumT VminP2G;
            VminP2G = particleP2G(pos, vel, Cp, affine, stress);

            NumT waveSpeed, Cmin, Vmin;
            timestepLimits(
                vel, U, sig, Cp, kStress, m_pHard[pId], waveSpeed, Vmin, Cmin
            );

            waveSpeedLocal = std::max(waveSpeedLocal, waveSpeed);
            CminLocal = std::min(CminLocal, Cmin);
            VminLocal = std::min(VminLocal, Vmin);
            VminLocal = std::min(VminLocal, VminP2G);
        }  // pId
        atomicMax(m_maxWaveSpeed, waveSpeedLocal);
        atomicMin(m_dtCLim, CminLocal);
        atomicMin(m_dtVLim, VminLocal);
    }
}

inline void MPM3D::projectParticle(
    Mat3& Fp, Mat3& U, Vec3& sig, Mat3& V, NumT& Jp, NumT& hard
) {
    const Params::Plasticity& plasticity = m_physParams.plasticity;
    const Params::Viscosity& viscosity = m_physParams.viscosity;
    const NumT pVol = m_physParams.particles.volume;

    const Elastic::IsotropicElasticity* isoElas =
        dynamic_cast<Elastic::IsotropicElasticity*>(mp_elasticity.get());

    const Elastic::ElasticityBase* elastic = mp_elasticity.get();

    Mat3 FpTest = Fp;
    Vec3 sigTest = sig;
    if (m_physParams.volCorrection == Params::VolumeCorrection::Tampubolon &&
        bool(
            mp_yield->returnMapType() | Plastic::ReturnMapType::PreserveVolume
        )) {
        NumT vCorr = cbrt(Jp);
        FpTest *= vCorr;
        sigTest *= vCorr;
    }
    Vec3 sigNew = sig;
    if (isoElas) {
        sigNew =
            isoElas->returnMappingSig(sigTest, *mp_yield, hard, *mp_hardening);
        Fp = U * sigNew.asDiagonal() * V.transpose();
    } else {
        Fp = mp_elasticity->returnMapping(
            FpTest, *mp_yield, hard, *mp_hardening
        );
        Eigen::JacobiSVD<Mat3, Eigen::ComputeFullU | Eigen::ComputeFullV> svd;
        svd.compute(Fp);
        sigNew = svd.singularValues();
    }
    Jp *= sig.prod() / sigNew.prod();
    if (bool(mp_yield->returnMapType() | Plastic::ReturnMapType::SandLike)) {
        if ((sigNew - sigTest).squaredNorm() < 1e-8) {
            Jp = 1;
        }
    }
    hard = mp_hardening->hardeningParam(sig, sigNew, hard);

    sig = sigNew;
}

inline void MPM3D::enforceVolumePreservation(
    Mat3& Fp, Mat3& U, Vec3& sig, Mat3& V, Mat3& Cp, NumT& J, NumT mass,
    bool nearRigid
) {
    if (!bool(
            mp_yield->returnMapType() | Plastic::ReturnMapType::PreserveVolume
        )) {
        return;
    }
    if (m_physParams.volCorrection == Params::VolumeCorrection::Gao) {
        NumT maxMass = m_physParams.partPerCell * m_pMass;
        if (mass < maxMass && !nearRigid) {
            sig = Vec3::Ones();
            Fp = U * sig.asDiagonal() * V.transpose();
            J = sig.prod();
        }
    }
}

NumT MPM3D::particleP2G(
    const Vec3& pos, const Vec3& vel, const Mat3& Cp, const Mat3& affine,
    const Mat3& stress
) {
    // Quadratic kernel
    Vec3i base;
    Vec3 fx;
    Vec3 w0, w1, w2;
    std::tie(base, fx, w0, w1, w2) = getP2GCoordinates(pos);
    // Transfer
    const Vec3 extForce = m_pMass * m_g + externalForces(pos, m_pMass, m_t);
    NumT speedLimMin = m_physParams.dt;

    Grid::rangeIter(
        std::function([this, &fx, &w0, &w1, &w2, &vel, &Cp, &extForce, &affine,
                       &stress, &speedLimMin](
                          const Vec3i& ijk, const Vec3i& offset, NumT& gMass,
                          Vec3& gVel, Vec3& gVelOld
                      ) {
            const Vec3 offsetF = offset.cast<NumT>();
            const Vec3 dPos = (offsetF - fx).cwiseProduct(m_grid.getDx());
            const NumT weight = w0[offset[0]] * w1[offset[1]] * w2[offset[2]];
#pragma omp atomic update
            gMass += weight * m_pMass;
            const Vec3 dvIner = weight * m_pMass * (vel + Cp * dPos);
            const Vec3 dv = weight * (extForce + (affine + stress) * dPos);
            for (size_t l = 0; l < 3; ++l) {
#pragma omp atomic update
                gVel[l] += dv[l];
#pragma omp atomic update
                gVelOld[l] += dvIner[l];
            }  // l
            NumT speedLim = weight * 0.95 * m_grid.getDx().minCoeff() /
                            dvIner.cwiseAbs().maxCoeff();
            speedLimMin = std::min(speedLim, speedLimMin);
        }),
        base, base + Vec3i(3, 3, 3), m_gMass, m_gVel, m_gVelOld
    );
    return speedLimMin;
}
template <int N>
inline NumT MPM3D::particleP2GNoAtomic(
    const Vec3i& blockOffset, const Vec3& pos, const Vec3& vel,
    const Mat3& affine, const Mat3& stress,
    Grid::DenseGrid3D<NumT, N>& massGrid, Grid::DenseGrid3D<Vec3, N>& velGrid,
    Grid::DenseGrid3D<Vec3, N>& velOldGrid
) {
    // Quadratic kernel
    Vec3i base;
    Vec3 fx;
    Vec3 w0, w1, w2;
    std::tie(base, fx, w0, w1, w2) = getP2GCoordinates(pos);

    base -= blockOffset;

    // Transfer
    const Vec3 extForce = m_pMass * m_g + externalForces(pos, m_pMass, m_t);
    NumT speedLimMin = m_physParams.dt;

    Grid::rangeIter(
        std::function([this, &fx, &w0, &w1, &w2, &vel, &extForce, &affine,
                       &stress, &speedLimMin](
                          const Vec3i& ijk, const Vec3i& offset, NumT& gMass,
                          Vec3& gVel, Vec3& gVelOld
                      ) {
            if ((ijk.array() < 0).any()) {
                throw std::runtime_error("AAAAAA");
            }
            if ((ijk.array() > 6).any()) {
                throw std::runtime_error("BBBBBB");
            }

            const Vec3 offsetF = offset.cast<NumT>();
            const Vec3 dPos = (offsetF - fx).cwiseProduct(m_grid.getDx());
            const NumT weight = w0[offset[0]] * w1[offset[1]] * w2[offset[2]];

            gMass += weight * m_pMass;
            const Vec3 dvIner = weight * (m_pMass * vel + affine * dPos);
            const Vec3 dv = weight * (extForce + (affine + stress) * dPos);
            gVel += dv;
            gVelOld += dvIner;
            NumT speedLim = weight * 0.95 * m_grid.getDx().minCoeff() /
                            dvIner.cwiseAbs().maxCoeff();
            speedLimMin = std::min(speedLim, speedLimMin);
        }),
        base, base + Vec3i(3, 3, 3), massGrid, velGrid, velOldGrid
    );
    return speedLimMin;
}
inline void MPM3D::timestepLimits(
    const Vec3& vel, const Mat3& U, const Vec3& sig, const Mat3& Cp,
    const Mat3& kStress, const NumT hard, NumT& waveSpeed, NumT& Vmin,
    NumT& Cmin
) {
    const Elastic::IsotropicElasticity* isoElas =
        dynamic_cast<Elastic::IsotropicElasticity*>(mp_elasticity.get());

    Vec3 hessDiag =
        isoElas->KirchhoffJacobian(sig, hard, *mp_hardening).diagonal();
    Vec3 stressSig = (U.transpose() * kStress * U).diagonal();
    hessDiag = hessDiag - stressSig.cwiseQuotient(sig);
    hessDiag = hessDiag.cwiseQuotient(sig);
    waveSpeed = 0;

#pragma unroll
    for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
            if (i == j) {
                waveSpeed = std::max(waveSpeed, sig[i] * sig[i] * hessDiag[i]);
            } else {
                if (sig[i] != sig[j]) {
                    waveSpeed = std::max(
                        waveSpeed, sig[j] * sig[j] *
                                       (stressSig[i] - stressSig[j]) /
                                       (sig[i] * sig[i] - sig[j] * sig[j])
                    );
                }
            }
        }
    }
    waveSpeed = std::sqrt(waveSpeed / m_physParams.rho / sig.prod());
    Cmin = 0.2 / Cp.cwiseAbs().maxCoeff();
    // Eigen::JacobiSVD<Mat3> svd(Cp);
    //    Cmin      = 0.2 / svd.singularValues().maxCoeff();
    Vmin = 0.95 * m_grid.getDx().minCoeff() / vel.norm();
}

void MPM3D::determineTimeStep() {
    m_dtOld = m_dt;
    m_dt = m_physParams.dt;
    if (m_t - m_dtRemain <= m_physParams.dt * 0.1) {
        m_dt /= 100;
    }
    std::cout << "t: " << m_t << std::endl;
    m_dt = std::min(
        m_dt, m_physParams.cfl * m_grid.getDx().minCoeff() / m_maxWaveSpeed
    );
    m_dt = std::min(m_dt, m_dtCLim);
    m_dt = std::min(m_dt, m_dtVLim);

    if (m_dtOld + 2 * (m_dt - m_dtOld) > 0) {
        m_dt = std::min(m_dt, m_dtOld + 2 * (m_dt - m_dtOld));
    }
    m_dt = std::min(m_dt, m_dtRemain);
    std::cout << "dt: " << m_dt << " max wave: " << m_maxWaveSpeed
              << " C lim: " << m_dtCLim << " V lim: " << m_dtVLim << " "
              << m_dtRemain << std::endl;
}

void MPM3D::coupleRigidBodies() {
    if (!mp_rigidBodyDynamics) {
        return;
    }

    static auto applyMomentChangeToObject =
        [](FrictionFrenzy::CollisionObject::Mesh& obj, const Vec3& momentChange,
           const Vec3& pos) -> void {
        const Vec3 relPos = pos - obj.getTranslation();
        Vec3 velChange = momentChange / obj.mass();
        Vec3 angChange = obj.invInertiaTensor() * relPos.cross(momentChange);
        for (int d = 0; d < 3; ++d) {
#pragma omp atomic update
            obj.velocity()[d] += velChange[d];
#pragma omp atomic update
            obj.angularVel()[d] += angChange[d];
        }
    };

    for (int objIt = 0; objIt < mp_rigidBodyDynamics->nObjects(); ++objIt) {
        auto* obj = dynamic_cast<FrictionFrenzy::CollisionObject::Mesh*>(
            &mp_rigidBodyDynamics->getObject(objIt)
        );

        auto& aabb = obj->getFCLObject()->getAABB();
        Vec3 center = aabb.center();
        Vec3 aabbSize(aabb.width(), aabb.height(), aabb.depth());
        Vec3i lowerRange = m_grid.pos2ijk(center - 0.5 * aabbSize);
        Vec3i upperRange = m_grid.pos2ijk(center + 0.5 * aabbSize);
        lowerRange = lowerRange.cwiseMax(0).cwiseMin(m_grid.getNodeRes());
        upperRange = upperRange.cwiseMax(0).cwiseMin(
            m_grid.getNodeRes() + Vec3i(1, 1, 1)
        );

        auto func = std::function(
            [&obj, this](
                const Vec3i& ijk, const Vec3i& offset, NumT& mass, Vec3& vel,
                Vec3& velOld
            ) -> void {
                if (mass <= 0) {
                    return;
                }
                const Vec3 nodePos = m_grid.getIJKPos(ijk);
                Vec3 sdfGrad;
                NumT sdf;
                std::tie(sdf, sdfGrad) = obj->signedDistance(nodePos);
                if (sdf > 0) {
                    return;
                }
                if (obj->isActive()) {
                    Vec3 momentChange = (vel - m_g * mass) * m_dt;
                    applyMomentChangeToObject(*obj, momentChange, nodePos);
                }

                Vec3 tempVel = velOld + vel * m_dt;
                const Vec3 velOrig = tempVel;
                const Vec3 relPos = nodePos - obj->getTranslation();
                const Vec3 objVel =
                    obj->velocity() + obj->angularVel().cross(relPos);
                sdfGrad.normalize();

                if (resolveCollision(
                        sdfGrad, m_physParams.boundaries.muWall, tempVel,
                        objVel * mass
                    )) {
                    vel = (tempVel - velOld) / m_dt;
                    if (obj->isActive()) {
                        applyMomentChangeToObject(
                            *obj, velOrig - tempVel, nodePos
                        );
                    }
                }
            }
        );
        Grid::rangeWriteParallel(
            func, lowerRange, upperRange, m_gMass, m_gVel, m_gVelOld
        );
    }
}

void MPM3D::coreStepGridStep() {
    coreStepGridMirror();
    // coreStepGridEnforce();
}

void MPM3D::coreStepGridMirror() {
    // Shortcuts

    /// Grid Physics
    Grid::forEach(
        std::function(
            [this](
                const Vec3i& ijk, NumT& mass, Vec3& vel, Vec3& velOld
            ) -> void {
                if (mass <= 0) {
                    velOld.setZero();
                    vel.setZero();
                    return;
                }
                // Explicit time stepping
                vel *= m_dt;
                vel += velOld;

                velOld /= mass;
            }
        ),
        m_gMass, m_gVel, m_gVelOld
    );

    for (int dim = 0; dim < 3; ++dim) {
        Vec3i bound = m_grid.getNodeRes();
        Vec3i start = Vec3i::Zero();
        bound[dim] = m_border + 1;
        start[dim] = m_border;

        auto solveBoundary = [this](
                                 const Vec3i& idxMirr, Vec3& gVel, NumT& gMass,
                                 int dim, int dir
                             ) {
            const Vec3 velMirrOrig = gVel;
            const NumT massMirrOrig = gMass;
            Vec3 velReflect = m_gVel(idxMirr);
            velReflect[dim] = -velReflect[dim];
            gVel += velReflect;
            gMass += m_gMass(idxMirr);
            const NumT normVelDiff =
                gVel[dim] - velMirrOrig[dim] / massMirrOrig * gMass;
            if (normVelDiff * dir > 0) {
                NumT normMirr = gVel[dim];
                Vec3 tanMirr = gVel;
                tanMirr[dim] = 0;
                const double friction = std::min(
                    m_physParams.boundaries.muWall * normVelDiff * dir /
                        (tanMirr.norm() + 1e-8),
                    1.
                );
                tanMirr *= (1. - friction);
                tanMirr[dim] = normMirr;
                gVel = tanMirr;
                m_gVel.ref(idxMirr) = gVel;
                m_gVel.ref(idxMirr)[dim] *= -1;
                m_gMass.ref(idxMirr) = gMass;
            } else {
                gVel = velMirrOrig * gMass / massMirrOrig;
                m_gVel.ref(idxMirr) *= gMass / m_gMass.ref(idxMirr);
                m_gMass.ref(idxMirr) = gMass;
                // gMass = massMirrOrig;
            }
        };
        auto reflectLower =
            std::function([this, dim, &solveBoundary](
                              const Vec3i& idx, const Vec3i& offset,
                              NumT& gMass, Vec3& gVel
                          ) {
                if (!gMass) {
                    return;
                }
                Vec3i idxMirr = idx;
                idxMirr[dim] = 2 * m_border - idx[dim];

                solveBoundary(idxMirr, gVel, gMass, dim, 1);
            });
        auto reflectUpper =
            std::function([this, dim, &solveBoundary](
                              const Vec3i& idx, const Vec3i& offset,
                              NumT& gMass, Vec3& gVel
                          ) {
                if (!gMass) {
                    return;
                }
                int reflectIdx = m_grid.getCellRes()[dim] - m_border;
                Vec3i idxMirr = idx;
                idxMirr[dim] = 2 * reflectIdx - idx[dim];

                solveBoundary(idxMirr, gVel, gMass, dim, -1);
            });
        Grid::rangeWriteParallel(
            reflectLower, start, start + bound, m_gMass, m_gVel
        );

        start[dim] = m_grid.getCellRes()[dim] - 2 * m_border;
        Grid::rangeWriteParallel(
            reflectUpper, start, start + bound, m_gMass, m_gVel
        );
    }
    Grid::forEach(
        std::function([this](const Vec3i& ijk, NumT& mass, Vec3& vel) -> void {
            if (mass <= 0) {
                return;
            }
            vel /= mass;
        }),
        m_gMass, m_gVel
    );
}
void MPM3D::coreStepGridEnforce() {
    static auto func = std::function(
        [this](const Vec3i& ijk, NumT& mass, Vec3& vel, Vec3& velOld) -> void {
            if (mass <= 0) {
                vel = Zero3;
                velOld = Zero3;
                return;
            }

            // Explicit time stepping
            vel *= m_dt;
            vel += velOld;
            vel /= mass;
            velOld /= mass;

            const Vec3 velOrig = vel;
            const Vec3i boundType = m_grid.boundFlagsLayer(ijk, m_border + 1);
            vel[0] *= (boundType[0] * vel[0] <= 0);
            vel[1] *= (boundType[1] * vel[1] <= 0);
            vel[2] *= (boundType[2] * vel[2] <= 0);
            const NumT friction = std::min(
                m_physParams.boundaries.muWall * (vel - velOrig).norm() /
                    (vel.norm() + 1e-8),
                1.
            );
            vel *= (1. - friction);
        }
    );
    Grid::forEach(func, m_gMass, m_gVel, m_gVelOld);
}

std::vector<std::pair<size_t, Vec3>> MPM3D::getRigidBodiesToucingPoint(
    Vec3 point
) {
    std::vector<std::pair<size_t, Vec3>> rigidIds;
    if (mp_rigidBodyDynamics) {
        for (int objIt = 0; objIt < mp_rigidBodyDynamics->nObjects(); ++objIt) {
            auto* obj = dynamic_cast<FrictionFrenzy::CollisionObject::Mesh*>(
                &mp_rigidBodyDynamics->getObject(objIt)
            );
            if (obj->getFCLObject()->getAABB().contain(point)) {
                Vec3 sdfGrad;
                NumT sdf;
                std::tie(sdf, sdfGrad) = obj->signedDistance(point);
                if (sdf <= 0) {
                    rigidIds.emplace_back(objIt, sdfGrad);
                }
            }
        }
    }
    return rigidIds;
}
bool MPM3D::resolveCollision(
    const Vec3& normal, const NumT mu, Vec3& velocity, const Vec3& refVel
) {
    assert(std::abs(normal.squaredNorm() - 1) < 1e-4);

    const NumT normSpeed = velocity.dot(normal);
    const NumT refNormSpeed = refVel.dot(normal);
    const NumT vN = normSpeed - refNormSpeed;
    if (vN < 0) {
        const Vec3 vT = velocity - normal * normSpeed;
        const NumT friction = std::max(mu * vN / (vT.norm() + 1e-8), NumT(-1));
        velocity = (1. + friction) * vT + normal * refNormSpeed;
        return true;
    }
    return false;
}

void MPM3D::coreStepG2P() {
#pragma omp parallel for schedule(dynamic, 1)
    for (size_t pId = 0; pId < m_nPart; ++pId) {
        // Grid cell
        Vec3& pos = m_pPos[pId];
        Vec3& vel = m_pVel[pId];
        Mat3& Cp = m_pC[pId];
        Vec3 velOld = Vec3::Zero();
        Vec3 velNew = Vec3::Zero();

        Vec3i base;
        Vec3 fx;
        Vec3 w0, w1, w2;
        std::tie(base, fx, w0, w1, w2) = getP2GCoordinates(pos);

        // Transfer
        Cp = Zero3x3;
        NumT p2gMass = 0;

        Grid::rangeIter(
            std::function([this, &fx, &w0, &w1, &w2, &vel, &velNew, &velOld,
                           &p2gMass, &Cp](
                              const Vec3i& idx, const Vec3i& offset,
                              const NumT& gMass, const Vec3& gVel,
                              const Vec3& gVelOld
                          ) {
                if (gMass == 0) {
                    return;
                }
                const Vec3 dPos = offset.cast<NumT>() - fx;
                const NumT weight =
                    w0[offset[0]] * w1[offset[1]] * w2[offset[2]];
                velNew += weight * gVel;
                velOld += weight * gVelOld;
                p2gMass += weight * gMass;
                Vec3i idxReflect = idx;
                bool boundReflect = false;
                Vec3i boundFlags = m_grid.boundFlagsLayer(idx, m_border);
#pragma unroll
                for (int dim = 0; dim < 3; ++dim) {
                    if (boundFlags[dim] < 0) {
                        idxReflect[dim] = 4 - idx[dim];
                        boundReflect = true;
                    } else if (boundFlags[dim] > 0) {
                        idxReflect[dim] =
                            2 * (m_grid.getCellRes()[dim] - m_border) -
                            idx[dim];
                        boundReflect = true;
                    }
                }
                Vec3 invDx = m_grid.getInvDx();
                Cp +=
                    4. * weight * invDx.asDiagonal() * gVel * dPos.transpose();
            }),
            base, base + Vec3i(3, 3, 3), m_gMass, m_gVel, m_gVelOld
        );

        bool boundary = false;
        if (m_physParams.boundaries.collisionParticles &&
            mp_rigidBodyDynamics) {
            for (int objIt = 0; objIt < mp_rigidBodyDynamics->nObjects();
                 ++objIt) {
                auto* obj =
                    dynamic_cast<FrictionFrenzy::CollisionObject::Mesh*>(
                        &mp_rigidBodyDynamics->getObject(objIt)
                    );
                if (obj->getFCLObject()->getAABB().contain(pos + vel * m_dt)) {
                    Vec3 sdfGrad;
                    NumT sdf;
                    std::tie(sdf, sdfGrad) =
                        obj->signedDistance(pos + vel * m_dt);
                    if (sdf < 0) {
                        boundary = true;
                    }  // outside
                }
            }
        }  // m_obstaclePtr
        m_pG2PMass[pId] = p2gMass;
        Vec3 posNew = pos + velNew * m_dt;
        boundary =
            boundary |
            ((m_grid.boundFlagsLayer(m_grid.pos2ijk(posNew), m_border + 1)
                  .array() != 0)
                 .any());

        Vec3 velDiff = (!boundary) * m_asflipCoeff * (vel - velOld);

        vel = velNew + velDiff;
        NumT xadj = 1;
        if (((Mat3::Identity() + m_dt * Cp) * m_pF[pId]).determinant() < 1) {
            xadj = 0;
        }

        // Advection
        Vec3 velPos = (velNew + xadj * velDiff);
        pos += m_dt * velPos;

        // #ifndef DEBUG_OBS_NO_COL
        // Boundary condition - obstacle
        if (m_physParams.boundaries.collisionParticles &&
            mp_rigidBodyDynamics) {
            for (int objIt = 0; objIt < mp_rigidBodyDynamics->nObjects();
                 ++objIt) {
                auto* obj =
                    dynamic_cast<FrictionFrenzy::CollisionObject::Mesh*>(
                        &mp_rigidBodyDynamics->getObject(objIt)
                    );
                if (obj->getFCLObject()->getAABB().contain(pos)) {
                    Vec3 sdfGrad;
                    NumT sdf;
                    std::tie(sdf, sdfGrad) = obj->signedDistance(pos);
                    if (sdf < m_grid.getDx().maxCoeff() * 1.5) {
                        m_pNearRigid[pId] = 1;
                    } else {
                        m_pNearRigid[pId] = 0;
                    }
                    if (sdf > 0) {
                        continue;
                    }  // outside
                    sdfGrad = sdfGrad.normalized();
                    pos -= sdf * sdfGrad;
                    const Vec3 vN = vel.dot(sdfGrad) * sdfGrad;
                    const Vec3 objVel =
                        obj->velocity() +
                        obj->angularVel().cross(pos - obj->getTranslation());
                    const Vec3 vT = vel - vN;
                    vel = vT + objVel.dot(sdfGrad) * sdfGrad;
                }
            }
        }  // m_obstaclePtr
           // #endif     // DEBUG_OBS_NO_COL

        // Clamp
        clampPos(pos, vel);

    }  // pId
}

void MPM3D::postStep() {
    //
}

void MPM3D::updateDebugData() {
    if (m_debugParams == Params::DisplayValue::PlasticVolume) {
        m_partDebugData.data = m_pJp;
    } else {
        std::fill(m_partDebugData.data.begin(), m_partDebugData.data.end(), 1);
    }

    /// Particles colours
    if (m_debugParams == Params::DisplayValue::Volume) {
        // PARTICLE_LOOP(pId) {
        for (size_t pId = 0; pId < m_nPart; ++pId) {
            // Compute 1D parameter indicating the compression/extension
            const Mat3& Fp = m_pF[pId];
            const NumT J = Fp.determinant();
            const NumT center = static_cast<NumT>(0.75);
            const NumT scale = static_cast<NumT>(3);
            if (J <= 1.) {
                m_partDebugData.data[pId] =
                    center +
                    center * tanh(scale * (J - static_cast<NumT>(1.0)));
            } else {
                m_partDebugData.data[pId] =
                    center +
                    (1 - center) * tanh(scale * (J - static_cast<NumT>(1.0)));
            }

        }  // pId
        m_partDebugData.min = 0;
        m_partDebugData.max = 1;
    }  // Volume
    else if (m_debugParams == Params::DisplayValue::ParticleAltitude) {
        double zMin = 42.;
        double zMax = -42.;

#pragma omp parallel
        {
            double zMinLoc = zMin;
            double zMaxLoc = zMax;
#pragma omp for nowait
            for (size_t pId = 0; pId < m_nPart; ++pId) {
                const double z = m_pPos[pId][2];
                zMinLoc = std::min(zMinLoc, z);
                zMaxLoc = std::max(zMaxLoc, z);
            }

#pragma omp critical
            {
                zMin = std::min(zMin, zMinLoc);
                zMax = std::max(zMax, zMaxLoc);
            }
#pragma omp barrier

#pragma omp for
            for (size_t pId = 0; pId < m_nPart; ++pId) {
                m_partDebugData.data[pId] = m_pPos[pId][2];
            }
        }  // omp parallel
        m_partDebugData.min = zMin;
        m_partDebugData.max = zMax;

    }  // Altitude
    else if (m_debugParams == Params::DisplayValue::PackingFraction) {
        const NumT pVol = m_physParams.particles.volume;
        // Volume of the 3d quadratic spline
        const NumT nodeVolume = m_grid.getDx().prod();
        constexpr NumT limitPackingFraction = 0.74;

        NumT maxPF = 0.;

#pragma omp parallel
        {
            NumT localMaxPF = 0.;
#pragma omp for
            for (size_t pId = 0; pId < m_nPart; ++pId) {
                m_partDebugData.data[pId] =
                    m_pG2PMass[pId] / nodeVolume / limitPackingFraction;
                localMaxPF = std::max(localMaxPF, m_partDebugData.data[pId]);
            }
#pragma omp critical
            { maxPF = std::max(localMaxPF, maxPF); }
        }
        m_partDebugData.min = 0;
        m_partDebugData.max = maxPF;
    }  // Packing fraction
    else if (m_debugParams == Params::DisplayValue::ParticleSpeed) {
        NumT maxSpeed = 0;
#pragma omp parallel
        {
            NumT localMaxSpeed = 0.;
#pragma omp for
            for (size_t pId = 0; pId < m_nPart; ++pId) {
                const Vec3& vel = m_pVel[pId];
                const NumT speed = vel.norm();
                m_partDebugData.data[pId] = speed;
                localMaxSpeed = std::max(localMaxSpeed, speed);
            }  // pId
#pragma omp barrier
#pragma omp critical
            { maxSpeed = std::max(localMaxSpeed, maxSpeed); }  // omp critical
        }                                                      // omp parallel
        m_partDebugData.min = 0;
        m_partDebugData.max = maxSpeed;
    }  // Particle speed
    else if (m_debugParams == Params::DisplayValue::ParticlePressure) {
        NumT maxPressure = 0;
        NumT minPressure = 0;
#pragma omp parallel
        {
            NumT localMaxPressure = 0.;
            NumT localMinPressure = 0.;
#pragma omp for
            for (size_t pId = 0; pId < m_nPart; ++pId) {
                Mat3 cauchyStress = mp_elasticity->KirchhoffStress(
                                        m_pF[pId], m_pHard[pId], *mp_hardening
                                    ) /
                                    m_pF[pId].determinant();
                m_partDebugData.data[pId] = -cauchyStress.trace() / 3;
                localMaxPressure =
                    std::max(localMaxPressure, m_partDebugData.data[pId]);
                localMinPressure =
                    std::min(localMinPressure, m_partDebugData.data[pId]);
            }  // pId
#pragma omp barrier
#pragma omp critical
            {
                maxPressure = std::max(localMaxPressure, maxPressure);
                minPressure = std::min(localMinPressure, minPressure);
            }  // omp critical
        }      // omp parallel
        m_partDebugData.min = minPressure;
        m_partDebugData.max = maxPressure;
    }  // Particle speed
}

void MPM3D::incGravity(int gx, int gy, int gz) {
    m_gX += gx;
    m_gY += gy;
    m_gZ += gz;
    m_g = {m_gX * 9.81, m_gY * 9.81, m_gZ * 9.81};
    mp_rigidBodyDynamics->gravity() = m_g;
    std::cout << "Gravity: (" << m_g[0] << ", " << m_g[1] << ", " << m_g[2]
              << ")" << std::endl;
}

void MPM3D::clampPos(Vec3& pos, Vec3& vel) {
    NumT padding = m_border + 1e-2;
    Vec3i borderFlag = m_grid.boundFlagsLayer(m_grid.pos2ijk(pos), m_border);
    Vec3 borderMin = padding * m_grid.getDx() + m_grid.getStartPos();
    Vec3 borderMax = m_grid.getEndPos() - padding * m_grid.getDx();
    pos = pos.cwiseMin(borderMax).cwiseMax(borderMin);
}
std::tuple<Vec3i, Vec3, Vec3, Vec3, Vec3> MPM3D::getP2GCoordinates(
    const Vec3& pos
) {
    // Vec3  mPos = m_grid.pos2fracijk(pos);
    // Vec3i base = (mPos.array() - 0.5).cast<int>();
    Vec3 mPos;
    Vec3i base;
    std::tie(mPos, base) = pointToGridPos(pos);
    const Vec3 fx = mPos - base.cast<NumT>();

    const Vec3 w0 = {
        0.5 * (1.5 - fx[0]) * (1.5 - fx[0]), 0.75 - (fx[0] - 1) * (fx[0] - 1),
        0.5 * (fx[0] - 0.5) * (fx[0] - 0.5)};
    const Vec3 w1 = {
        0.5 * (1.5 - fx[1]) * (1.5 - fx[1]), 0.75 - (fx[1] - 1) * (fx[1] - 1),
        0.5 * (fx[1] - 0.5) * (fx[1] - 0.5)};
    const Vec3 w2 = {
        0.5 * (1.5 - fx[2]) * (1.5 - fx[2]), 0.75 - (fx[2] - 1) * (fx[2] - 1),
        0.5 * (fx[2] - 0.5) * (fx[2] - 0.5)};
    return {base, fx, w0, w1, w2};
}

void MPM3D::dumpParticleData(
    std::vector<NumT>& data, NumT& currTime, bool rotationOnly
) {
    currTime = m_t;
    const VectorVec3& pos = m_pPos;
    const VectorMat3& F = m_pF;
    const int dof = (rotationOnly ? 7 : 12);
    data.clear();
    data.resize(pos.size() * dof);
#pragma omp parallel for
    for (int outID = 0; outID < pos.size(); ++outID) {
        int i = m_pInvPartOrder[outID];
        data[outID * dof + 0] = pos[i].x();
        data[outID * dof + 1] = pos[i].y();
        data[outID * dof + 2] = pos[i].z();
        if (rotationOnly) {
            Eigen::JacobiSVD<Mat3> svd;
            svd.compute(F[i], Eigen::ComputeFullU | Eigen::ComputeFullV);
            Mat3 rotation = svd.matrixU() * svd.matrixV().transpose();
            Eigen::Quaternion<NumT> quat(rotation);
            data[outID * dof + 3] = quat.w();
            data[outID * dof + 4] = quat.x();
            data[outID * dof + 5] = quat.y();
            data[outID * dof + 6] = quat.z();
        } else {
            int offset = 3;
            for (int j = 0; j < 3; ++j) {
                for (int k = 0; k < 3; ++k) {
                    data[outID * dof + offset] = F[i](j, k);
                    ++offset;
                }
            }
        }
    }
    return;
}

void MPM3D::dumpRigidData(std::vector<NumT>& data, NumT& currTime) {
    currTime = m_t;
    data.resize(mp_rigidBodyDynamics->nObjects() * 7);
    for (int i = 0; i < mp_rigidBodyDynamics->nObjects(); ++i) {
        const auto& obj = mp_rigidBodyDynamics->getObject(i);
        const Vec3& pos = obj.getTranslation();
        const auto& quat = obj.getRotation();
        data[i * 7 + 0] = pos[0];
        data[i * 7 + 1] = pos[1];
        data[i * 7 + 2] = pos[2];
        data[i * 7 + 3] = quat.w();
        data[i * 7 + 4] = quat.x();
        data[i * 7 + 5] = quat.y();
        data[i * 7 + 6] = quat.z();
    }
}
Vec3 MPM3D::externalForces(const Vec3& pos, NumT mass, NumT time) {
    return Vec3(0., 0., 0.);
}
}  // namespace MPM
