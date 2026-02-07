#pragma once

#include "Common/CustomTypes.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/YieldSurfaceBase.hpp"
namespace MPM {
namespace Elastic {
using Hardening::HardeningBase;
using Type::Mat3, Type::Vec3, Type::NumT;
class ElasticityBase {
public:
    ElasticityBase() {}
    virtual ~ElasticityBase() {}
    virtual Params::ElasticityType type() const {
        return Params::ElasticityType::None;
    }
    virtual NumT energy(
        const Mat3& F, const NumT Jp, const HardeningBase& hardening
    ) const = 0;
    virtual Mat3 KirchhoffStress(
        const Mat3& F, const NumT Jp, const HardeningBase& hardening
    ) const = 0;
    virtual Mat3 returnMapping(
        const Mat3& FTrial, const Plastic::YieldSurfaceBase& yield,
        const NumT Jp, const HardeningBase& hardening
    ) const = 0;
};
class IsotropicElasticity : public ElasticityBase {
public:
    IsotropicElasticity() : ElasticityBase() {}
    virtual NumT energy(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const = 0;
    NumT energy(const Mat3& F, const NumT Jp, const HardeningBase& hardening)
        const override {
        Eigen::JacobiSVD<Mat3> svd(
            F, Eigen::ComputeFullU | Eigen::ComputeFullV
        );
        return energy(svd.singularValues(), Jp, hardening);
    }
    Mat3 KirchhoffStress(
        const Mat3& F, const NumT Jp, const HardeningBase& hardening
    ) const override {
        Eigen::JacobiSVD<Mat3> svd(
            F, Eigen::ComputeFullU | Eigen::ComputeFullV
        );
        return KirchhoffStress(
            svd.matrixU(), svd.singularValues(), Jp, hardening
        );
    }
    Mat3 KirchhoffStress(
        const Mat3& U, const Vec3& sig, const NumT Jp,
        const HardeningBase& hardening
    ) const {
        return U * KirchhoffStressSig(sig, Jp, hardening).asDiagonal() *
               U.transpose();
    }

    virtual Vec3 KirchhoffStressSig(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const = 0;

    virtual Mat3 KirchhoffJacobian(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const = 0;

    virtual Mat3 returnMapping(
        const Mat3& FTrial, const Plastic::YieldSurfaceBase& yield,
        const NumT Jp, const HardeningBase& hardening
    ) const override;
    virtual Vec3 returnMappingSig(
        const Vec3& sigTrial, const Plastic::YieldSurfaceBase& yield,
        const NumT Jp, const HardeningBase& hardening
    ) const = 0;

    Vec3 cuttingPlaneReturnMapping(
        const Vec3 sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
        const Hardening::HardeningBase& hardening
    ) const;

protected:
};
}  // namespace Elastic
}  // namespace MPM
