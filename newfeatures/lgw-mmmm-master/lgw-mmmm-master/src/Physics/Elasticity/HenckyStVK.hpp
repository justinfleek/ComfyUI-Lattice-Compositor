#pragma once

#include "Common/CustomTypes.hpp"
#include "ElasticityBase.hpp"
namespace MPM {
namespace Elastic {
class HenckyStVK : public IsotropicElasticity {
public:
    HenckyStVK(NumT E, NumT mu) {
        m_lambda = E * mu / ((1 + mu) * (1 - mu));
        m_shear = E / (2 + 2 * mu);
    }
    Params::ElasticityType type() const override {
        return Params::ElasticityType::HenckyStVK;
    }

    NumT energy(const Vec3& sig, const NumT Jp, const HardeningBase& hardening)
        const override;
    Vec3 returnMappingSig(
        const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
        const HardeningBase& hardening
    ) const override;

    NumT lambda() const { return m_lambda; }
    NumT shear() const { return m_shear; }

    Vec3 KirchhoffStressSig(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const override;
    Mat3 KirchhoffJacobian(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const override;

protected:
    NumT m_lambda;  /// First Lame parameter
    NumT m_shear;   /// Shear modulus
};
class HenckyStVKCutting : public HenckyStVK {
public:
    HenckyStVKCutting(NumT E, NumT mu) : HenckyStVK(E, mu) {}
    Vec3 returnMappingSig(
        const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
        const HardeningBase& hardening
    ) const override;
};
}  // namespace Elastic
}  // namespace MPM
