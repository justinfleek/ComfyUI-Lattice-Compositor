#pragma once

#include "Common/CustomTypes.hpp"
#include "ElasticityBase.hpp"
namespace MPM {
namespace Elastic {
class FixedCorotated : public IsotropicElasticity {
public:
    FixedCorotated(NumT E, NumT mu) {
        m_lambda = E * mu / ((1 + mu) * (1 - mu));
        m_shear = E / (2 + 2 * mu);
    }
    Params::ElasticityType type() const override {
        return Params::ElasticityType::FixedCorotated;
    }

    NumT energy(const Vec3& sig, const NumT Jp, const HardeningBase& hardening)
        const override;
    Vec3 returnMappingSig(
        const Vec3& FTrial, const Plastic::YieldSurfaceBase& yield,
        const NumT Jp, const HardeningBase& hardening
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
private:
    NumT m_lambda;  /// First Lame parameter
    NumT m_shear;   /// Shear modulus
};
}  // namespace Elastic
}  // namespace MPM
