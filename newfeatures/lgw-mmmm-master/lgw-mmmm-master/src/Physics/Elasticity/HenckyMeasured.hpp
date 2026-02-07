#pragma once

#include <sys/types.h>
#include <cstdint>
#include <filesystem>
#include <vector>
#include "Common/CustomTypes.hpp"
#include "ElasticityBase.hpp"
namespace MPM {
namespace Elastic {
class CubicCurve {
public:
    CubicCurve() {}
    CubicCurve(NumT start, NumT end, uint16_t divisions)
        : m_endpoints(start, end),
          m_divisions(divisions),
          m_dx((end - start) / divisions) {
        m_vals.reserve(divisions + 1);
        m_cubics.reserve(divisions + 1);
    }
    NumT interpolate(NumT x) const;
    NumT deriv(NumT x) const;
    NumT deriv2(NumT x) const;

    Type::Vec2 m_endpoints;
    uint16_t m_divisions;
    NumT m_dx;
    std::vector<NumT> m_vals;
    std::vector<Type::Vec3> m_cubics;
};
class HenckyMeasured : public IsotropicElasticity {
public:
    HenckyMeasured(const std::filesystem::path& filepath, NumT scale);
    Params::ElasticityType type() const override {
        return Params::ElasticityType::HenckyMeasured;
    }

    NumT energy(const Vec3& sig, const NumT Jp, const HardeningBase& hardening)
        const override;
    Vec3 returnMappingSig(
        const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
        const HardeningBase& hardening
    ) const override;

    Vec3 KirchhoffStressSig(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const override;
    Mat3 KirchhoffJacobian(
        const Vec3& sig, const NumT Jp, const HardeningBase& hardening
    ) const override;

protected:
private:
    CubicCurve m_mCubic, m_bCubic;
    NumT m_scale;
};
}  // namespace Elastic
}  // namespace MPM
