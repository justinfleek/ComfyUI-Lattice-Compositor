#pragma once

#include "YieldSurfaceBase.hpp"
namespace MPM {
namespace Plastic {
class SnowYield : public YieldSurfaceBase {
public:
    SnowYield() {}
    Params::PlasticityType type() const override {
        return Params::PlasticityType::Snow;
    }
    ReturnMapType returnMapType() const override {
        return ReturnMapType::ResistExpand | ReturnMapType::ResistShrink;
    }
    bool deformationConstraint() const override { return true; }
    Vec3 projectDeformation(const Vec3& sig) const override {
        Vec3 newSig = sig;
        newSig = newSig.cwiseMax(m_sigMin).cwiseMin(m_sigMax);
        return newSig;
    }
    NumT value(const Vec3& T) const override { return 0; }
    Vec3 gradient(const Vec3& T) const override { return Vec3::Zero(); }

private:
    NumT m_sigMin = 1 - 2.5e-2;
    NumT m_sigMax = 1 + 4.5e-3;
};
}  // namespace Plastic
}  // namespace MPM
