#pragma once

#include "YieldSurfaceBase.hpp"
namespace MPM {
namespace Plastic {
class FluidYield : public YieldSurfaceBase {
public:
    FluidYield() {}
    Params::PlasticityType type() const override {
        return Params::PlasticityType::Fluid;
    }
    ReturnMapType returnMapType() const override {
        return ReturnMapType::PreserveVolume | ReturnMapType::ResistShrink |
               ReturnMapType::ResistExpand;
    }
    bool deformationConstraint() const override { return true; }
    Vec3 projectDeformation(const Vec3& sig) const override {
        return Vec3::Constant(std::cbrt(sig.prod()));
    }
    Vec3 projectStress(const Vec3& sig) const override {
        return Vec3::Constant(sig.mean());
    }
    NumT value(const Vec3& T) const override {
        Vec3 dev = T.array() - T.mean();
        return dev.norm();
    }
    Vec3 gradient(const Vec3& T) const override {
        Vec3 dev = T.array() - T.mean();
        return dev.normalized();
    }
};
}  // namespace Plastic
}  // namespace MPM
