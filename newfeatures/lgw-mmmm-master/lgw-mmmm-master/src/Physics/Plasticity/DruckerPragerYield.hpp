#pragma once

#include "YieldSurfaceBase.hpp"
namespace MPM {
namespace Plastic {
class DruckerPragerYield : public YieldSurfaceBase {
public:
    DruckerPragerYield(NumT coneRatio) {
        m_coneRatio =
            sqrt(3.) * 2 * coneRatio / (3 - coneRatio);  // Daviet et al. 2016
    }
    Params::PlasticityType type() const override {
        return Params::PlasticityType::SandDP;
    }
    ReturnMapType returnMapType() const override {
        return ReturnMapType::PreserveVolume | ReturnMapType::ResistShrink |
               ReturnMapType::SandLike;
    }
    bool deformationConstraint() const override { return false; }
    Vec3 projectStress(const Vec3& sig) const override {
        NumT p = sig.mean();
        Vec3 dev = sig.array() - p;

        NumT maxDev = (m_cohesion - p) * m_coneRatio;
        if (p >= m_cohesion) {
            return Vec3::Constant(m_cohesion);
        } else if (dev.squaredNorm() > maxDev * maxDev) {
            dev *= maxDev / dev.norm();
            return Vec3::Constant(p) + dev;
        } else {
            return sig;
        }
    }

    // TODO: Fill these out
    NumT value(const Vec3& T) const override {
        NumT p = T.mean();
        Vec3 dev = T.array() - p;

        NumT maxDev = (m_cohesion - p) * m_coneRatio;
        return dev.norm() - maxDev;
    }
    Vec3 gradient(const Vec3& T) const override {
        NumT p = T.mean();
        Vec3 dev = T.array() - p;

        return dev.normalized() + Vec3::Constant(m_coneRatio / 3);
    }

private:
    NumT m_coneRatio = 0.338;
    NumT m_cohesion = 0;
};
}  // namespace Plastic
}  // namespace MPM
