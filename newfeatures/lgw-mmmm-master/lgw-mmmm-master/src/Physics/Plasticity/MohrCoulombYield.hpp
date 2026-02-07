#pragma once
#include <iostream>
#include "YieldSurfaceBase.hpp"
namespace MPM {
namespace Plastic {
class MohrCoulombYield : public YieldSurfaceBase {
public:
    MohrCoulombYield(NumT coneRatio) : m_coneRatio(coneRatio) {}
    Params::PlasticityType type() const override {
        return Params::PlasticityType::SandMC;
    }
    ReturnMapType returnMapType() const override {
        return ReturnMapType::PreserveVolume | ReturnMapType::ResistShrink |
               ReturnMapType::SandLike;
    }
    bool deformationConstraint() const override { return false; }
    Vec3 projectStress(const Vec3& sig) const override {
        NumT p = sig.sum();

        if (p >= 0) {
            return Vec3::Constant(0);
        } else if (sig[0] - sig[2] > m_coneRatio * (sig[0] + sig[2])) {
            Vec3 searchDir(-m_coneRatio - 3, 2 * m_coneRatio, -m_coneRatio + 3);
            NumT r = ((m_coneRatio + 1) * sig[0] + (m_coneRatio - 1) * sig[2]) /
                     (2 * m_coneRatio * m_coneRatio + 6);
            Vec3 newSig = sig + r * searchDir;
            if (newSig[0] < newSig[1]) {
                newSig[0] = (1 - m_coneRatio) / (3 - m_coneRatio) * p;
                newSig[1] = newSig[0];
                newSig[2] = (1 + m_coneRatio) / (3 - m_coneRatio) * p;
            } else if (newSig[1] < newSig[2]) {
                newSig[0] = (1 - m_coneRatio) / (m_coneRatio + 3) * p;
                newSig[2] = (1 + m_coneRatio) / (m_coneRatio + 3) * p;
                newSig[1] = newSig[2];
            }
            return newSig;
        } else {
            return sig;
        }
    }

    // TODO: Fill these out
    NumT value(const Vec3& T) const override {
        return (T[0] - T[2]) + m_coneRatio * (T[0] + T[2]);
    }
    Vec3 gradient(const Vec3& T) const override {
        Vec3 mainGrad(1 + m_coneRatio, 0, 1 - m_coneRatio);
        Vec3 g1(0, 1 + m_coneRatio, 1 - m_coneRatio);
        Vec3 g2(1 + m_coneRatio, 1 - m_coneRatio, 0);
        return mainGrad + g1 * pow(m_gradTol, T[0] - T[1]) +
               g2 * pow(m_gradTol, T[1] - T[2]);
        // return Vec3(1 + m_coneRatio, 0, 1 - m_coneRatio);
    }

private:
    NumT m_coneRatio = 0.338;
    NumT m_gradTol = 1e-5;
    // NumT m_cohesion = 0;
};
}  // namespace Plastic
}  // namespace MPM
