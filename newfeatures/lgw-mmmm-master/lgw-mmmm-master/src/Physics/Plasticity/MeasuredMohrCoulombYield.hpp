#pragma once
#include <filesystem>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include "YieldSurfaceBase.hpp"
namespace MPM {
namespace Plastic {
class MeasuredMohrCoulombYield : public YieldSurfaceBase {
public:
    MeasuredMohrCoulombYield(const std::filesystem::path& filename, NumT scale)
        : m_scale(scale) {
        std::ifstream file(filename);
        if (file.fail()) {
            throw std::invalid_argument(
                "Yield surface file " + filename.string() + " does not exist!"
            );
        }
        file >> m_endpoints[0] >> m_endpoints[1] >> m_divisions;
        m_dx = (m_endpoints[1] - m_endpoints[0]) / m_divisions;
        NumT a1, a2, a3, a4;
        while (file >> a1 >> a2 >> a3 >> a4) {
            m_pointVals.push_back(a1);
            m_curves.emplace_back(a2, a3, a4);
        }
        // for (int i = 0; i < m_curves.size(); ++i) {
        // 	std::cout << m_pointVals[i] << " " << m_curves[i].transpose() <<
        // std::endl;
        // }
    }
    Params::PlasticityType type() const override {
        return Params::PlasticityType::SandMC;
    }
    ReturnMapType returnMapType() const override {
        return ReturnMapType::PreserveVolume | ReturnMapType::ResistShrink |
               ReturnMapType::SandLike;
    }
    bool deformationConstraint() const override { return false; }
    Vec3 projectStress(const Vec3& sig) const override { return sig; }

    NumT value(const Vec3& T) const override {
        Vec3 scaledT = T / m_scale;
        NumT x = (scaledT[0] + scaledT[2]) * 0.5;
        NumT rad = (T[0] - T[2]) * 0.5;
        if (x > m_endpoints[1]) {
            NumT f =
                m_pointVals.back() + (x - m_endpoints[1]) * m_curves.back()[2];
            // f = std::max(f, NumT(0));
            // std::cout << f << std::endl;
            return rad - f * m_scale;
        } else if (x < m_endpoints[0]) {
            NumT f = m_pointVals[0] + (x - m_endpoints[0]) * m_curves[0][2];
            // return rad - f * m_scale;
            f = std::max(f, NumT(0));
            return rad - f * m_scale;
            // return std::max(rad - f * m_scale, NumT(0));
        } else {
            int idx = (x - m_endpoints[0]) / m_dx;
            NumT d = x - (m_endpoints[0] + idx * m_dx);
            if (d != d) {
                std::cout << x << " " << idx << " " << T.transpose()
                          << std::endl;
            }
            NumT f =
                m_pointVals[idx] + m_curves[idx].dot(Vec3(d * d * d, d * d, d));
            return rad - f * m_scale;
        }
    }
    Vec3 gradient(const Vec3& T) const override {
        Vec3 scaledT = T / m_scale;
        NumT x = (scaledT[0] + scaledT[2]) * 0.5;
        Vec3 g0;
        if (x > m_endpoints[1]) {
            NumT f =
                m_pointVals.back() + (x - m_endpoints[1]) * m_curves.back()[2];
            // g0 = T;
            // NumT dfdx = (f >= 0)? m_curves.back()[2]: 0;
            NumT dfdx = m_curves.back()[2];
            g0 = Vec3(0.5 - 0.5 * dfdx, 0, -0.5 - 0.5 * dfdx);
        } else if (x < m_endpoints[0]) {
            NumT dfdx = m_curves[0][2];
            g0 = Vec3(0.5 - 0.5 * dfdx, 0, -0.5 - 0.5 * dfdx);
        } else {
            int idx = (x - m_endpoints[0]) / m_dx;
            NumT d = x - (m_endpoints[0] + idx * m_dx);
            NumT dfdx = m_curves[idx].dot(Vec3(3 * d * d, 2 * d, 1));
            g0 = Vec3(0.5 - 0.5 * dfdx, 0, -0.5 - 0.5 * dfdx);
        }
        Vec3 g1(g0[1], g0[0], g0[2]);
        Vec3 g2(g0[0], g0[2], g0[1]);
        return g0 + g1 * pow(m_gradTol, T[0] - T[1]) +
               g2 * pow(m_gradTol, T[1] - T[2]);
        // return Vec3(1 + m_coneRatio, 0, 1 - m_coneRatio);
    }

private:
    Type::Vec2 m_endpoints;
    uint16_t m_divisions;
    NumT m_scale, m_dx;
    std::vector<NumT> m_pointVals;
    std::vector<Type::Vec3> m_curves;
    NumT m_gradTol = 1e-3;
    // NumT m_cohesion = 0;
};
}  // namespace Plastic
}  // namespace MPM
