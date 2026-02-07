#include "HenckyMeasured.hpp"
#include <cmath>
#include <fstream>
#include <iostream>
#include <stdexcept>
namespace MPM {
namespace Elastic {
NumT CubicCurve::interpolate(NumT x) const {
    if (x < m_endpoints[0]) {
        return std::max((x - m_endpoints[0]) * m_cubics[0][2], NumT(0));
    } else if (x > m_endpoints[1]) {
        return std::max((x - m_endpoints[1]) * m_cubics.back()[2], NumT(0));
    } else {
        int idx = (x - m_endpoints[0]) / m_dx;
        NumT diff = x - (m_endpoints[0] + idx * m_dx);
        return m_vals[idx] +
               m_cubics[idx].dot(Vec3(diff * diff * diff, diff * diff, diff));
    }
}
NumT CubicCurve::deriv(NumT x) const {
    if (x < m_endpoints[0]) {
        return (x - m_endpoints[0]) * m_cubics[0][2] >= 0 ? m_cubics[0][2] : 0;
    } else if (x > m_endpoints[1]) {
        return (x - m_endpoints[1]) * m_cubics.back()[2] >= 0
                   ? m_cubics.back()[2]
                   : 0;
    } else {
        int idx = (x - m_endpoints[0]) / m_dx;
        NumT diff = x - (m_endpoints[0] + idx * m_dx);
        return m_cubics[idx].dot(Vec3(3 * diff * diff, 2 * diff, 1));
    }
}
NumT CubicCurve::deriv2(NumT x) const {
    if (x < m_endpoints[0]) {
        return 0;
    } else if (x > m_endpoints[1]) {
        return 0;
    } else {
        int idx = (x - m_endpoints[0]) / m_dx;
        NumT diff = x - (m_endpoints[0] + idx * m_dx);
        return m_cubics[idx].dot(Vec3(6 * diff, 2, 0));
    }
}
HenckyMeasured::HenckyMeasured(
    const std::filesystem::path& filename, NumT scale
)
    : m_scale(scale) {
    std::ifstream file(filename);
    if (file.fail()) {
        throw std::invalid_argument(
            "Elasticity file " + filename.string() + " does not exist!"
        );
    }
    NumT start, end;
    uint16_t divisions;
    file >> start >> end >> divisions;
    m_mCubic = CubicCurve(start, end, divisions);
    for (int i = 0; i < divisions + 1; ++i) {
        NumT a1, a2, a3, a4;
        file >> a1 >> a2 >> a3 >> a4;
        m_mCubic.m_vals.push_back(a1);
        m_mCubic.m_cubics.emplace_back(a2, a3, a4);
    }
    file >> start >> end >> divisions;
    m_bCubic = CubicCurve(start, end, divisions);
    for (int i = 0; i < divisions + 1; ++i) {
        NumT a1, a2, a3, a4;
        file >> a1 >> a2 >> a3 >> a4;
        m_bCubic.m_vals.push_back(a1);
        m_bCubic.m_cubics.emplace_back(a2, a3, a4);
    }
}
NumT HenckyMeasured::energy(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT h = hardening(Jp);
    Vec3 hencky(log(sig[0]), log(sig[1]), log(sig[2]));
    NumT logVol = hencky.sum();
    NumT devHencky = (hencky.array() - hencky.mean()).matrix().squaredNorm();
    NumT e = m_mCubic.interpolate(devHencky) * devHencky +
             m_bCubic.interpolate(logVol) * logVol * logVol;
    return e * h * m_scale;
}
Vec3 HenckyMeasured::KirchhoffStressSig(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT h = hardening(Jp);
    Vec3 hencky(log(sig[0]), log(sig[1]), log(sig[2]));
    NumT logVol = hencky.sum();
    Vec3 devHencky = hencky.array() - hencky.mean();
    NumT devHenckyF2 = devHencky.squaredNorm();

    NumT lambda =
        m_bCubic.deriv(logVol) * logVol + 2 * m_bCubic.interpolate(logVol);
    NumT shearMag = 2 * (m_mCubic.deriv(devHenckyF2) * devHenckyF2 +
                         m_mCubic.interpolate(devHenckyF2));
    Vec3 kirch = shearMag * devHencky + Vec3::Constant(lambda * logVol);
    return kirch * h * m_scale;
}
Mat3 HenckyMeasured::KirchhoffJacobian(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT h = hardening(Jp);
    Vec3 hencky(log(sig[0]), log(sig[1]), log(sig[2]));
    Vec3 sInv = sig.cwiseInverse();
    NumT logVol = hencky.sum();
    Vec3 devHencky = hencky.array() - hencky.mean();
    NumT devHenckyF2 = devHencky.squaredNorm();

    NumT m2 = m_mCubic.deriv2(devHenckyF2);
    NumT dm = m_mCubic.deriv(devHenckyF2);
    NumT m = m_mCubic.interpolate(devHenckyF2);
    NumT b2 = m_bCubic.deriv2(logVol);
    NumT db = m_bCubic.deriv(logVol);
    NumT b = m_bCubic.interpolate(logVol);

    Mat3 D;
    D << 2, -1, -1, -1, 2, -1, -1, -1, 2;
    D /= 3;

    Mat3 ret =
        4 * (m2 * devHenckyF2 + 2 * dm) * devHencky * devHencky.transpose();
    ret += 2 * (dm * devHenckyF2 + m) * D;
    ret += Mat3::Constant(b2 * logVol * logVol + 4 * db * logVol + 2 * b);
    ret = ret * sInv.asDiagonal();

    return ret * h * m_scale;
}
Vec3 HenckyMeasured::returnMappingSig(
    const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
    const HardeningBase& hardening
) const {
    Vec3 sigNew = sig;
    if (yield.deformationConstraint()) {
        sigNew = yield.projectDeformation(sig);
    } else {
        const NumT J = sig.prod();
        const NumT h = hardening(Jp);
        if (std::isnan(Jp)) {
            throw std::runtime_error("what on earth?");
        }
        if (yield.value(KirchhoffStressSig(sigNew, Jp, hardening)) >= 0) {
            // if (J > 1) {
            // sigNew = Vec3::Constant(cbrt(J));
            // sigNew = Vec3::Ones();
            // } else {
            sigNew = cuttingPlaneReturnMapping(sig, yield, Jp, hardening);
            // }
        }
    }
    return sigNew;
}
}  // namespace Elastic
}  // namespace MPM
