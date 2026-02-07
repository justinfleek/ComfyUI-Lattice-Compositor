#include "FixedCorotated.hpp"
#include <Eigen/src/Core/Matrix.h>
#include <Eigen/src/Core/util/Constants.h>
#include <Eigen/src/SVD/JacobiSVD.h>
#include <cmath>
#include <iostream>
#include <limits>
#include "Common/CustomTypes.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
namespace MPM {
namespace Elastic {
// NumT FixedCorotated::hardening(const NumT Jp) const {
//     return std::max((NumT)0.1, std::min((NumT)5, (NumT)exp(10 * (1. - Jp))));
// }
NumT FixedCorotated::energy(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT J = sig.prod();
    NumT h = hardening(Jp);

    return h * m_shear * (sig - Vec3::Ones()).squaredNorm() +
           0.5 * h * m_lambda * (J - 1) * (J - 1);
}
Vec3 FixedCorotated::KirchhoffStressSig(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT J = sig.prod();
    NumT h = hardening(Jp);
    return 2 * h * m_shear * (sig.cwiseProduct(sig) - sig) +
           h * m_lambda * (J - 1) * J * Type::Vec3::Ones();
}
Mat3 FixedCorotated::KirchhoffJacobian(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    const NumT J = sig.prod();
    const NumT h = hardening(Jp);
    Mat3 kirchJacobian =
        2 * h * m_shear * (2 * sig.array() - 1).matrix().asDiagonal();
    kirchJacobian += h * m_lambda * (2 * J - 1) * J *
                     sig.cwiseInverse().asDiagonal() * Mat3::Ones();
    return kirchJacobian;
}
Vec3 FixedCorotated::returnMappingSig(
    const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
    const HardeningBase& hardening
) const {
    Vec3 sigNew = sig;
    if (yield.deformationConstraint()) {
        sigNew = yield.projectDeformation(sig);
    } else {
        const NumT J = sig.prod();
        const NumT h = hardening(Jp);
        if (yield.value(KirchhoffStressSig(sigNew, Jp, hardening)) > 0) {
            sigNew = cuttingPlaneReturnMapping(sig, yield, Jp, hardening);
        }
    }
    return sigNew;
}
}  // namespace Elastic
}  // namespace MPM
