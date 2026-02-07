#include "HenckyStVK.hpp"
#include <Eigen/src/SVD/JacobiSVD.h>
#include "Common/CustomTypes.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
namespace MPM {
namespace Elastic {
NumT HenckyStVK::energy(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT J = sig.prod();
    NumT h = hardening(Jp);
    Vec3 hencky(std::log(sig[0]), std::log(sig[1]), std::log(sig[2]));

    return h * m_shear * (hencky.cwiseProduct(hencky)).sum() +
           0.5 * h * m_lambda * hencky.sum() * hencky.sum();
}
Vec3 HenckyStVK::KirchhoffStressSig(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT h = hardening(Jp);
    Vec3 hencky(std::log(sig[0]), std::log(sig[1]), std::log(sig[2]));
    return 2 * h * m_shear * hencky +
           h * m_lambda * hencky.sum() * Type::Vec3::Ones();
}
Mat3 HenckyStVK::KirchhoffJacobian(
    const Vec3& sig, const NumT Jp, const HardeningBase& hardening
) const {
    NumT h = hardening(Jp);
    Mat3 kirchJacobian = 2 * h * m_shear * sig.cwiseInverse().asDiagonal();
    kirchJacobian +=
        h * m_lambda * Mat3::Ones() * sig.cwiseInverse().asDiagonal();
    return kirchJacobian;
}
Vec3 HenckyStVK::returnMappingSig(
    const Vec3& sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
    const HardeningBase& hardening
) const {
    Vec3 sigNew = sig;
    if (yield.deformationConstraint()) {
        sigNew = yield.projectDeformation(sig);
    } else {
        // Project stress
        Vec3 stressTrial = KirchhoffStressSig(sig, Jp, hardening);
        const Vec3 stress = yield.projectStress(stressTrial);
        if (stress != stressTrial) {
            NumT k = stress.sum() * m_lambda / (2 * m_shear + 3 * m_lambda);
            Vec3 s = (stress.array() - k) / (2 * m_shear * hardening(Jp));
            sigNew = Vec3(std::exp(s[0]), std::exp(s[1]), std::exp(s[2]));
        }
    }
    return sigNew;
}
Vec3 HenckyStVKCutting::returnMappingSig(
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
            if (yield.returnMapType() != Plastic::ReturnMapType::ResistExpand &&
                J > 1) {
                sigNew = Vec3::Ones();
            } else {
                sigNew = cuttingPlaneReturnMapping(sig, yield, Jp, hardening);
            }
        }
    }
    return sigNew;
}
}  // namespace Elastic
}  // namespace MPM
