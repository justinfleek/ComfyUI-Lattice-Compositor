#include <iostream>
#include <random>
#include "Common/CustomTypes.hpp"
#include "Physics/Elasticity/HenckyStVK.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/DruckerPragerYield.hpp"
#include "Physics/Plasticity/MohrCoulombYield.hpp"

int main() {
    const Type::NumT r = 0.6;
    MPM::Plastic::MohrCoulombYield mcYield(r);

    std::mt19937 gen(1024);
    std::normal_distribution<Type::NumT> dist(-0.1, 0.2);

    Type::Vec3 stress(-1e4, -1.001e4, -6e4);
    Type::Vec3 projS = mcYield.projectStress(stress);
    std::cout << projS.transpose() << " " << projS.sum() << " "
              << projS[0] - projS[2] << " " << projS[0] + projS[2] << std::endl;

    MPM::Elastic::HenckyStVK elastic(5.5e5, 0.3);
    MPM::Plastic::DruckerPragerYield dpYield(r);
    Type::Vec3 F(1.1, 1.0, 0.8);
    Type::Mat3 Ftest = elastic.returnMapping(F.asDiagonal(), dpYield, 1,
                                             MPM::Hardening::NoHardening());
    Type::Mat3 tOrig = elastic.KirchhoffStress(F.asDiagonal(), 1,
                                               MPM::Hardening::NoHardening());
    auto dev = [](const Type::Mat3& m) -> Type::Vec3 {
        return m.diagonal().array() - m.trace() / 3.;
    };
    const double muFriction = sqrt(2. / 3.) * 2 * r / (3 - r);
	std::cout << muFriction << std::endl;
    std::cout << tOrig << dev(tOrig).normalized().transpose() << std::endl;
    std::cout << "Got:\n" << Ftest << std::endl;

    Type::Mat3 tGot =
        elastic.KirchhoffStress(Ftest, 1, MPM::Hardening::NoHardening());
    std::cout << tGot << " " << tGot.trace() << " "
              << dev(tGot).norm() / tGot.trace() * 3 << std::endl;

    const Type::Vec3 eDp(log(F[0]), log(F[1]), log(F[2]));
    const double eDpTr = eDp[0] + eDp[1] + eDp[2];
    const Type::Vec3 eHat = eDp - (eDpTr / 3.) * Type::Vec3(1., 1., 1.);
    const double eHatNorm = eHat.norm();
    double dGamma = eHatNorm + (3 * elastic.lambda() + 2 * elastic.shear()) /
                                   (2 * elastic.shear()) * eDpTr * muFriction;

    if (dGamma <= 0) {
        // Static - stress already in the yield surface
    } else {
        Type::Vec3 newSig;
        if ((eHatNorm <= 0) || (eDpTr > 0)) {
            // Expansion
            newSig[0] = 1.;
            newSig[1] = 1.;
            newSig[2] = 1.;
        } else {
            // Friction
            const Type::Vec3 hDp = eDp - dGamma * eHat / eHatNorm;
            newSig[0] = exp(hDp[0]);
            newSig[1] = exp(hDp[1]);
            newSig[2] = exp(hDp[2]);
        }
        std::cout << "Expected: " << newSig.transpose() << " " << newSig.prod()
                  << std::endl;
        Type::Mat3 tExp = elastic.KirchhoffStress(
            newSig.asDiagonal(), 1, MPM::Hardening::NoHardening());
        std::cout << tExp << " " << tExp.trace() << " "
                  << dev(tExp).norm() / tExp.trace() * 3 << std::endl;
    }  // dGamma

    projS = projS = dpYield.projectStress(stress);
    Type::Vec3 projDev = projS.array() - projS.mean();
    std::cout << projS.transpose() << " " << projS.sum() << " "
              << projDev.norm() / projS.mean()
              << sqrt(2. / 3) * (2 * r) / (3 - r) << std::endl;
}
