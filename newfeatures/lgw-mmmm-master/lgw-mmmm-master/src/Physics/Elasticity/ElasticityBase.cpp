#include "ElasticityBase.hpp"
#include <iostream>
#include "Physics/Plasticity/YieldSurfaceBase.hpp"
namespace MPM {
namespace Elastic {

Mat3 IsotropicElasticity::returnMapping(
    const Mat3& FTrial, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
    const HardeningBase& hardening
) const {
    Eigen::JacobiSVD<Mat3> svd(
        FTrial, Eigen::ComputeFullU | Eigen::ComputeFullV
    );
    Type::Vec3 sig = svd.singularValues();
    Type::Vec3 sigNew = returnMappingSig(sig, yield, Jp, hardening);
    return svd.matrixU() * sigNew.asDiagonal() * svd.matrixV().transpose();
}
Vec3 IsotropicElasticity::cuttingPlaneReturnMapping(
    const Vec3 sig, const Plastic::YieldSurfaceBase& yield, const NumT Jp,
    const Hardening::HardeningBase& hardening
) const {
    Vec3 sigNew = sig;
    NumT stepSize = 1.0;
    bool solved = false;
    NumT tol = 1e-6;
    NumT J = sig.prod();
    bool volumePreserving =
        bool(yield.returnMapType() | Plastic::ReturnMapType::PreserveVolume);
    if (yield.value(KirchhoffStressSig(
            Vec3::Constant(cbrt(sigNew.prod())), Jp, hardening
        )) > 0) {
        sigNew = Vec3::Constant(cbrt(sigNew.prod()));
        volumePreserving = false;
    }
    for (int it = 0; it < 50; ++it) {
        Vec3 stress = KirchhoffStressSig(sigNew, Jp, hardening);
        NumT y = yield.value(stress);
        Vec3 yGrad = yield.gradient(stress);
        Vec3 flowDir = yGrad;

        if (abs(stress[0] - stress[2]) < 1e-5 || stepSize < 1e-15) {
            // flowDir = Vec3::Ones();
            volumePreserving = false;
            // stepSize = 1;
        }
        if (volumePreserving) {
            flowDir.array() -= flowDir.mean();
        }
        if (it == 0) {
            Mat3 kirchJacobian = KirchhoffJacobian(sigNew, Jp, hardening);
            stepSize =
                1. / (yGrad.dot(kirchJacobian * flowDir.cwiseProduct(sigNew)));
            if (!std::isfinite(stepSize)) {
                stepSize = 1;
            }
        }
        // std::cout << sigNew.transpose() << " " << stress.transpose() << " "
        // << y
        //           << " " << flowDir.transpose() << " " << stepSize <<
        //           std::endl;
        // std::cout << "Def: " << sigNew.transpose() << std::endl;
        // std::cout << "Stress: " << stress.transpose() << " Yield: " << y
        //           << std::endl;
        // std::cout << "Flow dir: " << flowDir.transpose()
        //           << " step: " << stepSize << std::endl;

        if (y < tol) {
            solved = true;
            break;
        }
        int ss;
        for (ss = 0; ss < 50; ++ss) {
            Vec3 sigTest = sigNew - stepSize * y * flowDir;
            int projectMode = 0;
            if (sigTest[0] >= sigTest[1] && sigTest[1] >= sigTest[2]) {
                projectMode = 0;
            } else if (sigTest[0] < sigTest[1] && sigTest[0] > sigTest[2]) {
                projectMode += 1;
            } else if (sigTest[1] < sigTest[2] && sigTest[0] > sigTest[2]) {
                projectMode += 2;
            } else {
                projectMode = 3;
            }
            switch (projectMode) {
            case 1: {
                sigTest.head<2>().array() = sigTest.head<2>().mean();
                break;
            }
            case 2: {
                sigTest.tail<2>().array() = sigTest.tail<2>().mean();
                break;
            }
            case 3: {
                sigTest.array() = sigTest.mean();
                break;
            }
            default: {
            }
            }
            if (volumePreserving) {
                sigTest *= cbrt(J / sigTest.prod());
            }

            if ((sigTest.array() > 0).all()) {
                Vec3 stressTest = KirchhoffStressSig(sigTest, Jp, hardening);
                NumT testYield = yield.value(stressTest);

                // std::cout << "\t" << ss << std::endl;
                //             std::cout << "\tDef: " << sigTest.transpose()
                //                       << ", step size: " << stepSize <<
                //                       std::endl;
                //             std::cout << "\tStress: " <<
                //             stressTest.transpose()
                //                       << " Yield: " << testYield <<
                //                       std::endl;
                // std::cout << y << " " << testYield << " " << stepSize
                //           << std::endl;
                if (testYield > -tol && testYield < y) {
                    sigNew = sigTest;
                    // stepSize *= std::min(y / (y - testYield), NumT(10));
                    stepSize *= y / (y - testYield);
                    break;
                }
            }
            stepSize *= 0.5;
        }
        if (stepSize < 1e-50) {
            break;
        }
        if (ss >= 20) {
            if (volumePreserving) {
                volumePreserving = false;
                stepSize = 1;
            } else {
                break;
            }
        }
    }
    if (!solved) {
        // sigNew = Vec3::Ones();
        Vec3 sigInc = Vec3::Constant(cbrt(J)).cwiseQuotient(sigNew).cwiseSqrt();
        for (int it = 0; it < 50; it++) {
            Vec3 s = KirchhoffStressSig(sigNew, Jp, hardening);
            NumT yT = yield.value(s);
            if (abs(yT) < tol) {
                break;
            }
            if (yT > 0) {
                sigNew = sigNew.cwiseProduct(sigInc);
            } else {
                sigNew = sigNew.cwiseQuotient(sigInc);
            }
            sigInc = sigInc.cwiseSqrt();
        }
    }
    return sigNew;
}
}  // namespace Elastic
}  // namespace MPM
