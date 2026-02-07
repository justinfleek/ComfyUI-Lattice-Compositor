#include <iostream>
#include <random>
#include "Common/CustomTypes.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Elasticity/HenckyMeasured.hpp"
#include "Physics/Elasticity/HenckyStVK.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/MeasuredMohrCoulombYield.hpp"

int main(int argc, char** argv) {
    if (argc < 3) {
        std::cout << "File name required!" << std::endl;
        return -1;
    }
    MPM::Elastic::HenckyMeasured hmElastic(argv[1], 1);
    // MPM::Elastic::FixedCorotated hmElastic(5e5, 0.3);
    MPM::Plastic::MeasuredMohrCoulombYield dpYield(argv[2], 1);
    MPM::Hardening::NoHardening hardening;

    std::mt19937 gen(1024);
    std::normal_distribution<Type::NumT> dist(1, 1);
    std::normal_distribution<Type::NumT> distPress(0, 1e-2);
    std::normal_distribution<Type::NumT> distDev2(-1e-4, 1e-4);

    int successes = 0;
    int trials = 1000000;
    std::cout << "Enter number of trials: ";
    std::cin >> trials;
    const Type::NumT tol = 1e-7;
    for (int it = 0; it < trials; ++it) {
        Type::NumT p = distPress(gen);
        // Type::Vec3 testF = Type::Vec3::Constant(1 + p);
        // testF[0] += dist(gen) * p;//+ distDev2(gen);
        // testF[1] += dist(gen) * p;//+ distDev2(gen);
        // testF[2] += dist(gen) * p;//+ distDev2(gen);
        Type::Vec3 testF = Type::Vec3::Constant(1);
        testF[0] += dist(gen) * 1e-2;  //+ distDev2(gen);
        testF[1] += dist(gen) * 1e-2;  //+ distDev2(gen);
        testF[2] += dist(gen) * 1e-2;  //+ distDev2(gen);

        if ((testF.array() < 0).any() || testF.prod() > 1) {
            it--;
            continue;
        }

        if (testF[0] < testF[1]) {
            std::swap(testF[0], testF[1]);
        }
        if (testF[1] < testF[2]) {
            std::swap(testF[1], testF[2]);
        }
        if (testF[0] < testF[1]) {
            std::swap(testF[0], testF[1]);
        }

        if (dpYield.value(hmElastic.KirchhoffStressSig(testF, 1, hardening)) <
            0) {
            it--;
            continue;
        }

        Type::Vec3 sigA =
            hmElastic.KirchhoffStressSig(testF, 1, hardening).transpose();
        Type::Vec3 fP, fN, sigFD;
        for (int i = 0; i < 3; ++i) {
            fP = testF;
            fP[i] += tol;
            fN = testF;
            fN[i] -= tol;
            sigFD[i] = (hmElastic.energy(fP, 1, hardening) -
                        hmElastic.energy(fN, 1, hardening)) /
                       tol / 2;
        }
        sigFD = sigFD.cwiseProduct(testF);
        if (sigA.norm() == 0 || (sigA - sigFD).norm() / sigA.norm() < 1e-4) {
            // successes++;
        } else {
            std::cout << sigA.transpose() << " " << sigFD.transpose()
                      << std::endl;
        }
        // std::cout << sigA.transpose() << " " << sigFD.transpose()
        //           << std::endl;

        // Type::Mat3 jacFD;
        // for (int i = 0; i < 3; ++i) {
        //     fP = testF;
        //     fP[i] += tol;
        //     fN = testF;
        //     fN[i] -= tol;
        //     sigFD = hmElastic.KirchhoffStressSig(fP, 1, hardening) -
        //             hmElastic.KirchhoffStressSig(fN, 1, hardening);
        //     sigFD /= tol * 2;
        //     jacFD.col(i) = sigFD;
        // }
        // std::cout << "Expected:\n"
        //           << jacFD << "\nGot:\n"
        //           << hmElastic.KirchhoffJacobian(testF, 1, hardening)
        //           << std::endl;
        // std::cout << "Trial: " << it << std::endl;
        Type::Vec3 r = hmElastic.returnMappingSig(testF, dpYield, 1, hardening);
        if (dpYield.value(hmElastic.KirchhoffStressSig(r, 1, hardening)) <=
            1e-6) {
            successes++;
        } else {
            std::cout << dpYield.value(
                             hmElastic.KirchhoffStressSig(r, 1, hardening))
                      << std::endl;
        }
        // hmElastic.returnMapping(testF.asDiagonal(), dpYield, 1, hardening)
        //     .diagonal();
        // std::cout << testF.transpose() << " " << r.transpose() << std::endl;
        // cuttingPlaneReturnMapping(testF, dpYield, 1, hardening);
    }
    std::cout << "Unit tests: " << successes << "/" << trials << " succeeded. "
              << ((successes == trials) ? "Success!" : "Fail!") << std::endl;
}
