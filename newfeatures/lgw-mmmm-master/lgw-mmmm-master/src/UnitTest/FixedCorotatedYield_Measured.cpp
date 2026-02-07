#include <iostream>
#include <random>
#include "Common/CustomTypes.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/MeasuredMohrCoulombYield.hpp"
#include "Physics/Plasticity/MohrCoulombYield.hpp"

int main(int argc, char** argv) {
    if (argc < 1) {
        std::cout << "File name required!" << std::endl;
        return -1;
    }
    MPM::Elastic::FixedCorotated fcElastic(5e5, 0.4);
    MPM::Hardening::NoHardening hardening;
    MPM::Plastic::MeasuredMohrCoulombYield dpYield(argv[1], 0.01);

    std::mt19937 gen(1024);
    std::normal_distribution<Type::NumT> dist(-1e-5, 1e-4);

    int successes = 0;
    int trials = 1000000;
    std::cout << "Enter number of trials: ";
    std::cin >> trials;
    const Type::NumT tol = 1e-6;
    for (int it = 0; it < trials; ++it) {
        Type::Vec3 testF = Type::Vec3::Constant(1);
        testF[0] += dist(gen);
        testF[1] += dist(gen);
        testF[2] += dist(gen);

        // if (testF.prod() >= 1) {
        //     it--;
        //     continue;
        // }

        if (testF[0] < testF[1]) {
            std::swap(testF[0], testF[1]);
        }
        if (testF[1] < testF[2]) {
            std::swap(testF[1], testF[2]);
        }
        if (testF[0] < testF[1]) {
            std::swap(testF[0], testF[1]);
        }
        if (dpYield.value(
                fcElastic.KirchhoffStress(testF.asDiagonal(), 1, hardening)
                    .diagonal()) < 0) {
            it--;
            continue;
        }

        Type::Vec3 stress =
            fcElastic.KirchhoffStress(testF.asDiagonal(), 1, hardening)
                .diagonal();
        Type::Vec3 yieldGradFD;
        for (int i = 0; i < 3; ++i) {
            Type::NumT inc = 1e-5;
            Type::Vec3 stressP = stress, stressN = stress;
            stressP[i] += inc;
            stressN[i] -= inc;
            yieldGradFD[i] =
                (dpYield.value(stressP) - dpYield.value(stressN)) / (2 * inc);
        }
        // std::cout << "stress: " << stress.transpose()
        //           << "gradVal: " << dpYield.value(stress) << std::endl;
        // std::cout << "gradFD: " << yieldGradFD.transpose() << std::endl;
        // std::cout << "grad: " << dpYield.gradient(stress).transpose()
        //           << std::endl;

        Type::Mat3 projF =
            fcElastic.returnMapping(testF.asDiagonal(), dpYield, 1, hardening);
        Type::Mat3 testS = fcElastic.KirchhoffStress(projF, 1, hardening);
        if (dpYield.value(testS.diagonal()) < tol) {
            successes++;
        } else {
            std::cout << dpYield.value(testS.diagonal()) << std::endl;
        }

        // std::cerr << "Test:\n"
        //           << testF << "\n\n"
        //           << projF << "\n\n"
        //           << testS << std::endl;
        // if ((mapS.diagonal() - projS).cwiseAbs().maxCoeff() < tol) {
        //     successes++;
        // } else {
        //     std::cerr << "Unit test " << it << " failed: expected "
        //               << projS.transpose() << ". Got "
        //               << mapS.diagonal().transpose() << std::endl;
        // }
    }
    std::cout << "Unit tests: " << successes << "/" << trials << " succeeded. "
              << ((successes == trials) ? "Success!" : "Fail!") << std::endl;
}
