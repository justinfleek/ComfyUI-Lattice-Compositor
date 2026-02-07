#include <iostream>
#include <random>
#include "Common/CustomTypes.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/MohrCoulombYield.hpp"

int main() {
    MPM::Elastic::FixedCorotated fcElastic(5e5, 0.4);
    MPM::Hardening::NoHardening hardening;
    MPM::Plastic::MohrCoulombYield dpYield(1.2);

    std::mt19937 gen(1024);
    std::normal_distribution<Type::NumT> dist(-1e-1, 1e-1);

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

        if (testF.prod() >= 1) {
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
        if (dpYield.value(fcElastic.KirchhoffStress(testF.asDiagonal(), 1,
                                                    hardening).diagonal()) < 0) {
            it--;
            continue;
        }

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
