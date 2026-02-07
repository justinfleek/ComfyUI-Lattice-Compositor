#include <iostream>
#include <random>
#include "Common/CustomTypes.hpp"
#include "Physics/Elasticity/FixedCorotated.hpp"
#include "Physics/Hardening/HardeningBase.hpp"
#include "Physics/Plasticity/DruckerPragerYield.hpp"

int main() {
    MPM::Elastic::FixedCorotated fcElastic(5e5, 0.4);
    MPM::Hardening::NoHardening hardening;
    MPM::Plastic::DruckerPragerYield dpYield(0.4);

    std::mt19937 gen(1024);
    std::normal_distribution<Type::NumT> dist(-0.1, 0.2);

    int successes = 0;
    const int trials = 1000;
    const Type::NumT tol = 1e-8;
    for (int it = 0; it < trials; ++it) {
        Type::Vec3 testF = Type::Vec3::Ones();
        testF[0] += dist(gen);
        testF[1] += dist(gen);
        testF[2] += dist(gen);
        Type::Mat3 projF =
            fcElastic.returnMapping(testF.asDiagonal(), dpYield, 1, hardening);
        Type::Mat3 testS =
            fcElastic.KirchhoffStress(testF.asDiagonal(), 1, hardening);
        Type::Vec3 projS = dpYield.projectStress(testS.diagonal());

        Type::Mat3 mapS = fcElastic.KirchhoffStress(projF, 1, hardening);

        if ((mapS.diagonal() - projS).cwiseAbs().maxCoeff() < tol) {
            successes++;
        } else {
            std::cerr << "Unit test " << it << " failed: expected "
                      << projS.transpose() << ". Got "
                      << mapS.diagonal().transpose() << std::endl;
        }
    }
    std::cout << "Unit tests: " << successes << "/" << trials << " succeeded. "
              << ((successes == trials) ? "Success!" : "Fail!") << std::endl;
}
