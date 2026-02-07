#include <iostream>
#include <random>

#include "Solver/PrimalDual/NonSmoothForces/ForceConstraint/ForceConstraint.h"
int main() {
	using namespace FrictionFrenzy;
	std::shared_ptr<Scalar> f = std::make_shared<Scalar>(1);
	Solver::PerturbedSecondOrderCone cone(f);
	std::random_device rd;   // a seed source for the random number engine
	std::mt19937 gen(rd());  // mersed sonne_twister_engine seeded with rd()
	std::uniform_real_distribution<> dis(0.01, 1.0);

	int totalGradTestNo = 1000;
	int gradTestPassed = 0;
	int hessTestPassed = 0;
	for (int testNo = 0; testNo < totalGradTestNo; ++testNo) {
		*cone.mp_frictionCoeff = dis(gen);
		Vector3 vec = Vector3::Random();
		if (vec[0] < 0) {
			vec[0] = -vec[0];
		}
		Scalar c = cone.constraint(vec);
		Scalar eps = 1e-6;
		Vector3 analyticalG = cone.gradient(vec);
		Vector3 finiteDiffG = Vector3::Zero();
		for (int i = 0; i < 3; ++i) {
			Vector3 vecP = vec;
			Vector3 vecN = vec;
			vecP[i] += eps;
			vecN[i] -= eps;
			finiteDiffG[i] =
				(cone.constraint(vecP) - cone.constraint(vecN)) / (2 * eps);
		}
		if ((analyticalG - finiteDiffG).norm() < 1e-7) {
			gradTestPassed++;
		} else {
			std::cout << "Gradient Fail: " << analyticalG.transpose() << " "
					  << finiteDiffG.transpose() << std::endl;
		}

		Matrix3 analyticalH = cone.hessian(vec);
		Matrix3 finiteDiffH = Matrix3::Zero();
		for (int i = 0; i < 3; ++i) {
			Vector3 vecP = vec;
			Vector3 vecN = vec;
			vecP[i] += eps;
			vecN[i] -= eps;
			Vector3 gradDiff =
				(cone.gradient(vecP) - cone.gradient(vecN)) / (2 * eps);
			finiteDiffH.col(i) << gradDiff;
		}
		// std::cout << "Hessian:\n"
		//           << analyticalH << "\n"
		//           << finiteDiffH << std::endl;
		if ((analyticalH - finiteDiffH).norm() < 1e-7) {
			hessTestPassed++;
		}
	}
	std::cout << "Gradient test: " << gradTestPassed << "/" << totalGradTestNo
			  << " passed." << std::endl;
	std::cout << "Hessian test: " << hessTestPassed << "/" << totalGradTestNo
			  << " passed." << std::endl;
	int totalLineSearchTest = 1000;
	// int lineTestPassed = 0;
	// for (int testNo = 0; testNo < totalLineSearchTest; ++testNo) {
	// 	std::uniform_real_distribution<> normDis(0, 10.0);
	// 	std::uniform_real_distribution<> angDis(0, 2 * M_PI);
	// 	*cone.mp_frictionCoeff = dis(gen);
	// 	Vector3 vec;
	// 	vec[0] = normDis(gen);
	// 	std::uniform_real_distribution<> magDis(
	// 		0, *cone.mp_frictionCoeff * vec[0]);
	// 	FloatType m = magDis(gen), ang = angDis(gen);
	// 	vec[1] = m * std::cos(ang);
	// 	vec[2] = m * std::sin(ang);
	// 	Vector3 step = Vector3::Random();
	// 	FloatType a = cone.maxStepSize(vec, step);
	// 	FloatType c = cone.constraint(vec + a * step);
	//
	// 	if (c < 1e-7) {
	// 		lineTestPassed++;
	// 	}
	// }
	// std::cout << "Line test: " << lineTestPassed << "/" << totalLineSearchTest
	// 		  << " passed." << std::endl;
	int projectionTestPassed = 0;
	for (int testNo = 0; testNo < totalLineSearchTest; ++testNo) {
		std::uniform_real_distribution<> normDis(1e1, 0);
		std::uniform_real_distribution<> angDis(0, 2 * M_PI);
		std::uniform_real_distribution<> targetDis(-1e-2, 1e-2);
		*cone.mp_frictionCoeff = dis(gen);
		Vector3 vec;
		Scalar target = 0;  // targetDis(gen);
		vec[0] = normDis(gen);
		std::uniform_real_distribution<> magDis(
			*cone.mp_frictionCoeff * vec[0],
			2 * *cone.mp_frictionCoeff * vec[0]);
		// std::uniform_real_distribution<> magDis(0,
		//                                         cone.m_frictionCoeff *
		//                                         vec[0]);
		// std::uniform_real_distribution<> magDis(0, 1e-3);
		Scalar m = magDis(gen), ang = angDis(gen);
		vec[1] = m * std::cos(ang);
		vec[2] = m * std::sin(ang);
		Vector3 proj = cone.project(vec, vec, target);
		Scalar c = cone.constraint(proj) - target;
		Vector3 grad = cone.gradient(proj);

		if (std::abs(c) < 1e-7 &&
		    grad.normalized().cross((proj - vec).normalized()).norm() < 1e-7) {
			projectionTestPassed++;
		} else {
			std::cout << "FAIL: " << c << vec.transpose() << " "
					  << proj.transpose() << std::endl;
			std::cout
				<< grad.normalized().cross((proj - vec).normalized()).norm()
				<< std::endl;
		}
	}
	std::cout << "Projection test: " << projectionTestPassed << "/"
			  << totalLineSearchTest << " passed." << std::endl;
}
