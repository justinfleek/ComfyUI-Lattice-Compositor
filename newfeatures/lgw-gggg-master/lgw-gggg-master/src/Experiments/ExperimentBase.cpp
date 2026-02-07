#include "ExperimentBase.h"
namespace Homogenization {
namespace Experiments {
namespace ff = FrictionFrenzy;
ff::Matrix3 homogenizedStress(ff::Dynamics::DynamicSystem& dynamics) {
	ff::Matrix3 stress;
	auto periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());
	stress.setZero();
	auto& contacts = dynamics.contactInfo();
	for (int i = 0; i < contacts.size(); ++i) {
		const auto& c = contacts[i];
		for (int j = 0; j < 2; ++j) {
			auto T = c.getTrans(j);
			ff::Vector6 force = T * c.localForce;
			auto& obj = dynamics.getObject(c.objId[j]);
			if (c.isBoundary) {
				FrictionFrenzy::Matrix3 crossMat =
					T.block<3, 3>(3, 0) * T.block<3, 3>(0, 0).transpose();
				FrictionFrenzy::Vector3 disp(
					0.5 * crossMat(2, 1) - 0.5 * crossMat(1, 2),
					0.5 * crossMat(0, 2) - 0.5 * crossMat(2, 0),
					0.5 * crossMat(1, 0) - 0.5 * crossMat(0, 1));
				FrictionFrenzy::Vector3 pos = obj.getTranslation() + disp;
				stress += force.head<3>() * pos.transpose();
			}

			ff::Matrix3 invI = obj.invInertiaTensor();
			ff::Matrix3 Iold = obj.inertiaTensor();
			ff::Vector3 angAcc = invI * force.tail<3>();
			ff::Matrix3 angAccCross;
			angAccCross << 0, -angAcc(2), angAcc(1), angAcc(2), 0, -angAcc(0),
				-angAcc(1), angAcc(0), 0;
			stress -= force.head<3>() * obj.getTranslation().transpose();
			stress -= angAccCross * (obj.density() * obj.squaredDist() *
			                             ff::Matrix3::Identity() -
			                         Iold);
		}
	}
	stress /= periodic->getScale().prod();
	return stress;
}

void assignDeformRate(FrictionFrenzy::Dynamics::DynamicSystem& dynamics,
                      const FrictionFrenzy::Vector3& tRate,
                      const FrictionFrenzy::Vector3& scaleRate,
                      const FrictionFrenzy::Vector3& shearRate) {
	auto periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());

	// Assign deformation rate to periodic world
	periodic->assignDeformRate(tRate, scaleRate, shearRate);


	// Apply linear velocity gradient to each object such that the 
	ff::Matrix3 lhs = ff::Matrix3::Zero();
	ff::Matrix3 rhs = ff::Matrix3::Zero();

	ff::Matrix3 velGrad = periodic->velocityGrad();

	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);
		ff::Vector3 x = obj.getTranslation();
		ff::Vector3 v = obj.velocity();
		ff::Scalar m = obj.mass();
		lhs += m * x * x.transpose();
		rhs += m * x * (velGrad * x - v).transpose();
	}
	ff::Matrix3 K = (lhs.inverse() * rhs).transpose();
	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);
		obj.velocity() += K * obj.getTranslation();
	}
}
}  // namespace Experiments
}  // namespace Homogenization
