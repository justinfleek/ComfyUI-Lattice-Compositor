#pragma once

#include <vector>
#include "RigidBodyWorld.h"
namespace FrictionFrenzy {
namespace Dynamics {
class EuclideanWorld : public RigidBodyWorld {
   public:
	EuclideanWorld() {}
	RigidWorldType getType() const override {
		return RigidWorldType::EUCLIDEAN;
	}
	void updateRigidBodyPositions(
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
		Contact::BroadPhaseManager& broadPhase,
		Scalar timestep) override{};
	Affine worldTransformation() const override { return Affine::Identity(); }
	Affine worldDisplayTransformation() const override {
		return Affine::Identity();
	}
	void fillFromParams(const Params::RigidBodyWorld& params) override {}
};
}  // namespace Dynamics
}  // namespace FrictionFrenzy
