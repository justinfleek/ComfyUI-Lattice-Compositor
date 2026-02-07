#pragma once

#include <vector>
#include "CollisionObject/CollisionObject.h"
#include "CollisionObject/RigidObjectBase.h"
#include "Contact/BroadPhase.h"
#include "Contact/ContactGenerator/ContactGeneratorBase.h"
#include "Contact/ContactInfo.h"
namespace FrictionFrenzy {
namespace Params {
	struct RigidBodyWorld {};
}

namespace Dynamics {
enum class RigidWorldType { NONE, EUCLIDEAN, PERIODIC };
class RigidBodyWorld {
   public:
	RigidBodyWorld() {}
	virtual ~RigidBodyWorld() {}
	virtual void fillFromParams(const Params::RigidBodyWorld &params) = 0;
	virtual RigidWorldType getType() const { return RigidWorldType::NONE; }
	virtual void initialize(
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>&
			objects) {}
	virtual void updateRigidBodyPositions(
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
		Contact::BroadPhaseManager& broadPhase,
		Scalar timestep) = 0;
	virtual void detectAdditionalContacts(
		std::vector<Contact::ContactInformation>& contactInfo,
		Contact::BroadPhaseManager& broadPhase,
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
		std::unordered_map<const fcl::CollisionGeometry<Scalar>*, size_t>&
			pointerToObjectId,
		Contact::ContactMatrix& contactMatrix) {}
	virtual void fillVelocityCorrection(
		std::vector<Contact::ContactInformation>& contactInfo,
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects)
		const {
#pragma omp parallel for
		for (size_t i = 0; i < contactInfo.size(); ++i) {
			contactInfo[i].velocityCorrection.setZero();
		}
	}
	virtual Affine worldTransformation() const = 0;
	virtual Affine worldDisplayTransformation() const = 0;
	virtual void reset() {}
};
}  // namespace Dynamics
}  // namespace FrictionFrenzy
