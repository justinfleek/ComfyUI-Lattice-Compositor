#pragma once

#include <memory>
#include <utility>
#include <vector>
#include "CollisionObject/RigidObjectBase.h"
#include "Common/MatrixTypes.h"
#include "Contact/BroadPhase.h"
#include "Contact/ContactInfo.h"
#include "Dynamics/DynamicSystem.h"
#include "RigidBodyWorld.h"
#include "fcl/geometry/collision_geometry.h"
#include "fcl/narrowphase/collision_object.h"
#include "fcl/narrowphase/contact.h"
namespace FrictionFrenzy {
namespace Params {
struct PeriodicWorld : public RigidBodyWorld {
	Vector3 center;
	Vector3 scale;
};
}  // namespace Params
namespace Dynamics {
class PeriodicWorld : public RigidBodyWorld {
   public:
	PeriodicWorld() {}
	RigidWorldType getType() const override { return RigidWorldType::PERIODIC; }
	void initialize(
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects)
		override;
	void updateRigidBodyPositions(
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
		Contact::BroadPhaseManager& broadPhase,
		Scalar timestep) override;
	Affine worldTransformation() const override {
		return toTransformation(m_center, m_scale, m_shear);
	}
	Affine worldDisplayTransformation() const override;
	void reset() override {
		m_center = m_centerOrig;
		m_scale = m_scaleOrig;
		m_shear = m_shearOrig;
	}
	Affine invWorldTransformation() const {
		return toInvTransformation(m_center, m_scale, m_shear);
	}
	Affine toTransformation(const Eigen::Ref<const Vector3> center,
	                        const Eigen::Ref<const Vector3> scale,
	                        const Eigen::Ref<const Vector3> shear) const;
	Affine toInvTransformation(const Eigen::Ref<const Vector3> center,
	                           const Eigen::Ref<const Vector3> scale,
	                           const Eigen::Ref<const Vector3> shear) const;
	Affine shearMatrix() const { return shearMatrix(m_shear); }
	Affine shearMatrix(const Eigen::Ref<const Vector3> shear) const;
	Affine invShearMatrix() const { return invShearMatrix(m_shear); }
	Affine invShearMatrix(const Eigen::Ref<const Vector3> shear) const;
	Vector3 wrapPos(Vector3 pos, Vector3i dir = Vector3i(0, 0, 0)) const;
	bool isInBoundary(const Eigen::Ref<const Vector3> pos);
	Vector3& getScale() { return m_scale; }
	Vector3& getShear() { return m_shear; }
	Vector3& getCenter() { return m_center; }
	void fillFromParams(const Params::RigidBodyWorld& params) override {
		const Params::PeriodicWorld* paramsCast =
			static_cast<const Params::PeriodicWorld*>(&params);
		m_center = paramsCast->center;
		m_scale = paramsCast->scale;
		m_centerOrig = m_center;
		m_scaleOrig = m_scale;
		m_shearOrig = m_shear;
	}
	bool& showPeriodic() { return m_showPeriodic; }

	void updateDeformation(
		const Vector3& newPos,
		const Vector3& newScale,
		const Vector3& newShear,
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>&
			objects);

	void assignDeformRate(const Eigen::Ref<const Vector3> center,
	                      const Eigen::Ref<const Vector3> scale,
	                      const Eigen::Ref<const Vector3> shear) {
		m_moveRate = center;
		m_scaleRate = scale;
		m_shearRate = shear;
	}

	void detectAdditionalContacts(
		std::vector<Contact::ContactInformation>& contactInfo,
		Contact::BroadPhaseManager& broadPhase,
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
		std::unordered_map<const fcl::CollisionGeometry<Scalar>*, size_t>&
			pointerToObjectId,
		Contact::ContactMatrix& contactMatrix) override;

	void fillVelocityCorrection(
		std::vector<Contact::ContactInformation>& contactInfo,
		std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects)
		const override;

	Matrix3 velocityGrad() const;

   protected:
	Vector3 m_center = Vector3::Zero();
	Vector3 m_scale = Vector3(1, 1, 1);
	Vector3 m_shear = Vector3::Zero();
	Vector3 m_centerOrig = Vector3::Zero();
	Vector3 m_scaleOrig = Vector3(1, 1, 1);
	Vector3 m_shearOrig = Vector3::Zero();
	Vector3 m_scaleRate = Vector3::Zero();
	Vector3 m_shearRate = Vector3::Zero();
	Vector3 m_moveRate = Vector3::Zero();

	bool m_showPeriodic = false;
	std::vector<std::unique_ptr<RigidObjectBase>> m_phantomObj;
	std::unordered_map<size_t, std::pair<size_t, Vector3i>> m_phantomToObjId;
};
}  // namespace Dynamics
}  // namespace FrictionFrenzy
