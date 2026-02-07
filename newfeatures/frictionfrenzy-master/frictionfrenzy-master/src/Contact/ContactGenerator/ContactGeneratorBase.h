#pragma once

#include <fcl/fcl.h>
#include "../ContactInfo.h"
#include "CollisionObject/RigidObjectBase.h"

namespace FrictionFrenzy {
namespace Contact {

/**
 * @brief Given a collision point pos and normal direction n (normalized),
 * fill the local-to-global transformation and the given the two collision
 * objects.
 *
 * @param[in] pos The global collision point
 * @param[in] n   The contact normal
 * @param[in] pObj0, pObj1 Pointers to the two coliding objects
 * @param[out] out The contact information data structure to write to.
 */
inline void normalToTransform(const Vector3& pos,
                              const Vector3& n,
                              const CollisionObject::RigidObjectBase* pObj0,
                              const CollisionObject::RigidObjectBase* pObj1,
                              ContactInformation& out) {
	// Calculate the rotation axis and angle of the x-axis to the collision
	// normal.
	const Vector3 axis = Vector3(1, 0, 0).cross(n);
	const Scalar cos = Vector3(1, 0, 0).dot(n);
	const Scalar angle = std::atan2(axis.norm(), cos);

	// Convert angle-axis notation to rotation matrix.
	Matrix3 rot =
		Isometry(Eigen::AngleAxis<Scalar>(angle, axis.normalized())).rotation();

	// Fill the contact structures.
	const std::array<const CollisionObject::RigidObjectBase*, 2> objPtr = {
		pObj0, pObj1};
	for (int j = 0; j < 2; ++j) {
		Vector3 c = pos - objPtr[j]->getTranslation();
		if (j) {
			rot *= -1;
		}
		out.pos = pos;
		out.transformation[j] << rot, c.cross(rot.col(0)), c.cross(rot.col(1)),
			c.cross(rot.col(2));
	}
}

/**
 * @brief Convert an FCL contact to internal structure.
 * @param[in] contact: The FCL contact.
 * @param[in] area:    The contact area.
 * @param[in] pObj0, pObj1: The two collision objects
 */
inline ContactInformation convertContact(
	const fcl::Contact<Scalar>& contact,
	const Scalar area,
	const CollisionObject::RigidObjectBase* pObj0,
	const CollisionObject::RigidObjectBase* pObj1) {
	ContactInformation out;
	out.objId[0] = pObj0->getID();
	out.objId[1] = pObj1->getID();
	normalToTransform(contact.pos, contact.normal, pObj0, pObj1, out);
	out.localForce = Vector3::Zero();
	out.dynamicFriction = Vector2::Zero();
	out.depth = std::abs(contact.penetration_depth);
	out.area = area;
	out.isDynamic = false;
	return out;
}

/**
 * A contact generator takes in a vector of FCL contacts and convert them to
 * internal contact information.
 */
class ContactGeneratorBase {
   public:
	ContactGeneratorBase() = default;
	virtual ~ContactGeneratorBase() {}
	/**
	 * @brief Convert a vector of FCL contacts and convert them to internal
	 * contact information.
	 *
	 * @param[in] contacts: Vector of FCL contacts
	 * @param[in] pObj0, pObj1: The two collision objects
	 * @param[out] out: The vector of ContactInformation structs.
	 */
	virtual void operator()(const std::vector<fcl::Contact<Scalar>>& contacts,
	                        const CollisionObject::RigidObjectBase* pObj0,
	                        const CollisionObject::RigidObjectBase* pObj1,
	                        std::vector<ContactInformation>& out) const {
		for (size_t i = 0; i < contacts.size(); ++i) {
			out.push_back(
				Contact::convertContact(contacts[i], 1.0, pObj0, pObj1));
		}
		return;
	}
};

class SphereSphereContactGenerator : public ContactGeneratorBase {
   public:
	SphereSphereContactGenerator(){};
	void operator()(const std::vector<fcl::Contact<Scalar>>& contacts,
	                const CollisionObject::RigidObjectBase* pObj0,
	                const CollisionObject::RigidObjectBase* pObj1,
	                std::vector<ContactInformation>& out) const override;
};

class MeshMeshContactGenerator : public ContactGeneratorBase {
   public:
	void operator()(const std::vector<fcl::Contact<Scalar>>& contacts,
	                const CollisionObject::RigidObjectBase* pObj0,
	                const CollisionObject::RigidObjectBase* pObj1,
	                std::vector<ContactInformation>& out) const override;
};

typedef std::array<
	std::array<std::unique_ptr<Contact::ContactGeneratorBase>,
               static_cast<size_t>(CollisionObject::Type::N_TYPES)>,
	static_cast<size_t>(CollisionObject::Type::N_TYPES)>
	ContactMatrix;
}  // namespace Contact
}  // namespace FrictionFrenzy
