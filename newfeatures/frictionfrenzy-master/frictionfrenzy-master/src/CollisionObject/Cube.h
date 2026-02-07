#pragma once
#include "RigidObjectBase.h"

namespace FrictionFrenzy {
namespace CollisionObject {
/**
 * Box object that computes collisions with FCL's box-box intersection
 */
class Cube : public RigidObjectBase {
   public:
	Cube(size_t id,
	     CPUMeshData* p_mesh,
	     CPUMeshData* p_collMesh,
	     Affine transformation = Affine::Identity())
		: RigidObjectBase(id, p_mesh, p_collMesh, transformation) {}
	void initializeFCLObject() override;
	CollisionObject::Type getType() const override {
		return CollisionObject::Type::CUBE;
	}
	std::unique_ptr<RigidObjectBase> shallowCopy(int id) const override {
		std::unique_ptr<RigidObjectBase> ret = std::make_unique<Cube>(
			id, mp_mesh, mp_collisionMesh, getRigidTransMatrix());
		auto retMesh = dynamic_cast<Cube*>(ret.get());
		retMesh->getSideVector() = m_sides;
		copyBaseData(ret.get());
		return ret;
	}
	Scalar obbMinLength() const override;
	std::string toString() const override;

	Vector3& getSideVector() { return m_sides; }

   protected:
	Vector3 m_sides;
};
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
