#pragma once
#include "RigidObjectBase.h"

namespace FrictionFrenzy {
namespace CollisionObject {
// An ellipsoid collision object.
class Ellipsoid : public RigidObjectBase {
   public:
	Ellipsoid(size_t id,
	          CPUMeshData* p_mesh,
	          CPUMeshData* p_collMesh,
	          Affine transformation = Affine::Identity())
		: RigidObjectBase(id, p_mesh, p_collMesh, transformation) {}
	void initializeFCLObject() override;
	CollisionObject::Type getType() const override {
		return CollisionObject::Type::ELLIPSOID;
	}
	Scalar obbMinLength() const override;
	std::string toString() const override;
	std::unique_ptr<RigidObjectBase> shallowCopy(int id) const override {
		std::unique_ptr<RigidObjectBase> ret = std::make_unique<Ellipsoid>(
			id, mp_mesh, mp_collisionMesh, getRigidTransMatrix());
		copyBaseData(ret.get());
		return ret;
	}

   protected:
	Vector3 m_dimensions;
};
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
