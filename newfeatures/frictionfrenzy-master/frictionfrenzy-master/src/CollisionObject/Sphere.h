#pragma once
#include "RigidObjectBase.h"
namespace FrictionFrenzy {
namespace CollisionObject {

// A sphere collision object.
class Sphere : public RigidObjectBase {
   public:
	Sphere(size_t id,
	       CPUMeshData* p_mesh,
	       CPUMeshData* p_collMesh,
	       Affine transformation = Affine::Identity())
		: RigidObjectBase(id, p_mesh, p_collMesh, transformation) {}
	void initializeFCLObject() override;
	CollisionObject::Type getType() const override {
		return CollisionObject::Type::SPHERE;
	}
	Scalar obbMinLength() const override;
	std::string toString() const override;
	Scalar radius() const { return m_radius; }
	void setRadius(Scalar radius) { m_radius = radius; }

	std::unique_ptr<RigidObjectBase> shallowCopy(int id) const override {
		std::unique_ptr<RigidObjectBase> ret = std::make_unique<Sphere>(
			id, mp_mesh, mp_collisionMesh, getRigidTransMatrix());
		copyBaseData(ret.get());
		dynamic_cast<Sphere*>(ret.get())->setRadius(m_radius);
		return ret;
	}

   protected:
	Scalar m_radius;
};
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
