#pragma once

#include "RigidObjectBase.h"

namespace FrictionFrenzy {
namespace CollisionObject {
/**
 * A convex collision object. This uses GJK to detect collisions.
 * The input mesh is assumed to already be convex, and only one collision point
 * between convex objects.
 */
class Convex : public RigidObjectBase {
   public:
	Convex(size_t id,
	       CPUMeshData* p_mesh,
	       CPUMeshData* p_collMesh,
	       Affine transformation = Affine::Identity())
		: RigidObjectBase(id, p_mesh, p_collMesh, transformation) {}
	void initializeFCLObject() override;
	CollisionObject::Type getType() const override {
		return CollisionObject::Type::CONVEX;
	}
	Scalar obbMinLength() const override;
	std::string toString() const override;

	std::unique_ptr<RigidObjectBase> shallowCopy(int id) const override {
		std::unique_ptr<RigidObjectBase> ret = std::make_unique<Convex>(
			id, mp_mesh, mp_collisionMesh, getRigidTransMatrix());
		copyBaseData(ret.get());
		return ret;
	}

   protected:
	std::shared_ptr<std::vector<fcl::Vector3<Scalar>>> mp_transVertices;
	std::shared_ptr<std::vector<int>> mp_indices;
};
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
