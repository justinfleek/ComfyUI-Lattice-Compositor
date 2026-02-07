#include "BroadPhase.h"
#include "fcl/narrowphase/collision_object.h"
namespace FrictionFrenzy {
namespace Contact {
BroadPhaseManager::BroadPhaseManager() {
	mp_fclManager =
		std::make_unique<fcl::DynamicAABBTreeCollisionManager<Scalar>>();
}
void BroadPhaseManager::collide(fcl::DefaultCollisionData<Scalar>& cData) {
	mp_fclManager->collide(&cData, fcl::DefaultCollisionFunction);
}
void BroadPhaseManager::collide(fcl::CollisionObject<Scalar>* pObj,
                                fcl::DefaultCollisionData<Scalar>& cData) {
	mp_fclManager->collide(pObj, &cData, fcl::DefaultCollisionFunction);
}
void BroadPhaseManager::registerObjects(
	std::vector<fcl::CollisionObject<Scalar>*>& m_fclObjectPointers) {
	mp_fclManager->clear();
	mp_fclManager->registerObjects(m_fclObjectPointers);
	mp_fclManager->setup();
}
void BroadPhaseManager::update(fcl::CollisionObject<Scalar>* pobj) {
	mp_fclManager->update(pobj);
}
void BroadPhaseManager::update() {
	mp_fclManager->update();
}
}  // namespace Contact
}  // namespace FrictionFrenzy
