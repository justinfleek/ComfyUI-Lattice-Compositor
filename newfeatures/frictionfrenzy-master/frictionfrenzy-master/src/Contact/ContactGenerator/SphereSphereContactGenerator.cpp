#include <stdexcept>
#include "CollisionObject/Sphere.h"
#include "ContactGeneratorBase.h"
namespace FrictionFrenzy {
namespace Contact {
void SphereSphereContactGenerator::operator()(
	const std::vector<fcl::Contact<Scalar>>& contacts,
	const CollisionObject::RigidObjectBase* pObj0,
	const CollisionObject::RigidObjectBase* pObj1,
	std::vector<ContactInformation>& out) const {
	const CollisionObject::Sphere* pSphere0 =
		dynamic_cast<const CollisionObject::Sphere*>(pObj0);
	const CollisionObject::Sphere* pSphere1 =
		dynamic_cast<const CollisionObject::Sphere*>(pObj1);
	if (!pSphere0 || !pSphere1) {
		throw std::runtime_error("Cannot convert rigid body to spheres!");
	}
	Scalar r0 = pSphere0->radius();
	Scalar r1 = pSphere1->radius();
	Scalar d = (pSphere0->getTranslation() - pSphere1->getTranslation()).norm();
	Scalar cosT = (r0 * r0 + d * d - r1 * r1) / (2 * r0 * d);
	Scalar contactRadius = r0 * std::sqrt(1 - cosT * cosT);
	Scalar area = contactRadius * contactRadius * M_PI;
	if (area != area) {
		std::cout << r0 << " " << r1 << " " << d << " " << cosT << " "
				  << contactRadius << std::endl;
		throw std::runtime_error("Area is wrong");
	}
	for (size_t i = 0; i < contacts.size(); ++i) {
		out.push_back(Contact::convertContact(contacts[i], area, pObj0, pObj1));
	}
	return;
}
}  // namespace Contact
}  // namespace FrictionFrenzy
