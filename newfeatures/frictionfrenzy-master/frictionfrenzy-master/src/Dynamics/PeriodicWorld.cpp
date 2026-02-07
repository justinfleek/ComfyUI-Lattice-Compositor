#include "Dynamics/PeriodicWorld.h"
namespace FrictionFrenzy {
namespace Dynamics {
void PeriodicWorld::initialize(
	std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects) {
	// m_phantomObj.reserve(objects.size());
	// for (int i = 0; i < objects.size(); ++i) {
	// 	m_phantomObj.push_back(objects[i]->shallowCopy(objects.size() + i));
	// }
}
void PeriodicWorld::updateRigidBodyPositions(
	std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
	Contact::BroadPhaseManager& broadPhase,
	Scalar timestep) {
	m_scale += m_scaleRate * timestep;
	m_shear += m_shearRate * timestep;
	m_center += m_moveRate * timestep;

	Matrix3 velGrad = velocityGrad();
	for (size_t i = 0; i < objects.size(); ++i) {
		Vector3 pos = objects[i]->getTranslation();
		Vector3 posNew = wrapPos(pos);
		if (pos != posNew) {
			objects[i]->setTranslation(posNew);
			objects[i]->velocity() += velGrad * (posNew - pos);
		}
	}
};
// Affine PeriodicWorld::worldTransformation() const {
// 	Affine scaleMat = Affine::Identity();
// 	scaleMat = scaleMat.translate(m_center) * shearMatrix();
// 	scaleMat = scaleMat.scale(m_scale);
//
// 	return scaleMat;
// }
Affine PeriodicWorld::toTransformation(
	const Eigen::Ref<const Vector3> center,
	const Eigen::Ref<const Vector3> scale,
	const Eigen::Ref<const Vector3> shear) const {
	Affine scaleMat = Affine::Identity();
	scaleMat = scaleMat.translate(center) * shearMatrix(shear);
	scaleMat = scaleMat.scale(scale);

	return scaleMat;
}
Affine PeriodicWorld::worldDisplayTransformation() const {
	Affine scaleMat = Affine::Identity();
	scaleMat = scaleMat.translate(m_center) * shearMatrix(m_shear);
	scaleMat = scaleMat.scale(m_scale / 2);

	return scaleMat;
}
// Affine PeriodicWorld::invWorldTransformation() const {
// 	Affine scaleMat = Affine::Identity();
// 	scaleMat =
// 		scaleMat.scale((1. / m_scale.array()).matrix()) * invShearMatrix();
// 	scaleMat = scaleMat.translate(-m_center);
//
// 	return scaleMat;
// }
Affine PeriodicWorld::toInvTransformation(
	const Eigen::Ref<const Vector3> center,
	const Eigen::Ref<const Vector3> scale,
	const Eigen::Ref<const Vector3> shear) const {
	Affine scaleMat = Affine::Identity();
	scaleMat =
		scaleMat.scale((1. / scale.array()).matrix()) * invShearMatrix(shear);
	scaleMat = scaleMat.translate(-center);

	return scaleMat;
}
Affine PeriodicWorld::shearMatrix(const Eigen::Ref<const Vector3> shear) const {
	Affine shearRet = Affine::Identity();
	shearRet.linear()(0, 1) = shear[0];
	shearRet.linear()(0, 2) = shear[1];
	shearRet.linear()(1, 2) = shear[2];
	return shearRet;
}
Affine PeriodicWorld::invShearMatrix(
	const Eigen::Ref<const Vector3> shear) const {
	Affine shearRet = Affine::Identity();
	shearRet.linear()(0, 1) = -shear[0];
	shearRet.linear()(0, 2) = shear[0] * shear[2] - shear[1];
	shearRet.linear()(1, 2) = -shear[2];
	return shearRet;
}
Vector3 PeriodicWorld::wrapPos(Vector3 pos, Vector3i dir) const {
	Vector3 posNew = invWorldTransformation() * pos.homogeneous();
	posNew.array() += 0.5;
	bool changed = false;
	for (int i = 0; i < 3; ++i) {
		posNew[i] -= dir[i];
		if (posNew[i] < 0 || posNew[i] >= 1) {
			posNew[i] -= floor(posNew[i]);
			changed = true;
		}
		posNew[i] += dir[i];
	}
	if (changed) {
		posNew = worldTransformation() *
		         (posNew.array() - 0.5).matrix().homogeneous();
	} else {
		posNew = pos;
	}
	return posNew;
}
bool PeriodicWorld::isInBoundary(const Eigen::Ref<const Vector3> pos) {
	Vector3 posNew = invWorldTransformation() * pos.homogeneous();
	for (int i = 0; i < 3; ++i) {
		if (posNew[i] < -0.5 || posNew[i] >= 0.5) {
			return false;
		}
	}
	return true;
}

void PeriodicWorld::detectAdditionalContacts(
	std::vector<Contact::ContactInformation>& contactInfo,
	Contact::BroadPhaseManager& broadPhase,
	std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects,
	std::unordered_map<const fcl::CollisionGeometry<Scalar>*, size_t>&
		pointerToObjectId,
	Contact::ContactMatrix& contactMatrix) {
	struct PeriodicContact {
		fcl::Contact<Scalar> contact;
		size_t id[2];
		Vector3i dir[2];
	};
	std::vector<PeriodicContact> contacts;
	m_phantomObj.clear();
	m_phantomToObjId.clear();
	// std::vector<std::vector<Vector3i>> warpDirsObj(objects.size());
	std::vector<std::unordered_map<size_t, std::vector<Vector3i>>> warpDirsObj(
		objects.size());
	for (size_t objId = 0; objId < objects.size(); ++objId) {
		RigidObjectBase* obj = objects[objId].get();
		// RigidObjectBase* perObj = m_phantomObj[objId].get();

		// perObj->setRotation(obj->getRotation());
		auto& AABB = obj->getFCLObject()->getAABB();

		Vector3 objSize(AABB.width(), AABB.height(), AABB.depth());
		Vector3 objMin = AABB.center() - objSize / 2;
		Vector3 origTrans = obj->getTranslation();

		std::array<bool, 6> warpDims = {0, 0, 0, 0, 0, 0};
		for (int j = 0; j < 8; ++j) {
			Vector3 ax(j & 1, (j >> 1) & 1, (j >> 2) & 1);
			Vector3 bbPoint = objMin + (objSize.array() * ax.array()).matrix();
			Vector3 transBBPoint =
				invWorldTransformation() * bbPoint.homogeneous();
			for (int k = 0; k < 3; ++k) {
				warpDims[k] |= transBBPoint[k] > 0.5;
				warpDims[k + 3] |= transBBPoint[k] < -0.5;
			}
		}
		for (int i = -1; i < 2; ++i) {
			bool warpX =
				(i == -1) ? warpDims[0] : ((i == 1) ? warpDims[3] : true);

			for (int j = -1; j < 2; ++j) {
				bool warpY =
					(j == -1) ? warpDims[1] : ((j == 1) ? warpDims[4] : true);
				for (int k = -1; k < 2; ++k) {
					if (!i && !j && !k) {
						continue;
					}
					bool warpZ = (k == -1) ? warpDims[2]
					                       : ((k == 1) ? warpDims[5] : true);
					bool warpCurrDir = warpX && warpY && warpZ;
					if (warpCurrDir) {
						Vector3i dir(i, j, k);
						Vector3 translation = wrapPos(origTrans, dir);

						std::unique_ptr<RigidObjectBase> perObj =
							obj->shallowCopy(m_phantomObj.size() +
						                     objects.size());
						perObj->setTranslation(translation);
						perObj->setRotation(obj->getRotation());

						fcl::DefaultCollisionData<Scalar> collisionData;
						collisionData.request.num_max_contacts = 10000;
						collisionData.request.enable_contact = true;

						broadPhase.collide(perObj->getFCLObject(),
						                   collisionData);
						std::vector<fcl::Contact<Scalar>> objContacts;
						std::vector<PeriodicContact> newContacts;
						collisionData.result.getContacts(objContacts);

						for (size_t cidx = 0; cidx < objContacts.size();
						     ++cidx) {
							auto& c = objContacts[cidx];
							// if (!isInBoundary(c.pos)) {
							// 	// continue;
							// 	c.pos = wrapPos(c.pos);
							// }
							size_t otherId = (pointerToObjectId[c.o1] != objId
							                   ? pointerToObjectId[c.o1]
							                   : pointerToObjectId[c.o2]);
							if (otherId < objId &&
							    warpDirsObj[otherId].count(objId)) {
								bool recorded = false;
								for (auto& d : warpDirsObj[otherId][objId]) {
									if (d == -dir) {
										recorded = true;
										break;
									}
								}
								if (recorded) {
									continue;
								}
							}
							newContacts.push_back(
								{c,
							     {pointerToObjectId.at(c.o1),
							      pointerToObjectId.at(c.o2)},
							     {Vector3i::Zero(), Vector3i::Zero()}});
							if (newContacts.back().id[1] == objId) {
								newContacts.back().id[1] = perObj->getID();
								newContacts.back().dir[1] = dir;
								warpDirsObj[objId][newContacts.back().id[0]]
									.push_back(dir);
							} else {
								newContacts.back().id[0] = perObj->getID();
								newContacts.back().dir[0] = dir;
								warpDirsObj[objId][newContacts.back().id[1]]
									.push_back(dir);
							}
						}

						if (!newContacts.empty()) {
							contacts.insert(contacts.end(), newContacts.begin(),
							                newContacts.end());
							m_phantomToObjId[perObj->getID()] = {obj->getID(),
							                                     dir};
							m_phantomObj.push_back(std::move(perObj));
						}
					}
				}
			}
		}
	}
	for (size_t i = 0; i < contacts.size(); ++i) {
		// Order the contacts by object ID;
		if (contacts[i].id[0] > contacts[i].id[1]) {
			std::swap(contacts[i].id[0], contacts[i].id[1]);
			std::swap(contacts[i].dir[0], contacts[i].dir[1]);
			std::swap(contacts[i].contact.o1, contacts[i].contact.o2);
			std::swap(contacts[i].contact.b1, contacts[i].contact.b2);
			contacts[i].contact.normal *= -1;
		}
	}

	// Sort the contacts lexographically by objects.
	std::sort(contacts.begin(), contacts.end(),
	          [&](const PeriodicContact& a, const PeriodicContact& b) {
				  size_t ida1 = a.id[0];
				  size_t ida2 = a.id[1];
				  size_t idb1 = b.id[0];
				  size_t idb2 = b.id[1];
				  if (ida1 != idb1) {
					  return ida1 < idb1;
				  } else if (ida2 != idb2) {
					  return ida2 < idb2;
				  } else {
					  return false;
				  }
			  });
	std::vector<size_t> breakPoints;
	breakPoints.push_back(0);
	for (size_t i = 0; i < contacts.size();) {
		size_t j = i + 1;
		for (; j < contacts.size(); ++j) {
			if (contacts[i].id[0] != contacts[j].id[0] ||
			    contacts[i].id[1] != contacts[j].id[1]) {
				break;
			}
		}
		breakPoints.push_back(j);
		i = j;
	}

	auto pairwiseObjectContacts =
		[this, &objects, &contactMatrix](
			std::vector<Contact::ContactInformation>& out,
			std::vector<PeriodicContact>& in, int begin, int end) {
			auto* oPtr =
				(in[begin].id[0] < objects.size())
					? objects[in[begin].id[0]].get()
					: m_phantomObj[in[begin].id[0] - objects.size()].get();
			auto* oPtr2 =
				(in[begin].id[1] < objects.size())
					? objects[in[begin].id[1]].get()
					: m_phantomObj[in[begin].id[1] - objects.size()].get();
			if (oPtr->isStatic() && oPtr2->isStatic()) {
				return;
			}
			if (oPtr == oPtr2) {
				return;
			}
			std::vector<fcl::Contact<Scalar>> fclContacts;
			fclContacts.reserve(end - begin);
			for (int i = begin; i < end; ++i) {
				fclContacts.push_back(in[i].contact);
			}

			// Call contact handlers to generate contacts.
			std::vector<ContactInformation> inter;
			(*contactMatrix[static_cast<size_t>(oPtr->getType())]
		                   [static_cast<size_t>(oPtr2->getType())])(
				fclContacts, oPtr, oPtr2, inter);

			if (inter.size() > 0) {
				std::sort(inter.begin(), inter.end(),
			              [&](const ContactInformation& a,
			                  const ContactInformation& b) {
							  if (a.pos[0] != b.pos[0]) {
								  return a.pos[0] < b.pos[0];
							  } else if (a.pos[1] != b.pos[1]) {
								  return a.pos[1] < b.pos[1];
							  } else if (a.pos[2] != b.pos[2]) {
								  return a.pos[2] < b.pos[2];
							  } else {
								  return false;
							  }
						  });
				// Merge contacts that are too close.
				std::vector<size_t> breakPoints;
				breakPoints.push_back(0);
				for (size_t i = 1; i < inter.size(); ++i) {
					if ((inter[i].pos - inter[i - 1].pos).squaredNorm() >
				        1e-8) {
						breakPoints.push_back(i);
					}
				}
				breakPoints.push_back(inter.size());
				for (size_t i = 0; i < breakPoints.size() - 1; ++i) {
					if (breakPoints[i + 1] - breakPoints[i] == 1) {
						out.push_back(inter[breakPoints[i]]);
					} else {
						ContactInformation temp = inter[breakPoints[i]];
						Vector3 normal = temp.normal();
						for (size_t j = breakPoints[i] + 1;
					         j < breakPoints[i + 1]; ++j) {
							normal += inter[j].normal();
							temp.area += inter[j].area;
							temp.depth = std::min(inter[j].depth, temp.depth);
						}
						normal.normalize();
						normalToTransform(temp.pos, normal, oPtr, oPtr2, temp);
						out.push_back(temp);
					}
				}
			}
		};
	std::vector<ContactInformation> newContacts;
	for (size_t i = 0; i < breakPoints.size() - 1; ++i) {
		pairwiseObjectContacts(newContacts, contacts, breakPoints[i],
		                       breakPoints[i + 1]);
	}
	for (size_t i = 0; i < newContacts.size(); ++i) {
		for (int j = 0; j < 2; ++j) {
			size_t id = newContacts[i].objId[j];
			if (id >= objects.size()) {
				newContacts[i].objId[j] = m_phantomToObjId[id].first;
			}
		}
		newContacts[i].isBoundary = true;
	}
	contactInfo.insert(contactInfo.end(), newContacts.begin(),
	                   newContacts.end());
}
Matrix3 PeriodicWorld::velocityGrad() const {
	// Matrix3 trans = (Matrix3() << 1, m_shearRate[0], m_shearRate[1], 0, 1,
	//                  m_shearRate[2], 0, 0, 1)
	//                     .finished();
	// trans = trans * (Matrix3() << m_scaleRate[0], 0, 0, 0, m_scaleRate[1], 0,
	// 0,
	//                  0, m_scaleRate[2])
	//                     .finished();
	return toTransformation(m_moveRate, m_scaleRate, m_shearRate).linear() *
	       invWorldTransformation().linear();
}
void PeriodicWorld::updateDeformation(
	const Vector3& newPos,
	const Vector3& newScale,
	const Vector3& newShear,
	std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects) {
	Affine invOldTrans = invWorldTransformation();
	m_center = newPos;
	m_scale = newScale;
	m_shear = newShear;
	Affine newTrans = worldTransformation() * invOldTrans;

#pragma omp parallel for
	for (size_t i = 0; i < objects.size(); ++i) {
		Vector3 oldP = objects[i]->getTranslation();
		objects[i]->setTranslation(newTrans * oldP);
	}
}
void PeriodicWorld::fillVelocityCorrection(
	std::vector<Contact::ContactInformation>& contactInfo,
	std::vector<std::unique_ptr<CollisionObject::RigidObjectBase>>& objects)
	const {
	Matrix3 velGrad = velocityGrad();
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		contactInfo[i].velocityCorrection.setZero();
		for (int j = 0; j < 2; ++j) {
			auto& obj = *(objects[contactInfo[i].objId[j]]);
			Vector3 realPos = obj.getTranslation();
			Vector3 virtualPos =
				contactInfo[i].pos - contactInfo[i].displacement(j);
			Vector6 globalVelCorrection;
			globalVelCorrection << velGrad * (virtualPos - realPos),
				Vector3::Zero();
			contactInfo[i].velocityCorrection +=
				contactInfo[i].toLocal(j, globalVelCorrection);
		}
	}
}
}  // namespace Dynamics
}  // namespace FrictionFrenzy
