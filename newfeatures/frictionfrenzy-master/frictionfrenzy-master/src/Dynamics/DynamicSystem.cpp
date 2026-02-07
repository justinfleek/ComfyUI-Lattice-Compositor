#include "DynamicSystem.h"
#include "CollisionObject/RigidObjectBase.h"
#include "Common/Cores.h"
#include "Common/LoggingOptions.h"
#include "Common/MatrixTypes.h"
#include "Contact/ContactGenerator/ContactGeneratorBase.h"
#include "Dynamics/EuclideanWorld.h"
#include "Dynamics/PeriodicWorld.h"
#include "Solver/Solver.h"

#include <omp.h>
#include <cmath>
#include <limits>
#include <memory>
#include <thread>

namespace FrictionFrenzy {
namespace Dynamics {
using CollisionObject::RigidObjectBase;
DynamicSystem::DynamicSystem(std::shared_ptr<unsigned int> logging)
	: mp_logging(logging) {
	const size_t n_types = static_cast<size_t>(CollisionObject::Type::N_TYPES);
	for (size_t i = 0; i < n_types; ++i) {
		for (size_t j = 0; j < n_types; ++j) {
			if (i == static_cast<size_t>(CollisionObject::Type::MESH) &&
			    j == static_cast<size_t>(CollisionObject::Type::MESH)) {
				m_contactGeneratorMatrix[i][j] =
					std::make_unique<Contact::MeshMeshContactGenerator>();
			} else if (i ==
			               static_cast<size_t>(CollisionObject::Type::SPHERE) &&
			           j ==
			               static_cast<size_t>(CollisionObject::Type::SPHERE)) {
				m_contactGeneratorMatrix[i][j] =
					std::make_unique<Contact::SphereSphereContactGenerator>();
			} else {
				m_contactGeneratorMatrix[i][j] =
					std::make_unique<Contact::ContactGeneratorBase>();
			}
		}
	}
}
void DynamicSystem::addObject(std::unique_ptr<RigidObjectBase> p_object) {
	m_objects.push_back(std::move(p_object));
}
void DynamicSystem::clear() {
	m_contactInfo.clear();
	m_pointerToObjectId.clear();
	m_fclObjectPointers.clear();
	m_objects.clear();
	m_meshData.clear();
	m_totalTime = 0;
	m_time = 0;
}
void DynamicSystem::initialize() {
	m_fclObjectPointers.clear();
	m_pointerToObjectId.clear();
	m_minObjLength = INFINITY;
	m_fclObjectPointers.resize(m_objects.size());
// #pragma omp parallel for default(shared) reduction(min : m_minObjLength)
	for (size_t i = 0; i < m_objects.size(); ++i) {
		m_objects[i]->initializeFCLObject();
		m_fclObjectPointers[i] = m_objects[i]->getFCLObject();
		m_minObjLength = std::min(m_minObjLength, m_objects[i]->obbMinLength());
	}
	for (size_t i = 0; i < m_objects.size(); ++i) {
		const fcl::CollisionGeometry<Scalar>* geo =
			m_objects[i]->getFCLObject()->collisionGeometry().get();
		m_pointerToObjectId[geo] = i;
	}

	m_broadPhase.registerObjects(m_fclObjectPointers);
	if (!mp_rigidWorld) {
		mp_rigidWorld = std::make_unique<EuclideanWorld>();
	}
	mp_rigidWorld->initialize(m_objects);
}

void DynamicSystem::updateFCLObject(size_t id) {
	RigidObjectBase& obj = *m_objects[id];
	m_broadPhase.update(obj.getFCLObject());
}
void DynamicSystem::updateAllFCLObjects() {
	m_broadPhase.update();
}
// void DynamicSystem::saveAllStates() {
// 	for (size_t i = 0; i < m_objects.size(); ++i) {
// 		RigidObjectBase& obj = *m_objects[i];
// 		obj.saveState(m_time);
// 	}
// }
// void DynamicSystem::clearSavedStates() {
// 	for (size_t i = 0; i < m_objects.size(); ++i) {
// 		RigidObjectBase& obj = *m_objects[i];
// 		obj.clearSavedStates();
// 	}
// }
std::tuple<Vector3, Scalar> DynamicSystem::getApproxBoundingSphere() {
	Vector3 minExt, maxExt;
	minExt.setConstant(std::numeric_limits<Scalar>::infinity());
	maxExt.setConstant(-std::numeric_limits<Scalar>::infinity());

	// Calculate the AABB of the current scene.
	for (size_t i = 0; i < m_fclObjectPointers.size(); ++i) {
		if (m_objects[i]->isActive()) {
			const fcl::AABB<Scalar>& aabb = m_fclObjectPointers[i]->getAABB();
			Vector3 c = aabb.center();
			Vector3 dims(aabb.width(), aabb.height(), aabb.depth());
			minExt = minExt.cwiseMin(c - 0.5 * dims);
			maxExt = maxExt.cwiseMax(c + 0.5 * dims);
		}
	}
	Vector3 center = 0.5 * (minExt + maxExt);
	// Set radius to AABB diagonal.
	Scalar radius = 0.5 * (maxExt - minExt).norm();
	return {center, radius};
}
void DynamicSystem::contactDetection() {
	std::vector<fcl::Contact<Scalar>> contactsRaw;

	m_contactDetectionTimer.Resume();
	generateFCLContacts(contactsRaw);
	m_totalContactsBeforeMerge += contactsRaw.size();
	m_contactMergeTimer.Resume();
	generateContacts(m_contactInfo, contactsRaw);
	mp_rigidWorld->detectAdditionalContacts(m_contactInfo, m_broadPhase,
	                                        m_objects, m_pointerToObjectId,
	                                        m_contactGeneratorMatrix);
	mp_rigidWorld->fillVelocityCorrection(m_contactInfo, m_objects);

	m_contactMergeTimer.Pause();
	m_contactDetectionTimer.Pause();

	m_totalContacts += m_contactInfo.size();

	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_CONTACTS)) {
		std::cout << "Solving " << m_contactInfo.size() << " contacts."
				  << std::endl;
	}
}
void DynamicSystem::fillForces(Scalar timestep) {
	contactDetection();
	applyExternalForces(timestep);

	mp_forceSolver->fillForces(timestep, m_gravity, m_contactInfo, m_objects);
#pragma omp parallel for
	for (size_t i = 0; i < m_objects.size(); ++i) {
		auto& obj = m_objects[i];
		obj->angularAcc() /= timestep;
		obj->acceleration() /= timestep;
	}

	if (!m_contactInfo.empty()) {
		m_totalContactSubsteps++;
	}
}
void DynamicSystem::applyExternalForces(Scalar timestep) {
#pragma omp parallel for
	for (size_t i = 0; i < m_objects.size(); ++i) {
		auto& obj = m_objects[i];
		// Initialize the object forces with gravity
		obj->angularAcc().setZero();
		if (obj->isActive()) {
			obj->acceleration() = m_gravity * timestep;
			// Add Coriolis forces
			Matrix3 rotMatT = obj->getRotation().toRotationMatrix().transpose();
			Vector3 angVelBody = rotMatT * obj->angularVel();
			Vector3 inerAngVel = obj->angularVel();
			if (angVelBody.norm()) {
				Vector3 angMomentumBody = obj->inertiaTensor0() * angVelBody;
				Vector3 angMomChange = angMomentumBody.cross(angVelBody);
				Vector3 midpoint =
					0.5 * timestep * angMomChange + angMomentumBody;
				angMomChange =
					midpoint.cross(obj->invInertiaTensor0() * midpoint);
				Vector3 newAngMom = timestep * angMomChange + angMomentumBody;
				if (!newAngMom.isZero()) {
					newAngMom *=
						angMomentumBody.dot(obj->invInertiaTensor0() *
					                        angMomentumBody) /
						newAngMom.dot(obj->invInertiaTensor0() * newAngMom);
				}
				inerAngVel =
					rotMatT.transpose() * obj->invInertiaTensor0() * newAngMom;
			}
			obj->angularAcc() = inerAngVel - obj->angularVel();
		}
	}
}
void DynamicSystem::updateAllObjects(Scalar dt) {
#pragma omp parallel for
	for (size_t i = 0; i < m_objects.size(); ++i) {
		auto* obj = m_objects[i].get();
		if (obj->isActive()) {
			obj->angularVel() += obj->angularAcc() * dt;
			obj->velocity() += obj->acceleration() * dt;
		}
		Vector3 rotInc3D(obj->angularVel() * dt + obj->oriCorrect());
		Vector3 pos = obj->getTranslation();
		Quaternion rot = obj->getRotation();
		// Matrix3 inerTensOld = obj->inertiaTensor();
		Quaternion rotInc =
			rotInc3D.squaredNorm() > 0
				? Quaternion(AngleAxis(rotInc3D.norm(), rotInc3D.normalized()))
				: Quaternion(AngleAxis(0, Vector3(1, 0, 0)));
		Vector3 posInc = obj->velocity() * dt + obj->posCorrect();
		pos += posInc;
		rot = rotInc * rot;
		obj->setConfiguration(pos, rot);
	}
	mp_rigidWorld->updateRigidBodyPositions(m_objects, m_broadPhase, dt);
	updateAllFCLObjects();
	m_totalSubsteps++;
	m_time += dt;
}
void DynamicSystem::step() {
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_TIME)) {
		std::cout << "Current time: " << m_time << std::endl;
	}
	Scalar timestep = m_timestep / m_substeps;

	// Helper function to update the velocity and positions of all objects.
	// 	auto updateObjects = [&](Scalar dt) {
	// #pragma omp parallel for
	// 		for (size_t i = 0; i < m_objects.size(); ++i) {
	// 			auto* obj = m_objects[i].get();
	// 			if (obj->isActive()) {
	// 				obj->angularVel() += obj->angularAcc();
	// 				obj->velocity() += obj->acceleration();
	// 			}
	// 			Vector3 rotInc3D(obj->angularVel() * dt + obj->oriCorrect());
	// 			Vector3 pos = obj->getTranslation();
	// 			Quaternion rot = obj->getRotation();
	// 			// Matrix3 inerTensOld = obj->inertiaTensor();
	// 			Quaternion rotInc =
	// 				rotInc3D.squaredNorm() > 0
	// 					? Quaternion(
	// 						  AngleAxis(rotInc3D.norm(), rotInc3D.normalized()))
	// 					: Quaternion(AngleAxis(0, Vector3(1, 0, 0)));
	// 			Vector3 posInc = obj->velocity() * dt + obj->posCorrect();
	// 			pos += posInc;
	// 			rot = rotInc * rot;
	// 			obj->setConfiguration(pos, rot);
	// 		}
	// 		mp_rigidWorld->updateRigidBodyPositions(m_objects, m_broadPhase);
	// 		updateAllFCLObjects();
	// 		m_totalSubsteps++;
	// 		m_time += dt;
	// 	};

	Timer stepTimer;
	stepTimer.Resume();
	if (m_adaptiveTimestep) {
		Scalar currStep = 0.;
		while (currStep < 1) {
			Timer substepTimer;
			substepTimer.Resume();

			// Find the maximum (normalized) velocity of AABB of objects.
			Vector3 minComp, maxComp;
			minComp.setConstant(std::numeric_limits<Scalar>::infinity());
			maxComp.setConstant(-std::numeric_limits<Scalar>::infinity());
			for (size_t i = 0; i < m_objects.size(); ++i) {
				auto vertVels = m_objects[i]->aabbVel();
				minComp = minComp.cwiseMin(vertVels.rowwise().minCoeff());
				maxComp = maxComp.cwiseMax(vertVels.rowwise().maxCoeff());
			}
			Vector3 avgVel = 0.5 * (minComp + maxComp);
			Scalar maxVertSpeed = 0;
			for (size_t i = 0; i < m_objects.size(); ++i) {
				auto vertVels = m_objects[i]->aabbVel();
				vertVels.colwise() -= avgVel;
				Scalar maxVertSpeedObj = vertVels.colwise().norm().maxCoeff();
				maxVertSpeed = std::max(maxVertSpeedObj, maxVertSpeed);
			}

			// Determine maximum allowed timestep size
			Scalar recStepSize =
				m_minObjLength /
				(2 * (maxVertSpeed * timestep + 1e-8) * m_substepFactor);
			recStepSize = std::min(1 - currStep, recStepSize);
			std::cout << "Substep size (0-1): " << recStepSize << std::endl;

			fillForces(recStepSize * timestep);
			updateAllObjects(recStepSize * timestep);

			currStep += recStepSize;
			substepTimer.Pause();
			if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_TIME)) {
				std::cout << "Total substep calculation time: "
						  << substepTimer.GetSeconds() << std::endl;
			}
		}
	} else {
		fillForces(timestep);
		updateAllObjects(timestep);
	}
	stepTimer.Pause();
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_TIME)) {
		std::cout << "Total step calculation time: " << stepTimer.GetSeconds()
				  << std::endl;
	}
	m_totalTime += stepTimer.GetSeconds();
	m_totalSteps++;
}
void DynamicSystem::generateFCLContacts(
	std::vector<fcl::Contact<Scalar>>& contacts) {
	fcl::DefaultCollisionData<Scalar> collisionData;
	collisionData.request.num_max_contacts = 1000000;
	collisionData.request.enable_contact = true;

	m_broadPhase.collide(collisionData);
	contacts.clear();
	collisionData.result.getContacts(contacts);
}
void DynamicSystem::reset() {
	mp_forceSolver->reset();
	// for (size_t i = 0; i < m_objects.size(); ++i) {
	// 	m_objects[i]->reset();
	// }
	mp_rigidWorld->reset();
	// updateAllFCLObjects();
	m_contactInfo.clear();

	m_contactDetectionTimer.Reset();
	m_contactMergeTimer.Reset();
	m_totalSteps = 0;
	m_totalSubsteps = 0;
	m_totalContactSubsteps = 0;
	m_totalContacts = 0;
	m_totalContactsBeforeMerge = 0;
	m_totalTime = 0;
	m_time = 0;
}

void DynamicSystem::generateContacts(std::vector<ContactInformation>& out,
                                     std::vector<fcl::Contact<Scalar>>& in) {
	omp_set_num_threads((in.size() < 300) ? 1 : physicalProcessors());

#pragma omp parallel for
	for (size_t i = 0; i < in.size(); ++i) {
		// Order the contacts by object ID;
		if (m_pointerToObjectId[in[i].o1] > m_pointerToObjectId[in[i].o2]) {
			std::swap(in[i].o1, in[i].o2);
			std::swap(in[i].b1, in[i].b2);
			in[i].normal *= -1;
		}
	}

	// Sort the contacts lexographically by objects.
	std::sort(
		in.begin(), in.end(),
		[&](const fcl::Contact<Scalar>& a, const fcl::Contact<Scalar>& b) {
			size_t ida1 = m_pointerToObjectId[a.o1];
			size_t ida2 = m_pointerToObjectId[a.o2];
			size_t idb1 = m_pointerToObjectId[b.o1];
			size_t idb2 = m_pointerToObjectId[b.o2];
			if (ida1 != idb1) {
				return ida1 < idb1;
			} else if (ida2 != idb2) {
				return ida2 < idb2;
			} else {
				return false;
			}
		});
	out.clear();
	std::vector<size_t> breakPoints;
	breakPoints.push_back(0);
	for (size_t i = 0; i < in.size();) {
		size_t j = i + 1;
		for (; j < in.size(); ++j) {
			if (in[i].o1 != in[j].o1 || in[i].o2 != in[j].o2) {
				break;
			}
		}
		breakPoints.push_back(j);
		i = j;
	}

	// Convert contacts pair (of objects) by pair
#pragma omp declare reduction(                                    \
		merge : std::vector<ContactInformation> : omp_out.insert( \
				omp_out.end(), omp_in.begin(), omp_in.end()))
#pragma omp parallel for reduction(merge : out)
	for (size_t i = 0; i < breakPoints.size() - 1; ++i) {
		addPairwiseObjectContacts(out, in, breakPoints[i], breakPoints[i + 1]);
	}
	omp_set_num_threads(std::thread::hardware_concurrency());
}
std::string DynamicSystem::printTimings() const {
	std::stringstream ss;

	ss << "Average #contacts (before merge): "
	   << (double)m_totalContactsBeforeMerge / m_totalContactSubsteps
	   << "\nAverage #contacts (after merge): "
	   << (double)m_totalContacts / m_totalContactSubsteps
	   << "\nAverage substeps per step: "
	   << (double)m_totalSubsteps / m_totalSteps
	   << "\nTotal #solids: " << m_objects.size() << "\n"
	   << "\nTimes per substep (seconds): "
	   << "\n\tTotal contact query time: "
	   << m_contactDetectionTimer.GetSeconds() / m_totalContactSubsteps
	   << "\n\t\tFrom primitive intersection check: "
	   << (m_contactDetectionTimer.GetSeconds() -
	       m_contactMergeTimer.GetSeconds()) /
			  m_totalContactSubsteps
	   << "\n\t\tContact generation time: "
	   << m_contactMergeTimer.GetSeconds() / m_totalContactSubsteps
	   << mp_forceSolver->printTimings(m_totalContactSubsteps)
	   << "\n\tTotal: " << m_totalTime / m_totalContactSubsteps;

	return ss.str();
}

void DynamicSystem::addPairwiseObjectContacts(
	std::vector<ContactInformation>& out,
	std::vector<fcl::Contact<Scalar>>& in,
	int begin,
	int end) {
	std::vector<fcl::Contact<Scalar>> contacts;

	auto* oPtr = m_objects[m_pointerToObjectId[in[begin].o1]].get();
	auto* oPtr2 = m_objects[m_pointerToObjectId[in[begin].o2]].get();
	if (oPtr->isStatic() && oPtr2->isStatic()) {
		return;
	}
	if (oPtr == oPtr2) {
		return;
	}
	contacts.reserve(end - begin);
	contacts.insert(contacts.begin(), in.begin() + begin, in.begin() + end);

	// Call contact handlers to generate contacts.
	std::vector<ContactInformation> inter;
	(*m_contactGeneratorMatrix[static_cast<size_t>(oPtr->getType())]
	                          [static_cast<size_t>(oPtr2->getType())])(
		contacts, oPtr, oPtr2, inter);

	if (inter.size() > 0) {
		std::sort(
			inter.begin(), inter.end(),
			[&](const ContactInformation& a, const ContactInformation& b) {
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
			if ((inter[i].pos - inter[i - 1].pos).squaredNorm() > 1e-8) {
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
				for (size_t j = breakPoints[i] + 1; j < breakPoints[i + 1];
				     ++j) {
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
}

void DynamicSystem::fillFromParams(const Params::DynamicSystem& params) {
	m_timestep = params.timestep;
	switch (params.forceSolverType) {
	case Solver::ForceSolverType::PrimalDual: {
		mp_forceSolver =
			std::make_unique<Solver::PrimalDualForceSolver>(mp_logging);
		break;
	}
	case Solver::ForceSolverType::Null: {
		mp_forceSolver = std::make_unique<Solver::NullForceSolver>(mp_logging);
		break;
	}
	default:
		throw std::runtime_error("Invalid solver type in config tree!");
	}
	mp_forceSolver->fillFromParams(*params.p_solver);
	m_gravity = params.gravity;

	switch (params.worldType) {
	case RigidWorldType::EUCLIDEAN: {
		mp_rigidWorld = std::make_unique<EuclideanWorld>();
		break;
	}
	case RigidWorldType::PERIODIC: {
		mp_rigidWorld = std::make_unique<PeriodicWorld>();
		break;
	}
	default:
		throw std::runtime_error("Invalid rigid body world type!");
	}
	mp_rigidWorld->fillFromParams(*params.p_rigidWorld);

	m_adaptiveTimestep = params.adaptiveTimestep;
	if (m_adaptiveTimestep) {
		m_substepFactor = params.substepFactor;
	}
	else {
		m_substeps = params.substeps;
	}
}
}  // namespace Dynamics
}  // namespace FrictionFrenzy
