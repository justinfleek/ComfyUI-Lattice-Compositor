#include "PrimalDualForceSolver.h"
#include "Common/Cores.h"
#include "Common/Hashing.h"
#include "Common/LoggingOptions.h"
#include "Common/MatrixTypes.h"
#include "NonSmoothForces/NonSmoothForces.h"
#include "SmoothForces/SmoothForces.h"
#include "Solver/ForceSolverBase.h"
#include "Solver/PrimalDual/NonSmoothForces/NonSmoothContactForce.h"
#include "Solver/PrimalDual/NonSmoothForces/NonSmoothForceBase.h"
#include "Solver/PrimalDual/SmoothForces/SmoothForceBase.h"

#include <eigen3/Eigen/src/Core/products/Parallelizer.h>
#include <omp.h>
#include <Eigen/CholmodSupport>
#include <amgcl/adapter/block_matrix.hpp>
#include <amgcl/amg.hpp>
#include <amgcl/backend/eigen.hpp>
#include <amgcl/coarsening/smoothed_aggregation.hpp>
#include <amgcl/make_solver.hpp>
#include <amgcl/relaxation/as_preconditioner.hpp>
#include <amgcl/relaxation/gauss_seidel.hpp>
#include <amgcl/solver/cg.hpp>
#include <amgcl/value_type/static_matrix.hpp>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <ostream>
#include <thread>

namespace FrictionFrenzy {
namespace Solver {
std::tuple<Scalar, Scalar> PrimalDualForceSolver::nonDimensionalParams(
	const Scalar timestep,
	const Vector3& gravity,
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& pObjects) {
	Scalar avgMass = 0;
	int actObjs = 0;
	for (size_t i = 0; i < pObjects.size(); ++i) {
		if (pObjects[i]->isActive()) {
			avgMass += pObjects[i]->genMassMat().trace();
			actObjs++;
		}
	}
	avgMass = (actObjs > 0) ? avgMass / actObjs / 6 : 1;

	Scalar charSpeed = 0;
	VectorX objSpeed = VectorX::Zero(pObjects.size());
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		bool hasStatic = false;
		Vector3 relVel = Vector3::Zero();
		for (int j = 0; j < 2; ++j) {
			int objId = contactInfo[i].objId[j];
			Vector6 velExt;
			velExt << pObjects[objId]->velocity(),
				pObjects[objId]->angularVel();
			if (pObjects[objId]->isActive()) {
				velExt.head(3) += gravity * timestep;
			} else {
				hasStatic = true;
			}
			Vector3 relVelHalf = contactInfo[i].toLocal(j, velExt);
			relVel += relVelHalf;

			objSpeed[objId] = std::max(objSpeed[objId], relVelHalf.norm());
		}
		if (hasStatic) {
			for (int j = 0; j < 2; ++j) {
				int objId = contactInfo[i].objId[j];
				objSpeed[objId] = std::max(objSpeed[objId], relVel.norm());
			}
		}
	}
	Scalar massSum = 0;
	for (size_t i = 0; i < pObjects.size(); ++i) {
		if (pObjects[i]->isActive()) {
			massSum += pObjects[i]->mass();
			charSpeed += objSpeed[i] * pObjects[i]->mass();
		}
	}
	charSpeed /= massSum;
	charSpeed = std::max(charSpeed, gravity.norm() * timestep);

	Scalar avgForce = 0;
	size_t numCache = 0;
	std::unordered_set<std::pair<size_t, size_t>> vs;
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		const auto& c = contactInfo[i];
		std::pair<size_t, size_t> objPair = {c.objId[0], c.objId[1]};
		if (m_contactCacheLocal.count(objPair)) {
			const auto& cc = m_contactCacheLocal[objPair];
			avgForce += cc.first / cc.second;
			numCache++;
			vs.insert(objPair);
		}
	}
	if (numCache) {
		avgForce /= numCache;
		Scalar charSpeedForce = avgForce * timestep / avgMass;
		charSpeed = (charSpeed + charSpeedForce) * 0.5;
	}

	charSpeed = std::max(charSpeed, 1e-4);

	return {avgMass, charSpeed};
}
void PrimalDualForceSolver::fillForces(
	const Scalar timestep,
	const Vector3& gravity,
	std::vector<ContactInformation>& contactInfo,
	std::vector<std::unique_ptr<RigidObjectBase>>& objects) {
	// Terminate if no contacts are present.
	if (contactInfo.empty()) {
		return;
	}

	std::vector<std::unordered_set<size_t>> adjObj(objects.size());
	std::vector<bool> hasContact(objects.size(), false);
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		size_t id0 = contactInfo[i].objId[0];
		size_t id1 = contactInfo[i].objId[1];
		if (objects[id0]->isActive() && objects[id1]->isActive()) {
			adjObj[id0].insert(id1);
			adjObj[id1].insert(id0);
		}
		hasContact[id0] = true;
		hasContact[id1] = true;
	}
	std::vector<size_t> objToGroup(objects.size(), -1);
	std::vector<bool> visited(objects.size(), false);
	typedef std::queue<int> queue;
	queue bfsq;
	size_t gId = 0;
	for (size_t i = 0; i < objects.size(); ++i) {
		if (objects[i]->isStatic()) {
			continue;
		}
		if (!visited[i] && hasContact[i]) {
			bfsq.push(i);
			visited[i] = true;
			while (!bfsq.empty()) {
				size_t front = bfsq.front();
				objToGroup[front] = gId;
				bfsq.pop();
				for (const size_t& n : adjObj[front]) {
					if (!visited[n]) {
						bfsq.push(n);
						visited[n] = true;
					}
				}
			}
			gId++;
		}
	}

	std::vector<std::vector<ContactInformation>> contactGroups(gId);
	std::vector<std::vector<size_t>> localToGlobalContact(gId);
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		size_t group = -1;
		for (const size_t j : contactInfo[i].objId) {
			if (objects[j]->isActive()) {
				group = objToGroup[j];
				break;
			}
		}
		contactGroups[group].push_back(contactInfo[i]);
		localToGlobalContact[group].push_back(i);
	}

	if (hasLoggingOption(mp_logging, LoggingOptions::MISC_DEBUG)) {
		std::cout << "Solving " << gId << " contact groups." << std::endl;
	}

	for (size_t gId = 0; gId < contactGroups.size(); ++gId) {
		m_contactCacheLocal.clear();
		auto& contactInfoLocal = contactGroups[gId];
		auto& contactToGlobal = localToGlobalContact[gId];
		if (contactInfoLocal.empty()) {
			continue;
		}
		std::unordered_map<int, int> globalToLocalObjId;
		std::vector<int> localToGlobalObjId;
		for (size_t i = 0; i < contactInfoLocal.size(); ++i) {
			for (int j = 0; j < 2; ++j) {
				int id = contactInfoLocal[i].objId[j];
				if (!globalToLocalObjId.count(id)) {
					int localId = globalToLocalObjId.size();
					globalToLocalObjId[id] = localId;
					localToGlobalObjId.push_back(id);
				}
			}
		}
		std::vector<RigidObjectBase*> localObjs(globalToLocalObjId.size());
		for (size_t i = 0; i < localObjs.size(); ++i) {
			localObjs[i] = objects[localToGlobalObjId[i]].get();
		}
		for (size_t i = 0; i < contactInfoLocal.size(); ++i) {
			std::pair<size_t, size_t> localPair;
			size_t id0 = contactInfoLocal[i].objId[0];
			size_t id1 = contactInfoLocal[i].objId[1];
			localPair.first = globalToLocalObjId[id0];
			localPair.second = globalToLocalObjId[id1];
			if (m_contactCache.count({id0, id1})) {
				m_contactCacheLocal[localPair] = m_contactCache[{id0, id1}];
			}
		}
#pragma omp parallel for
		for (size_t i = 0; i < contactInfoLocal.size(); ++i) {
			for (int j = 0; j < 2; ++j) {
				int id = contactInfoLocal[i].objId[j];
				contactInfoLocal[i].objId[j] = globalToLocalObjId[id];
			}
		}

		fillForcesIntl(timestep, gravity, contactInfoLocal, localObjs);

		// Restore the numbering of objects.

#pragma omp parallel for
		for (size_t i = 0; i < contactInfoLocal.size(); ++i) {
			for (int j = 0; j < 2; ++j) {
				int id = contactInfoLocal[i].objId[j];
				contactInfoLocal[i].objId[j] = localToGlobalObjId[id];
			}
			contactInfo[contactToGlobal[i]] = contactInfoLocal[i];
		}
	}

	// Renumber objects to exclude ones not in contact.
	// 	std::unordered_map<int, int> globalToLocalObjId;
	// 	std::vector<int> localToGlobalObjId;
	// 	for (size_t i = 0; i < contactInfo.size(); ++i) {
	// 		for (int j = 0; j < 2; ++j) {
	// 			int id = contactInfo[i].objId[j];
	// 			if (!globalToLocalObjId.count(id)) {
	// 				int localId = globalToLocalObjId.size();
	// 				globalToLocalObjId[id] = localId;
	// 				localToGlobalObjId.push_back(id);
	// 			}
	// 		}
	// 	}
	// 	std::vector<RigidObjectBase*> localObjs(globalToLocalObjId.size());
	// 	for (size_t i = 0; i < localObjs.size(); ++i) {
	// 		localObjs[i] = objects[localToGlobalObjId[i]].get();
	// 	}
	// #pragma omp parallel for
	// 	for (size_t i = 0; i < contactInfo.size(); ++i) {
	// 		for (int j = 0; j < 2; ++j) {
	// 			int id = contactInfo[i].objId[j];
	// 			contactInfo[i].objId[j] = globalToLocalObjId[id];
	// 		}
	// 	}
	//
	// 	fillForcesIntl(timestep, gravity, contactInfo, localObjs);
	//
	// 	// Restore the numbering of objects.
	// #pragma omp parallel for
	// 	for (size_t i = 0; i < contactInfo.size(); ++i) {
	// 		for (int j = 0; j < 2; ++j) {
	// 			int id = contactInfo[i].objId[j];
	// 			contactInfo[i].objId[j] = localToGlobalObjId[id];
	// 		}
	// 	}

	m_contactCache.clear();
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		const auto& c = contactInfo[i];
		// auto& cc = m_contactCache[{c.objId[0], c.objId[1]}];
		std::pair<size_t, size_t> p{c.objId[0], c.objId[1]};
		if (!m_contactCache.count(p)) {
			m_contactCache[p].first = 0;
			m_contactCache[p].second = 0;
		}
		m_contactCache[{c.objId[0], c.objId[1]}].first += c.localForce[0];
		m_contactCache[{c.objId[0], c.objId[1]}].second += 1;
		// cc.first += c.localForce;
		// cc.second += 1;
	}
}

template <typename D>
void PrimalDualForceSolver::calculateResiduals(
	bool useStoredConstraints,
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& pObjects,
	const Eigen::MatrixBase<D>& vels,
	const Eigen::MatrixBase<D>& forces,
	const Eigen::MatrixBase<D>& lambda,
	const Eigen::MatrixBase<D>& velsOld,
	Eigen::Ref<const SparseMat> massMat,
	const Scalar charMass,
	const Scalar charSpeed,
	const Scalar timestep,
	const Scalar mu,
	Eigen::MatrixBase<D>& ru,
	Eigen::MatrixBase<D>& rf,
	Eigen::MatrixBase<D>& wrf,
	Eigen::MatrixBase<D>& rl) {
	VectorX ruadd;
	ru = massMat * (vels - velsOld);
#pragma omp parallel for
	for (size_t i = 0; i < pObjects.size(); ++i) {
		if (pObjects[i]->isStatic()) {
			ru.segment(i * 6, 6).setZero();
		}
	}
	VectorX fWeight = mp_nonSmoothForce->calculateTangentialWeight(
		contactInfo, pObjects, vels, forces, charMass);
	VectorX rSmoothForce = VectorX::Zero(pObjects.size() * 6);
	for (auto& smoothForce : m_smoothForces) {
		rSmoothForce += timestep / charSpeed / charMass *
		                smoothForce->force(contactInfo, pObjects, vels, forces,
		                                   mp_nonSmoothForce->dimensions(),
		                                   charSpeed, charMass, timestep);
	}
	ru -= rSmoothForce;
	mp_nonSmoothForce->nonSmoothResiduals(contactInfo, pObjects, vels, forces,
	                                      lambda, mu, useStoredConstraints,
	                                      ruadd, rf.derived(), rl.derived());
	ru += ruadd;
	wrf = rf.cwiseProduct(fWeight);
}

void PrimalDualForceSolver::fillForcesIntl(
	const Scalar timestep,
	const Vector3& gravity,
	std::vector<ContactInformation>& contactInfo,
	std::vector<RigidObjectBase*>& pObjects) {
	// Number of different unknowns for convenience.
	const size_t n_contacts = contactInfo.size();
	const size_t n_objects = pObjects.size();
	const size_t n_rigidDof = pObjects.size() * 6;
	const size_t n_forceDof = n_contacts * mp_nonSmoothForce->dimensions();
	const size_t n_constraintDof =
		n_contacts * mp_nonSmoothForce->constraintsPerForce();
	const size_t n_unknowns = n_rigidDof + n_forceDof + n_constraintDof;

	// The unknowns themselves.
	VectorX velsOld(n_rigidDof);
	VectorX vels(n_rigidDof);
	VectorX forces(n_forceDof);
	VectorX lambda(n_constraintDof);

	// The linear system structures.
	VectorX rhs(n_rigidDof);
	SparseMat A(n_rigidDof, n_rigidDof);
	std::unordered_map<std::pair<size_t, size_t>, Scalar*> matPointers;

	VectorX du(rhs.size()), df, dl;

	Eigen::setNbThreads((n_unknowns < 1000) ? 1 : physicalProcessors());
	omp_set_num_threads((n_unknowns < 1000) ? 1 : physicalProcessors());
	if (hasLoggingOption(mp_logging, LoggingOptions::MISC_DEBUG)) {
		std::cout << "Solving forces" << std::endl;
	}

	m_forceProcessTimer.Resume();

	// Initialize velocities.
#pragma omp parallel for
	for (size_t i = 0; i < n_objects; ++i) {
		vels.segment<6>(i * 6) << pObjects[i]->velocity(),
			pObjects[i]->angularVel();
		velsOld.segment<6>(i * 6) = vels.segment<6>(i * 6);
		if (pObjects[i]->isActive()) {
			velsOld.segment<3>(i * 6) += pObjects[i]->acceleration();
			velsOld.segment<3>(i * 6 + 3) += pObjects[i]->angularAcc();
		}
	}

	Scalar charMass = 1, charSpeed = 1;
	std::tie(charMass, charSpeed) =
		nonDimensionalParams(timestep, gravity, contactInfo, pObjects);
	vels /= charSpeed;
	velsOld /= charSpeed;

	// Pre solve logging
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_CHARFACTOR)) {
		std::cout << "Characteristic mass / speed: " << charMass << " "
				  << charSpeed << std::endl;
	}
	if (hasLoggingOption(mp_logging, LoggingOptions::MAX_PENETRATION_DEPTH)) {
		Scalar depth = 0;
		for (size_t i = 0; i < contactInfo.size(); ++i) {
			depth = std::max(depth, std::abs(contactInfo[i].depth));
		}
		std::cout << "Max penetration depth: " << depth << std::endl;
	}

	// Initialize mass matrix
	std::vector<Eigen::Triplet<Scalar>> massTriplets;
	for (size_t i = 0; i < n_objects; ++i) {
		if (pObjects[i]->isStatic()) {
			for (int j = 0; j < 6; ++j) {
				massTriplets.emplace_back(i * 6 + j, i * 6 + j, 1);
			}
		} else {
			Matrix6 masses = pObjects[i]->genMassMat() / charMass;
			for (int j = 0; j < 6; ++j) {
				for (int k = 0; k < 6; ++k) {
					if (masses(j, k)) {
						massTriplets.emplace_back(i * 6 + j, i * 6 + k,
						                          masses(j, k));
					}
				}
			}
		}
	}
	// VectorX bCoeff = VectorX::Zero(n_objects * 3);
	// for (size_t i = 0; i < n_contacts; ++i) {
	// 	std::pair<size_t, size_t> ids = {contactInfo[i].objId[0],
	// 	                                 contactInfo[i].objId[1]};
	// 	if (m_contactCacheLocal.count(ids)) {
	// 		const auto& cc = m_contactCacheLocal[ids];
	// 		if (!cc.second) {
	// 			continue;
	// 		}
	// 		for (size_t j = 0; j < 2; ++j) {
	// 			auto jac = contactInfo[i].getTrans(j);
	// 			Matrix3 disp =
	// 				jac.block<3, 3>(3, 0) * jac.block<3, 3>(0, 0).transpose();
	// 			Vector3 force = jac.block<3, 3>(0, 0) *
	// 			                (cc.first.cwiseProduct(Vector3(1, 0, 0))) /
	// 			                cc.second / charMass / charSpeed;
	// 			Matrix3 fc = (Matrix3() << 0, -force[2], force[1], force[2], 0,
	// 			              -force[0], -force[1], force[0], 0)
	// 			                 .finished();
	// 			Vector3 gsn = (fc * disp).colwise().norm().transpose();
	// 			bCoeff.segment<3>(3 * contactInfo[i].objId[j]) +=
	// 				timestep * timestep * gsn * 0.5;
	// 		}
	// 	}
	// }
	// for (size_t i = 0; i < n_objects; ++i) {
	// 	if (pObjects[i]->isActive()) {
	// 		for (size_t j = 0; j < 3; ++j) {
	// 			massTriplets.emplace_back(i * 6 + j + 3, i * 6 + j + 3,
	// 			                          bCoeff[3 * i + j]);
	// 		}
	// 	}
	// }
	SparseMat massMat(n_rigidDof, n_rigidDof);
	massMat.setFromTriplets(massTriplets.begin(), massTriplets.end());

	// Initialize the sparse matrix structures.
	std::unordered_set<std::pair<size_t, size_t>> objectPairs;
	mp_nonSmoothForce->linsysReserve(contactInfo, pObjects, objectPairs,
	                                 massTriplets);
	for (auto& smoothForce : m_smoothForces) {
		smoothForce->linsysReserve(contactInfo, pObjects, massTriplets,
		                           objectPairs);
	}
	A.setFromTriplets(massTriplets.begin(), massTriplets.end());
	for (int k = 0; k < A.outerSize(); ++k) {
		for (SparseMat::InnerIterator it(A, k); it; ++it) {
			matPointers[{it.row(), it.col()}] = &(it.valueRef());
		}
	}

	// Initialize force solvers.
	mp_nonSmoothForce->preprocess(contactInfo, pObjects, vels, timestep,
	                              charMass, charSpeed);
	// Initialize forces and constraints.
	mp_nonSmoothForce->initForces(contactInfo, timestep, charMass, charSpeed,
	                              vels, forces, lambda);

	int itCoupled = 0;
	// LDLT ldlt;
	Eigen::CholmodSimplicialLDLT<SparseMat> ldlt;
	Eigen::CholmodSupernodalLLT<SparseMat> snllt;
	CG cg;

	Scalar Hu = 1e-4;
	Scalar exitErr;

	// Main Newton's method loop
	auto mainIteration = [&](int maxIters, Scalar tol, int& it) {
		const Scalar power = 0.66667;
		VectorX ru, ruadd, rf, wrf, rl;
		for (it = 0; it < maxIters; ++it) {
			// Build the linear system
			m_systemBuildTimer.Resume();

			// Calculate constraints, residuals, and errors.
			mp_nonSmoothForce->calculateConstraints(vels, forces, lambda);
			Scalar sDualGap = mp_nonSmoothForce->surrogateDualGap(lambda);
			Scalar mu = sDualGap * 0.1;

			calculateResiduals(true, contactInfo, pObjects, vels, forces,
			                   lambda, velsOld, massMat, charMass, charSpeed,
			                   timestep, mu, ru, rf, wrf, rl);
			if (!it) {
				// Scalar scale = std::min(
				// 	std::min(ru.norm(), rf.norm()) / rl.norm(), Scalar(10));
				Scalar scale = std::min(ru.norm(), rf.norm()) / (rl.norm());
				scale = std::min(scale, Scalar(10));
				// NonSmoothContactForce* nsf =
				// 	dynamic_cast<NonSmoothContactForce*>(
				// 		mp_nonSmoothForce.get());
				// if (nsf && nsf->m_springBasedForce) {
				// 	scale = std::min(scale, Scalar(10));
				// } else {
				// 	scale = std::min(scale, Scalar(10));
				// }
				lambda *= scale;
				sDualGap *= scale;
				mu *= scale;

				calculateResiduals(true, contactInfo, pObjects, vels, forces,
				                   lambda, velsOld, massMat, charMass,
				                   charSpeed, timestep, mu, ru, rf, wrf, rl);
			}
			VectorX acVec =
				mp_nonSmoothForce->ACVector(contactInfo, vels, forces);
			Scalar err =
				ru.squaredNorm() + wrf.squaredNorm() + rl.squaredNorm();
			Scalar sErr = searchError(ru, wrf, rl);
			Scalar sacErr = searchACError(ru, acVec, rl.array() - mu);
			Scalar eps = Hu * std::pow(err, power * 0.5);
			Scalar momenErr = ru.norm() / ru.size();
			exitErr = std::max(momenErr, wrf.norm() / wrf.size());
			exitErr = std::max(exitErr, rl.norm() / rl.size());
			exitErr = std::max(exitErr, sDualGap);
			exitErr = std::min(exitErr,
			                   std::max(momenErr, acVec.norm() / acVec.size()));
			if (hasLoggingOption(mp_logging, LoggingOptions::PER_ITER_ERRORS)) {
				std::cout << "Error: " << ru.norm() / ru.size() << " "
						  << wrf.norm() / n_forceDof << " "
						  << rl.norm() / n_constraintDof
						  << ", search errors: " << sErr << " " << sacErr
						  << ", AC Error: " << acVec.norm() / acVec.size()
						  << ", dual gap: " << sDualGap << " H: " << Hu
						  << ", eps: " << eps << std::endl;
			}
			if (exitErr < tol && (sDualGap < tol || sDualGap < 10 * exitErr)) {
				break;
			}

			// Set linear system to zero
			rhs.setZero();
#pragma omp parallel for
			for (int k = 0; k < A.outerSize(); ++k) {
				for (SparseMat::InnerIterator Ait(A, k); Ait; ++Ait) {
					Ait.valueRef() = 0;
				}
			}
#pragma omp parallel for
			for (int k = 0; k < massMat.outerSize(); ++k) {
				for (SparseMat::InnerIterator Mit(massMat, k); Mit; ++Mit) {
					*matPointers[{Mit.row(), Mit.col()}] += Mit.value();
					if (Mit.row() == Mit.col()) {
						*matPointers[{Mit.row(), Mit.col()}] += eps;
					}
				}
			}

			// Calculate linear system terms.
			mp_nonSmoothForce->linsysAddition(contactInfo, pObjects, lambda, rf,
			                                  rl, eps, rhs, matPointers);
			if (it >= 1) {
				for (auto& smoothForce : m_smoothForces) {
					smoothForce->addForceGrad(
						contactInfo, pObjects, vels, forces,
						mp_nonSmoothForce->dimensions(), charSpeed, charMass,
						timestep, eps, matPointers);
				}
			}
			rhs -= ru;

			// Set static objects to zero.
#pragma omp parallel for
			for (size_t i = 0; i < pObjects.size(); ++i) {
				if (pObjects[i]->isStatic()) {
					rhs.segment<6>(i * 6).setZero();
				}
			}

			// Scale linear system for better convergence.
			VectorX D(A.rows());
#pragma omp parallel for
			for (Eigen::Index k = 0; k < A.outerSize(); ++k) {
				for (SparseMat::InnerIterator Mit(A, k); Mit; ++Mit) {
					if (Mit.row() == Mit.col()) {
						D[k] = 1 / std::sqrt(Mit.value());
						break;
					}
				}
			}
#pragma omp parallel for
			for (int k = 0; k < A.outerSize(); ++k) {
				for (SparseMat::InnerIterator Mit(A, k); Mit; ++Mit) {
					Mit.valueRef() *= (D[Mit.row()] * D[Mit.col()]);
				}
			}
			rhs = rhs.cwiseProduct(D);
			m_systemBuildTimer.Pause();

			// Solve linear system with either Eigen or AMGCL.
			m_systemSolveTimer.Resume();
			size_t maxCGIt = 1000;
			size_t iters = 0;
			Scalar linError;

			if (pObjects.size() < 1000) {
				if (it == 0) {
					ldlt.analyzePattern(A);
				}
				ldlt.factorize(A);
				if (ldlt.info() == Eigen::Success) {
					du = ldlt.solve(rhs);
				} else {
					du.setZero();
				}
			} else if (pObjects.size() < 10000) {
				if (it == 0) {
					snllt.analyzePattern(A);
				}
				snllt.factorize(A);
				if (snllt.info() == Eigen::Success) {
					du = snllt.solve(rhs);
				} else {
					du.setZero();
				}
			} else {
				typedef amgcl::static_matrix<Scalar, 6, 6> dmat_type;
				typedef amgcl::static_matrix<Scalar, 6, 1> dvec_type;
				typedef amgcl::backend::builtin<dmat_type> SBackend;
				typedef amgcl::make_solver<
					amgcl::amg<SBackend,
				               amgcl::coarsening::smoothed_aggregation,
				               amgcl::relaxation::gauss_seidel>,
					amgcl::solver::cg<SBackend>>
					amgSolver;

				auto pRhs = reinterpret_cast<dvec_type*>(rhs.data());
				auto pX = reinterpret_cast<dvec_type*>(du.data());
				auto B =
					amgcl::make_iterator_range(pRhs, pRhs + pObjects.size());
				auto X = amgcl::make_iterator_range(pX, pX + pObjects.size());
				amgSolver::params prm;
				auto Ab = amgcl::adapter::block_matrix<dmat_type>(A);
				prm.solver.maxiter = maxCGIt;
				amgSolver amgs(Ab, prm);
				std::tie(iters, linError) = amgs(B, X);
				if (!std::isfinite(linError)) {
					CG cg;
					du = cg.compute(A).solve(rhs);
					iters = cg.iterations();
					linError = cg.error();
				}
				if (hasLoggingOption(mp_logging,
				                     LoggingOptions::PER_ITER_ERRORS)) {
					std::cout << "Solver: " << iters
							  << " iters, error: " << linError << std::endl;
				}
			}
			du = du.cwiseProduct(D);

			// Retrieve force and lambda step size.
			mp_nonSmoothForce->retrieveNonSmoothForceInc(
				contactInfo, lambda, du, rf, rl, mu, df, dl);
			m_systemSolveTimer.Pause();

			// Perform a line search.
			m_lineSearchTimer.Resume();
			LineSearchResult stepSearch =
				lineSearch(contactInfo, pObjects, massMat, vels, forces, lambda,
			               ru, rf, rl, du, df, dl, velsOld, sErr, sacErr, mu,
			               timestep, charSpeed, charMass, 10);
			bool useGD = false;

			// Fall back to gradient descent if failed.
			if (stepSearch.stepSize == 0) {
				if (hasLoggingOption(mp_logging,
				                     LoggingOptions::PER_ITER_ERRORS)) {
					std::cout << "Falling back to gradient descent..."
							  << std::endl;
				}
				useGD = true;
				du = -ru;
				df = rf;
				dl = rl;
				stepSearch =
					lineSearch(contactInfo, pObjects, massMat, vels, forces,
				               lambda, ru, rf, rl, du, df, dl, velsOld, sErr,
				               sacErr, mu, timestep, charSpeed, charMass, 20);
				// FloatType scale = std::min(ru.norm(), rf.norm()) /
				// rl.norm(); lambda *= std::pow(scale, 0.5);
				if (stepSearch.stepSize < 5e-6 && Hu > 1e3) {
					if (hasLoggingOption(mp_logging,
					                     LoggingOptions::PER_ITER_ERRORS)) {
						std::cout << "Ending without converging..."
								  << std::endl;
					}
					++it;
					break;
				}
			}

			// if (stepSearch.stepSize > 5e-6) {
			vels = stepSearch.newU;
			forces = stepSearch.newF;
			lambda = stepSearch.newL;
			// } else {
			// FloatType scale = std::min(ru.norm(), rf.norm()) / rl.norm();
			// lambda *= std::pow(scale, 0.1);
			// }

			// Update regularizer.
			if (!useGD && stepSearch.stepSize == 1) {
				if (iters == maxCGIt) {
					Hu *= 1.3;
				} else {
					Hu /= 4;
				}
			} else {
				Hu *= 4;
			}
			Hu = std::max(Hu, Scalar(1e-6));
			m_lineSearchTimer.Pause();
		}
	};

	mainIteration(m_maxIter, m_tol, itCoupled);
	m_totalIterations += itCoupled;

	// Apply new velocities
#pragma omp parallel for
	for (size_t i = 0; i < pObjects.size(); ++i) {
		Vector6 newVel = vels.segment<6>(i * 6) * charSpeed;
		pObjects[i]->acceleration() =
			newVel.head<3>() - pObjects[i]->velocity();
		pObjects[i]->angularAcc() =
			newVel.tail<3>() - pObjects[i]->angularVel();
	}

	// Write new forces
	mp_nonSmoothForce->fillContactForces(forces, lambda, charMass, charSpeed,
	                                     m_tol, timestep, contactInfo);
	// #pragma omp parallel for
	// 	for (size_t i = 0; i < n_contacts; ++i) {
	// 		int dim = mp_nonSmoothForce->dimensions();
	// 		contactInfo[i].localForce.head(dim) =
	// 			forces.segment(i * dim, dim) * charSpeed * charMass;
	// 		contactInfo[i].isDynamic = (lambda(i) > m_tol);
	// 	}

	m_forceProcessTimer.Pause();

	// Post solve logging
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_ERRORS)) {
		VectorX acVec = mp_nonSmoothForce->ACVector(contactInfo, vels, forces);
		std::cout << "Iterations: " << itCoupled << std::endl;
		std::cout << "Exit Error: " << exitErr;
		std::cout << " acMax: "
				  << acVec
						 .reshaped(
							 mp_nonSmoothForce->dimensions(),
							 acVec.size() / mp_nonSmoothForce->dimensions())
						 .colwise()
						 .norm()
						 .maxCoeff()
				  << std::endl;
	}
	if (mp_nonSmoothForce->getType() ==
	        NonSmoothForceType::NON_SMOOTH_CONTACTS &&
	    hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_FRICTION_COEFF)) {
		Scalar averageFrictionCoeff = 0;
		Scalar averageFCWeight = 0;
		const Scalar coeff =
			*(dynamic_cast<NonSmoothContactForce*>(mp_nonSmoothForce.get())
		          ->mp_frictionCoeff);
		for (size_t i = 0; i < contactInfo.size(); ++i) {
			Scalar currCoeff = contactInfo[i].localForce.tail(2).norm() /
			                   contactInfo[i].localForce[0];
			if (currCoeff > coeff) {
				Scalar weight = contactInfo[i].localForce[0];
				averageFrictionCoeff += weight * currCoeff;
				averageFCWeight += weight;
			}
		}
		std::cout << "Average friction coefficient: "
				  << (averageFCWeight ? averageFrictionCoeff / averageFCWeight
		                              : coeff)
				  << std::endl;
	}
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_STEP_SPEEDS)) {
		Scalar tanSpeeds =
			objToContact(contactInfo, vels * charSpeed, {0, 1, 1})
				.reshaped(2, contactInfo.size())
				.colwise()
				.norm()
				.maxCoeff();
		const auto default_precision{std::cout.precision()};
		constexpr auto max_precision{
			std::numeric_limits<long double>::digits10 + 1};
		std::cout << std::setprecision(max_precision)
				  << "Max tangential speed: " << tanSpeeds << std::endl;
		std::cout << std::setprecision(default_precision);
	}

	Eigen::setNbThreads(std::thread::hardware_concurrency());
	omp_set_num_threads(std::thread::hardware_concurrency());
}
PrimalDualForceSolver::LineSearchResult PrimalDualForceSolver::lineSearch(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& pObjects,
	const SparseMat& massMat,
	const VectorX& vels,
	const VectorX& forces,
	const VectorX& lambda,
	const VectorX& ru,
	const VectorX& rf,
	const VectorX& rl,
	const VectorX& du,
	const VectorX& df,
	const VectorX& dl,
	const VectorX& velsOld,
	const Scalar sErr,
	const Scalar sacErr,
	const Scalar mu,
	const Scalar timestep,
	const Scalar charSpeed,
	const Scalar charMass,
	const int maxLineSearch) {
	Scalar step = 1.0;
	LineSearchResult res;
	res.newU = vels;
	res.newF = forces;
	res.newL = lambda;
	res.sErr = sErr;
	res.acErr = sacErr;
	res.stepSize = 0;
	if (hasLoggingOption(mp_logging, LoggingOptions::PER_ITER_ERRORS)) {
		std::cout << sErr << " " << sacErr << std::endl;
	}
	for (int stepIt = 0; stepIt < maxLineSearch; ++stepIt) {
		VectorX duIn = step * du;
		VectorX dfIn = step * df;
		VectorX dlIn = step * dl;

		mp_nonSmoothForce->filterLineSearch(contactInfo, pObjects, vels,
		                                    velsOld, forces, lambda, mu,
		                                    charMass, duIn, dfIn, dlIn);
		VectorX lInner = lambda + 0.99 * dlIn;
		VectorX vInner = vels + 0.99 * duIn;
		VectorX fInner = forces + 0.99 * dfIn;

		VectorX ruIn, rfIn, wrfIn, rlIn;
		calculateResiduals(false, contactInfo, pObjects, vInner, fInner, lInner,
		                   velsOld, massMat, charMass, charSpeed, timestep, mu,
		                   ruIn, rfIn, wrfIn, rlIn);

		Scalar inErr = searchError(ruIn, wrfIn, rlIn);
		VectorX acVecIn =
			mp_nonSmoothForce->ACVector(contactInfo, vInner, fInner);
		Scalar sacErrIn = searchACError(ruIn, acVecIn, rlIn.array() - mu);

		Scalar gErr = -duIn.dot(ruIn);
		Scalar gErrAC =
			gErr + dfIn.dot(acVecIn) +
			dlIn.cwiseQuotient(lInner).dot((rlIn.array() - mu).matrix());
		gErr += dfIn.dot(rfIn) + dlIn.cwiseQuotient(lInner).dot(rlIn);
		bool inErrAcpt = inErr - sErr < 1e-4 * step * gErr;
		// &&
		//                  gErr < 0.9 * (-duIn.dot(ru) + dfIn.dot(rf) +
		//                                dlIn.cwiseQuotient(lambda).dot(rl));
		// VectorX weight = mp_nonSmoothForce->calculateTangentialWeight(
		// 	contactInfo, pObjects, vInner, fInner, charMass);
		bool acErrAcpt = sacErrIn - sacErr < 1e-4 * step * gErrAC;
		// &&
		// rfIn.cwiseProduct(weight).squaredNorm() <
		//     4 * rf.cwiseProduct(weight).squaredNorm();
		bool acpt = (inErrAcpt || acErrAcpt);
		if (acpt || (stepIt == maxLineSearch - 1)) {
			if (hasLoggingOption(mp_logging, LoggingOptions::PER_ITER_ERRORS)) {
				std::cout << step << " " << inErr << ruIn.squaredNorm() << " "
						  << rfIn.squaredNorm() << " " << rlIn.squaredNorm()
						  << " " << sErr << std::endl;
			}
			if (acpt) {
				res.newU = vInner;
				res.newF = fInner;
				res.newL = lInner;
				res.stepSize = step;
				res.sErr = inErr;
				res.acErr = sacErrIn;
				return res;
			}
			break;
		}
		step *= 0.5;
	}
	return res;
}
std::string PrimalDualForceSolver::printTimings(size_t totalSteps) {
	std::stringstream ss;

	ss << "\n\tAvg. force calc time per substep: "
	   << m_forceProcessTimer.GetSeconds() / totalSteps
	   << "\n\t\tBuild system: " << m_systemBuildTimer.GetSeconds() / totalSteps
	   << "\n\t\tSolve system: " << m_systemSolveTimer.GetSeconds() / totalSteps
	   << "\n\t\tLine search: " << m_lineSearchTimer.GetSeconds() / totalSteps
	   << "\n\tAverage #iterations: " << (double)m_totalIterations / totalSteps
	   << "\n";

	return ss.str();
}

void PrimalDualForceSolver::fillFromParams(const Params::ForceSolver& params) {
	const Params::PrimalDualForceSolver* paramsCast =
		static_cast<const Params::PrimalDualForceSolver*>(&params);
	m_tol = paramsCast->tolerance;
	m_maxIter = paramsCast->maxIteration;
	std::shared_ptr<Scalar> frictionCoeff = std::make_shared<Scalar>(0.);

	if (paramsCast->p_nonSmoothForce == nullptr) {
		throw std::runtime_error("No non-smooth force defined!");
	}
	if (paramsCast->nonSmoothForceType == NonSmoothForceType::NONE) {
		throw std::runtime_error("Non-smooth force: no name provided!");
	}

	switch (paramsCast->nonSmoothForceType) {
	case NonSmoothForceType::NON_SMOOTH_CONTACTS: {
		mp_nonSmoothForce =
			std::make_unique<Solver::NonSmoothContactForce>(mp_logging);
		auto pForce = dynamic_cast<Solver::NonSmoothContactForce*>(
			mp_nonSmoothForce.get());
		frictionCoeff = pForce->mp_frictionCoeff;
		break;
	}
	case NonSmoothForceType::NON_SMOOTH_CONTACTS_NORMALIZED: {
		mp_nonSmoothForce =
			std::make_unique<Solver::NormalizedContactForce>(mp_logging);
		auto pForce = dynamic_cast<Solver::NormalizedContactForce*>(
			mp_nonSmoothForce.get());
		frictionCoeff = pForce->mp_frictionCoeff;
		break;
	}
	case NonSmoothForceType::ONLY_NORMAL_FORCE: {
		mp_nonSmoothForce =
			std::make_unique<Solver::OnlyNormalForce>(mp_logging);
		break;
	}
	case NonSmoothForceType::SECOND_ORDER_CONE: {
		mp_nonSmoothForce =
			std::make_unique<Solver::SecondOrderConeForce>(mp_logging);
		auto pForce = dynamic_cast<Solver::SecondOrderConeForce*>(
			mp_nonSmoothForce.get());
		frictionCoeff = pForce->mp_frictionCoeff;
		break;
	}
	default:
		throw std::runtime_error("Non-smooth force: no valid name provided!");
	}

	mp_nonSmoothForce->fillFromParams(*paramsCast->p_nonSmoothForce);
}
}  // namespace Solver
}  // namespace FrictionFrenzy
