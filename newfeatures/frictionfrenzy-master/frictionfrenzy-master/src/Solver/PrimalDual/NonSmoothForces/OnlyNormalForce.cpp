#include "OnlyNormalForce.h"

namespace FrictionFrenzy {
namespace Solver {
void OnlyNormalForce::preprocess(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed) {
	const size_t n_contacts = contactInfo.size();
	m_constraintVals.resize(n_contacts);
	m_nonSmoothK = VectorX::Zero(n_contacts);
	m_invConstraintVals = VectorX::Zero(n_contacts);
	m_currAvgMass = charMass;
	m_compliance.resize(n_contacts);
	m_reduction.resize(n_contacts);

	VectorX tk(n_contacts), damp(n_contacts);

	// Scalar damp = m_springDamp * m_springK;
	// Scalar tk = timestep * m_springK;
	if (m_areaBasedK && m_springBasedForce) {
#pragma omp parallel for
		for (size_t i = 0; i < n_contacts; ++i) {
			Scalar k = m_springK * contactInfo[i].area;
			tk[i] = k * timestep;
			damp[i] = k * m_springDamp;
		}
	} else {
		tk.setConstant(m_springK * timestep);
		damp.setConstant(m_springDamp * m_springK);
	}

	m_compliance = 1. / (timestep * (tk + damp).array());
	m_reduction = tk.array() / (tk + damp).array();

	// Scalar damp = m_springDamp * m_springK;
	// m_compliance = 1. / (timestep * (timestep * m_springK + damp));
	// m_reduction = (timestep * m_springK) / (timestep * m_springK + damp);

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		if (m_springBasedForce) {
			Scalar red =
				-m_reduction[i] * contactInfo[i].depth / timestep / charSpeed;
			m_nonSmoothK(i) += red;
		} else {
			Vector3 hu = contactInfo[i].toLocal(vels);
			m_nonSmoothK(i) += hu(0) * m_restitution;
		}
	}
}
void OnlyNormalForce::initForces(
	const std::vector<ContactInformation>& contactInfo,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed,
	VectorX& vels,
	VectorX& forces,
	VectorX& lambda) {
	forces = VectorX::Ones(forces.size());
	lambda.setConstant(1e-2);
};
void OnlyNormalForce::calculateConstraints(
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda) {
	m_constraintVals = -forces;
}
void OnlyNormalForce::nonSmoothResiduals(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda,
	const Scalar mu,
	const bool useStoredConstraints,
	VectorX& ru,
	VectorX& rf,
	VectorX& rl) {
	ru = VectorX::Zero(objects.size() * 6);
	rf = VectorX::Zero(contactInfo.size());
	rl = VectorX::Zero(contactInfo.size());

#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Scalar f = forces[i];
		rf[i] = -contactInfo[i].toNormal(vels);
		for (int j = 0; j < 2; ++j) {
			const int id = contactInfo[i].objId[j];
			const auto& obj = *objects[id];
			Vector6 hTf = contactInfo[i].toGlobalNormal(j, f);
			if (obj.isActive()) {
				for (int k = 0; k < 6; ++k) {
#pragma omp atomic
					ru[id * 6 + k] -= hTf[k];
				}
			}
		}
		if (m_springBasedForce) {
			rf(i) -= m_compliance[i] * m_currAvgMass * f;
		}

		rf(i) += lambda[i];
	}
	rf -= m_nonSmoothK;
	if (useStoredConstraints) {
		rl = lambda.cwiseProduct(m_constraintVals).array() + mu;
	} else {
		VectorX c = -forces;
		rl = lambda.cwiseProduct(c).array() + mu;
	}
}
void OnlyNormalForce::linsysAddition(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> lambda,
	const Eigen::Ref<const VectorX> rf,
	const Eigen::Ref<const VectorX> rl,
	Scalar eps,
	VectorX& y,
	std::unordered_map<std::pair<size_t, size_t>, Scalar*>& matPointers) {
	const size_t n_contacts = contactInfo.size();

	m_sf = rf;
	VectorX sfAdd(rf.size());
	VectorX lMats(contactInfo.size());
	m_invConstraintVals = 1. / (m_constraintVals.array() - eps);

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		Scalar reg = -lambda[i] * m_invConstraintVals[i];
		if (m_springBasedForce) {
			reg += m_compliance[i] * m_currAvgMass;
		}
		lMats[i] = reg;
		sfAdd(i) = -rl(i) * m_invConstraintVals[i];
	}
	m_sf += sfAdd;
	m_invK = VectorX::Zero(n_contacts);

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		Scalar reg = eps + lMats[i];
		m_invK[i] = 1. / reg;
		Scalar kInvSf = m_invK[i] * m_sf(i);
		for (int j = 0; j < 2; ++j) {
			int id1 = contactInfo[i].objId[j];
			if (objects[id1]->isStatic()) {
				continue;
			}
			Vector6 trans1 = contactInfo[i].getTrans(j).col(0);
			Vector6 yadd_block = trans1 * kInvSf;
			for (int k = 0; k < 6; ++k) {
#pragma omp atomic
				y(id1 * 6 + k, 0) += yadd_block(k);
			}

			for (int k = 0; k < 2; ++k) {
				int id2 = contactInfo[i].objId[k];
				if (objects[id2]->isActive()) {
					Vector6 trans2 = contactInfo[i].getTrans(k).col(0);
					Matrix6 massBlock = trans1 * m_invK[i] * trans2.transpose();
					for (int row = 0; row < 6; ++row) {
						for (int col = 0; col < 6; ++col) {
#pragma omp atomic
							(*matPointers[{id1 * 6 + row, id2 * 6 + col}]) +=
								massBlock(row, col);
						}
					}
				}
			}
		}
	}
}
void OnlyNormalForce::retrieveNonSmoothForceInc(
	const std::vector<ContactInformation>& contactInfo,
	const Eigen::Ref<const VectorX> lambda,
	const Eigen::Ref<const VectorX> du,
	const Eigen::Ref<const VectorX> rf,
	const Eigen::Ref<const VectorX> rl,
	const Scalar mu,
	VectorX& df,
	VectorX& dl) {
	df = VectorX::Zero(contactInfo.size());
	dl = VectorX::Zero(contactInfo.size());
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Scalar dfi = m_sf(i) - contactInfo[i].toNormal(du);
		dfi *= m_invK[i];
		df(i) = dfi;

		dl(i) = -m_invConstraintVals[i] * (-lambda[i] * dfi + rl(i));
	}
}
bool OnlyNormalForce::filterLineSearch(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> velsOld,
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda,
	Scalar mu,
	Scalar charMass,
	VectorX& du,
	VectorX& df,
	VectorX& dl) {
	bool projected = false;
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Scalar cf = forces(i);
		Scalar dfi = df(i);
		Scalar tf = cf + dfi;

		if (tf < 0) {
			tf = 0;
			df(i) = tf - cf;
			projected = true;
		}

		if (dl(i) < -lambda(i)) {
			dl(i) = -lambda(i);
		}
	}
	return projected;
}
VectorX OnlyNormalForce::ACVector(
	const std::vector<ContactInformation>& contactInfo,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces) const {
	VectorX acVec = VectorX::Zero(forces.size());
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Scalar localU = contactInfo[i].toNormal(vels);
		Scalar toProjectN = forces(i) - (localU + m_nonSmoothK(i) +
		                                 m_springBasedForce * m_compliance[i] *
		                                     m_currAvgMass * forces(i));
		acVec(i) = std::max(toProjectN, Scalar(0)) - forces(i);
	}
	return acVec;
}
void OnlyNormalForce::fillContactForces(
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda,
	const Scalar charMass,
	const Scalar charSpeed,
	const Scalar tolerance,
	const Scalar timestep,
	std::vector<ContactInformation>& contactInfo) {
	// Write new forces
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		contactInfo[i].localForce
			<< forces(i) * charSpeed * charMass / timestep,
			0, 0;
		contactInfo[i].isDynamic = true;
	}
}
void OnlyNormalForce::fillFromParams(const Params::NonSmoothForce &params) {
	const Params::OnlyNormalForce* paramsCast =
		static_cast<const Params::OnlyNormalForce*>(&params);
	m_springBasedForce = paramsCast->springBasedForce;
	if (m_springBasedForce) {
		m_areaBasedK = paramsCast->areaBasedSpring;
		m_springK = paramsCast->springK;
		m_springDamp = paramsCast->springDamp;
	} else {
		m_restitution = paramsCast->restitution;
	}
}
}  // namespace Solver
}  // namespace FrictionFrenzy
