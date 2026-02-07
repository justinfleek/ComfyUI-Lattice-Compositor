#include "SecondOrderConeForce.h"
#include "Solver/PrimalDual/NonSmoothForces/NonSmoothForceBase.h"
namespace FrictionFrenzy {
namespace Solver {
void SecondOrderConeForce::preprocess(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed) {
	const size_t n_contacts = contactInfo.size();
	m_constraintVals.resize(n_contacts);
	m_gradients.resize(n_contacts, 3);
	m_hessians.resize(n_contacts * 3, 3);
	m_nonSmoothK = VectorX::Zero(n_contacts * 3);
	m_KmatSVD.resize(n_contacts);

	for (size_t i = 0; i < n_contacts; ++i) {
		Vector3 hu = contactInfo[i].toLocal(vels);
		m_nonSmoothK(i * 3) += hu(0) * m_restitution;
	}
}
void SecondOrderConeForce::initForces(
	const std::vector<ContactInformation>& contactInfo,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed,
	VectorX& vels,
	VectorX& forces,
	VectorX& lambda) {
	forces = VectorX::Zero(forces.size());
	lambda.array() = 1e-2;
	for (int i = 0; i < lambda.size(); ++i) {
		forces[i * 3] = 1;
	}
}
VectorX SecondOrderConeForce::calculateTangentialWeight(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Scalar charMass) {
	VectorX fWeight = VectorX::Ones(forces.size());
	Scalar div = 0;
#pragma omp declare reduction(maximum:Scalar                         \
                              : omp_out = std::max(omp_out, omp_in)) \
	initializer(omp_priv = 0)
#pragma omp parallel for reduction(maximum : div)
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector2 tanVel = contactInfo[i].toTangent(vels);
		Scalar frictionWeight = 0;
		for (int j = 0; j < 2; ++j) {
			int oId = contactInfo[i].objId[j];
			if (objects[oId]->isActive()) {
				Vector6 hh = -contactInfo[i].toGlobalTangent(
					j, tanVel.tail<2>().normalized());
				frictionWeight +=
					hh.dot(objects[oId]->invGenMassMat() * hh) * charMass;
			}
		}
		Scalar fricRadius = mp_constraint->radiusAt(forces[3 * i]);
		Scalar contactWeight = std::min(
			fricRadius / (tanVel.norm() + 1e-8) * frictionWeight, Scalar(1));
		fWeight.block<2, 1>(3 * i + 1, 0).setConstant(contactWeight);
		div = std::max(div, contactWeight);
	}
	return fWeight;
}
void SecondOrderConeForce::calculateConstraints(
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda) {
	for (int i = 0; i < lambda.size(); ++i) {
		const Vector3& f = forces.segment<3>(i * 3);
		Scalar c = mp_constraint->constraint(f);
		Vector3 grad = mp_constraint->gradient(f);
		Matrix3 hess = mp_constraint->hessian(f);
		m_constraintVals[i] = c;
		m_gradients.row(i) = grad.transpose();
		m_hessians.block<3, 3>(i * 3, 0) = hess;
	}
}
void SecondOrderConeForce::nonSmoothResiduals(
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
	rf = VectorX::Zero(contactInfo.size() * 3);
	rl = VectorX::Zero(contactInfo.size());

	for (size_t i = 0; i < contactInfo.size(); ++i) {
		const Vector3& f = forces.segment<3>(i * 3);
		rf.segment<3>(3 * i) -= contactInfo[i].toLocal(vels);
		for (int j = 0; j < 2; ++j) {
			const int id = contactInfo[i].objId[j];
			const auto& obj = *objects[id];
			Vector6 hTf = -contactInfo[i].toGlobal(j, f);
			if (obj.isActive()) {
				ru.block<6, 1>(id * 6, 0) += hTf;
			}
		}
		const Vector3& grad = (useStoredConstraints)
		                          ? m_gradients.row(i).transpose()
		                          : mp_constraint->gradient(f);
		rf.segment<3>(3 * i) -= lambda[i] * grad;
	}
	rf -= m_nonSmoothK;
	if (useStoredConstraints) {
		rl = lambda.cwiseProduct(m_constraintVals).array() + mu;
	} else {
		VectorX c(contactInfo.size());
		for (size_t i = 0; i < contactInfo.size(); ++i) {
			c[i] = mp_constraint->constraint(forces.segment<3>(i * 3));
		}
		rl = lambda.cwiseProduct(c).array() + mu;
	}
}
void SecondOrderConeForce::linsysAddition(
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
	std::vector<Matrix3> lMats(n_contacts);
	m_invConstraints = VectorX::Ones(n_contacts).array() /
	                   (m_constraintVals.array() - eps * lambda.array());

	VectorX sfAdd(n_contacts * 3);
	for (size_t i = 0; i < n_contacts; ++i) {
		const Vector3& grad = m_gradients.row(i).transpose();
		Matrix3 reg =
			lambda[i] * -m_invConstraints[i] * grad * grad.transpose();
		lMats[i] = reg;
		sfAdd.segment<3>(i * 3) = grad * m_invConstraints(i) * rl(i);
	}
	m_sf += sfAdd;
#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		Matrix3 reg = Matrix3::Identity() * (eps);
		reg += lMats[i];
		reg += lambda[i] * m_hessians.block<3, 3>(i * 3, 0);
		m_KmatSVD[i].compute(reg, Eigen::ComputeThinU | Eigen::ComputeThinV);

		Vector3 kInvSf = m_KmatSVD[i].solve(m_sf.block<3, 1>(i * 3, 0));
		for (int j = 0; j < 2; ++j) {
			int id1 = contactInfo[i].objId[j];
			if (objects[id1]->isStatic()) {
				continue;
			}
			const auto& trans1 = contactInfo[i].getTrans(j);
			Vector6 yadd_block = trans1 * kInvSf;
			for (int k = 0; k < 6; ++k) {
#pragma omp atomic
				y(id1 * 6 + k, 0) += yadd_block(k);
			}

			for (int k = 0; k < 2; ++k) {
				int id2 = contactInfo[i].objId[k];
				if (objects[id2]->isActive()) {
					const auto& trans2 = contactInfo[i].getTrans(k);
					Matrix6 massBlock =
						trans1 * m_KmatSVD[i].solve(trans2.transpose());
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
void SecondOrderConeForce::retrieveNonSmoothForceInc(
	const std::vector<ContactInformation>& contactInfo,
	const Eigen::Ref<const VectorX> lambda,
	const Eigen::Ref<const VectorX> du,
	const Eigen::Ref<const VectorX> rf,
	const Eigen::Ref<const VectorX> rl,
	const Scalar mu,
	VectorX& df,
	VectorX& dl) {
	df = VectorX::Zero(contactInfo.size() * 3);
	dl = VectorX::Zero(contactInfo.size());
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector3 dfi = m_sf.block<3, 1>(i * 3, 0);
		dfi -= contactInfo[i].toLocal(du);
		dfi = m_KmatSVD[i].solve(dfi);
		df.segment<3>(i * 3) = dfi;
	}
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		dl(i) = m_gradients.row(i) * df.segment<3>(i * 3);
	}
	dl = -m_invConstraints.cwiseProduct(dl.cwiseProduct(lambda) + rl);
}
bool SecondOrderConeForce::filterLineSearch(
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
	Scalar minStep = 1.0;
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector3 cf = forces.segment<3>(i * 3);
		Vector3 dfi = df.segment<3>(i * 3) * minStep;
		Vector3 tf = cf + dfi;

		Scalar co = mp_constraint->constraint(tf);
		if (co > 0) {
			Vector3 pf = mp_constraint->project(tf, tf, 0.0);
			df.segment<3>(i * 3) = pf - cf;
			projected = true;
		}
	}
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		if (dl[i] < 0 && lambda[i] + dl[i] < 0) {
			dl[i] = -lambda[i];
		}
	}
	return projected;
}
void SecondOrderConeForce::fillContactForces(
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
		contactInfo[i].localForce =
			forces.segment<3>(i * 3) * charSpeed * charMass / timestep;
		contactInfo[i].isDynamic = (lambda(i) > tolerance);
	}
}

void SecondOrderConeForce::fillFromParams(
	const Params::NonSmoothForce& params) {
	const Params::SecondOrderConeForce* paramsCast =
		static_cast<const Params::SecondOrderConeForce*>(&params);
	m_restitution = paramsCast->restitution;
	*mp_frictionCoeff = paramsCast->frictionCoeff;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
