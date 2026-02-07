#include "NormalizedContactForce.h"
#include "Common/MatrixTypes.h"
#include "Solver/PrimalDual/NonSmoothForces/NonSmoothForceBase.h"
namespace FrictionFrenzy {
namespace Solver {
void NormalizedContactForce::preprocess(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed) {
	const size_t n_contacts = contactInfo.size();
	m_constraintVals.resize(2 * n_contacts);
	m_gradients.resize(n_contacts, 2);
	m_hessians.resize(n_contacts * 2, 2);
	m_nonSmoothK = VectorX::Zero(n_contacts * 3);
	m_KnormInv.resize(n_contacts);
	m_KmatSVD.resize(n_contacts);
	m_WeightMat.resize(n_contacts);
	m_tanWeight = VectorX::Ones(n_contacts);
	m_invConstraintVals = VectorX::Zero(n_contacts * 2);
	m_currAvgMass = charMass;
	m_currIter = 0;

	Scalar damp = m_springDamp * m_springK;

	Scalar tk = timestep * m_springK;
	m_compliance = 1. / (timestep * (tk + damp));
	m_reduction = tk / (tk + damp);

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		if (m_springBasedForce) {
			Scalar red =
				-m_reduction * contactInfo[i].depth / timestep / charSpeed;
			m_nonSmoothK(i * 3) += red;
		} else {
			Vector3 hu = Vector3::Zero();
			hu = contactInfo[i].toLocal(vels);
			m_nonSmoothK(i * 3) += hu(0) * m_restitution;
		}
	}
}
void NormalizedContactForce::initForces(
	const std::vector<ContactInformation>& contactInfo,
	const Scalar timestep,
	const Scalar charMass,
	const Scalar charSpeed,
	VectorX& vels,
	VectorX& forces,
	VectorX& lambda) {
	forces.reshaped(3, forces.size() / 3).colwise() = Vector3(1, 0, 0);
	lambda.setConstant(1e-2);
}
VectorX NormalizedContactForce::ACVector(
	const std::vector<ContactInformation>& contactInfo,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces) const {
	VectorX acVec = VectorX::Zero(forces.size());
	acVec.setConstant(std::numeric_limits<Scalar>::infinity());
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector3 localU = contactInfo[i].toLocal(vels);
		Scalar toProjectN = forces(3 * i) - (localU(0) + m_nonSmoothK(3 * i) +
		                                     m_springBasedForce * m_compliance *
		                                         m_currAvgMass * forces(3 * i));
		acVec(3 * i) = std::max(toProjectN, Scalar(0)) - forces(3 * i);

		Scalar r = forces(3 * i) * *mp_frictionCoeff;
		Vector2 localTan = forces.segment<2>(3 * i + 1) * r;
		Vector2 tDiff = localTan - localU.tail(2);
		Vector2 proj = (tDiff.norm() < r) ? tDiff : tDiff * r / tDiff.norm();
		acVec.segment<2>(3 * i + 1) = (proj - localTan);
	}
	return acVec;
}
VectorX NormalizedContactForce::calculateTangentialWeight(
	const std::vector<ContactInformation>& contactInfo,
	const std::vector<RigidObjectBase*>& objects,
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Scalar charMass) {
	VectorX fWeight = VectorX::Ones(forces.size());
	// #pragma omp parallel for
	// 	for (int i = 0; i < contactInfo.size(); ++i) {
	// 		FloatType w =
	// 			1 / std::max(*mp_frictionCoeff * forces(3 * i), FloatType(1));
	// 		fWeight.segment<2>(3 * i + 1).setConstant(w);
	// 	}
	return fWeight;
};
void NormalizedContactForce::calculateConstraints(
	const Eigen::Ref<const VectorX> vels,
	const Eigen::Ref<const VectorX> forces,
	const Eigen::Ref<const VectorX> lambda) {
#pragma omp parallel for
	for (int i = 0; i < forces.size() / 3; ++i) {
		const Vector3& f = forces.segment<3>(i * 3);
		m_constraintVals[2 * i] = -f[0];

		m_constraintVals[2 * i + 1] = mp_constraint->constraint(f);
		m_gradients.row(i) = mp_constraint->gradient(f).transpose();
		m_hessians.block<2, 2>(i * 2, 0) = mp_constraint->hessian(f);

		Scalar newTan = f(0) * *mp_frictionCoeff;

		m_tanWeight(i) = 1.0 * newTan;  // - 0.1 * m_tanWeight(i);
	}
	m_currIter++;
	m_tanWeight = m_tanWeight.cwiseMax(0);
}
void NormalizedContactForce::nonSmoothResiduals(
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

#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector3 fReal = forces.segment<3>(i * 3);
		Vector3 f = forces.segment<3>(i * 3);

		Scalar fw = m_tanWeight(i);
		if (!useStoredConstraints) {
			Scalar newTan = f(0) * *mp_frictionCoeff;
			fw = 1.0 * newTan;  // - 0.1 * fw;
		}
		f.tail<2>() *= fw;
		rf.segment<3>(3 * i) -= contactInfo[i].toLocal(vels);
		rf.segment<2>(3 * i + 1) *= fw;
		for (int j = 0; j < 2; ++j) {
			const int id = contactInfo[i].objId[j];
			const auto& obj = *objects[id];
			Vector6 hTf = -contactInfo[i].toGlobal(j, f);
			if (obj.isActive()) {
				for (int rui = 0; rui < 6; ++rui) {
#pragma omp atomic
					ru[id * 6 + rui] += hTf[rui];
				}
			}
		}
		if (m_springBasedForce) {
			rf(3 * i) -= m_compliance * m_currAvgMass * f[0];
		}

		rf(3 * i) += lambda[2 * i];
		const Vector2& grad = (useStoredConstraints)
		                          ? m_gradients.row(i).transpose()
		                          : mp_constraint->gradient(fReal);
		rf.segment<2>(3 * i + 1) -= lambda[2 * i + 1] * grad;
	}
	rf -= m_nonSmoothK;
	if (useStoredConstraints) {
		rl = lambda.cwiseProduct(m_constraintVals).array() + mu;
	} else {
		VectorX c(contactInfo.size() * 2);
#pragma omp parallel for
		for (size_t i = 0; i < contactInfo.size(); ++i) {
			const Vector3& f = forces.segment<3>(i * 3);
			c[2 * i] = -f[0];
			c[2 * i + 1] = mp_constraint->constraint(f);
		}
		rl = lambda.cwiseProduct(c).array() + mu;
	}
}
void NormalizedContactForce::linsysAddition(
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
	std::vector<Matrix2> lMats(n_contacts, Matrix2::Zero());
	VectorX lNorms(n_contacts);
	VectorX sfAdd(rf.size());
	sfAdd.setZero();
	m_invConstraintVals =
		1. / (m_constraintVals.array() - eps * lambda.array());

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		const Vector2& grad = m_gradients.row(i).transpose();
		lNorms[i] = -lambda[2 * i] * m_invConstraintVals[2 * i];
		if (m_springBasedForce) {
			lNorms[i] += m_compliance * m_currAvgMass;
		}
		lMats[i] = -lambda[2 * i + 1] * m_invConstraintVals[2 * i + 1] * grad *
		           grad.transpose();
		sfAdd(3 * i) = -rl(2 * i) * m_invConstraintVals[2 * i];
		sfAdd.segment<2>(3 * i + 1) =
			grad * rl(2 * i + 1) * m_invConstraintVals[2 * i + 1];
	}
	m_sf += sfAdd;

#pragma omp parallel for
	for (size_t i = 0; i < n_contacts; ++i) {
		Scalar regN = eps + lNorms[i];
		m_KnormInv[i] = 1. / regN;
		Matrix2 reg;
		reg = Matrix2::Identity() * (eps);
		reg += lMats[i];
		reg += lambda[2 * i + 1] * m_hessians.block<2, 2>(i * 2, 0);
		m_KmatSVD[i].compute(reg, Eigen::ComputeFullU | Eigen::ComputeFullV);

		Vector3 kInvSf = Vector3::Zero();
		kInvSf(0) = m_sf(i * 3) * m_KnormInv[i];
		kInvSf.tail<2>() =
			m_KmatSVD[i].solve(m_sf.segment<2>(i * 3 + 1)) * m_tanWeight(i);
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
					Matrix6 massBlock = trans1.col(0) * m_KnormInv[i] *
					                    trans2.col(0).transpose();
					massBlock += trans1.block<6, 2>(0, 1) *
					             m_KmatSVD[i].solve(
									 trans2.block<6, 2>(0, 1).transpose()) *
					             m_tanWeight[i] * m_tanWeight[i];
					for (int row = 0; row < 6; ++row) {
						for (int col = 0; col < 6; ++col) {
#pragma omp atomic
							*(matPointers[{id1 * 6 + row, id2 * 6 + col}]) +=
								massBlock(row, col);
						}
					}
				}
			}
		}
	}
	return;
}
void NormalizedContactForce::retrieveNonSmoothForceInc(
	const std::vector<ContactInformation>& contactInfo,
	const Eigen::Ref<const VectorX> lambda,
	const Eigen::Ref<const VectorX> du,
	const Eigen::Ref<const VectorX> rf,
	const Eigen::Ref<const VectorX> rl,
	const Scalar mu,
	VectorX& df,
	VectorX& dl) {
	df = VectorX::Zero(contactInfo.size() * 3);
	dl = VectorX::Zero(contactInfo.size() * 2);
#pragma omp parallel for
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		Vector3 dfi = m_sf.segment<3>(i * 3);
		Vector3 dv = contactInfo[i].toLocal(du);
		dv.tail<2>() *= m_tanWeight[i];
		dfi -= dv;
		dfi(0) = m_KnormInv[i] * dfi(0);
		dfi.tail<2>() = m_KmatSVD[i].solve(dfi.tail<2>());
		df.segment<3>(i * 3) = dfi;

		dl(2 * i) =
			-m_invConstraintVals[2 * i] * (-lambda[2 * i] * dfi[0] + rl(2 * i));
		dl(2 * i + 1) =
			-m_invConstraintVals[2 * i + 1] *
			(lambda[2 * i + 1] * m_gradients.row(i).dot(dfi.tail(2)) +
		     rl(2 * i + 1));
	}
}
bool NormalizedContactForce::filterLineSearch(
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
		const Vector3& cf = forces.segment<3>(i * 3);
		const Vector3& dfi = df.segment<3>(i * 3);
		Vector3 tf = cf + dfi;

		if (tf[0] < 0) {
			tf[0] = 0.1 * cf[0];
			df.segment<3>(i * 3) = tf - cf;
			projected = true;
		}
		Scalar co = mp_constraint->constraint(tf);
		if (co > 0) {
			Scalar cc = 0.1 * mp_constraint->constraint(cf);
			tf = mp_constraint->project(tf, tf, cc);
			df.segment<3>(i * 3) = tf - cf;
			projected = true;
		}
	}
#pragma omp parallel for
	for (size_t i = 0; i < 2 * contactInfo.size(); ++i) {
		if (dl[i] < 0 && lambda[i] + dl[i] < 0) {
			dl[i] = -lambda[i];
		}
	}
	return projected;
}
void NormalizedContactForce::fillContactForces(
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
		contactInfo[i].localForce.tail<2>() *=
			forces(i * 3) * *mp_frictionCoeff;
		contactInfo[i].isDynamic = (lambda(i) > tolerance);
	}
}
void NormalizedContactForce::fillFromParams(
	const Params::NonSmoothForce& params) {
	const Params::NormalizedContactForce* paramsCast =
		static_cast<const Params::NormalizedContactForce*>(&params);
	m_springBasedForce = paramsCast->springBasedForce;
	if (m_springBasedForce) {
		m_springK = paramsCast->springK;
		m_springDamp = paramsCast->springDamp;
	} else {
		m_restitution = paramsCast->restitution;
	}
	*mp_frictionCoeff = paramsCast->frictionCoeff;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
