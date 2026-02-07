#pragma once

#include "../ForceSolverBase.h"
#include "Common/MatrixTypes.h"
#include "Common/Timer.h"
#include "NonSmoothForces/NonSmoothForces.h"
#include "SmoothForces/SmoothForces.h"

namespace FrictionFrenzy {
namespace Params {
struct PrimalDualForceSolver : public ForceSolver {
	Scalar tolerance;
	int maxIteration;
	Solver::NonSmoothForceType nonSmoothForceType;
	std::unique_ptr<NonSmoothForce> p_nonSmoothForce;
	std::vector<Solver::SmoothForceType> smoothForceTypes;
	std::vector<std::unique_ptr<SmoothForce>> p_smoothForceParams;
};
}  // namespace Params

namespace Solver {
class PrimalDualForceSolver : public ForceSolver {
   public:
	/**
	 * Constructor
	 */
	PrimalDualForceSolver(std::shared_ptr<unsigned int> logging)
		: ForceSolver(logging) {}

	/* Inherited from `Configurable` */
	void fillFromParams(const Params::ForceSolver& params) override;

	/* Inherited from `ForceSolver` */
	void reset() override {
		m_forceProcessTimer.Reset();
		m_systemBuildTimer.Reset();
		m_systemSolveTimer.Reset();
		m_lineSearchTimer.Reset();
		m_totalIterations = 0;
	}

	/* Inherited from `ForceSolver` */
	ForceSolverType getType() override { return ForceSolverType::PrimalDual; }

	/* Inherited from `ForceSolver` */
	void fillForces(
		const Scalar timestep,
		const Vector3& gravity,
		std::vector<ContactInformation>& contactInfo,
		std::vector<std::unique_ptr<RigidObjectBase>>& objects) override;

	/* Inherited from `ForceSolver` */
	std::string printTimings(size_t totalSteps) override;

	/// Accessors
	/**
	 * Return maximum iterations
	 */
	int& maxIter() { return m_maxIter; }
	/**
	 * Return tolerence
	 */
	Scalar& tolerance() { return m_tol; }
	/**
	 * Return non-smooth force
	 */
	NonSmoothForceBase* nonSmoothForce() { return mp_nonSmoothForce.get(); }
	/**
	 * Return smooth force
	 */
	std::vector<std::unique_ptr<SmoothForceBase>>& smoothForces() {
		return m_smoothForces;
	}

   protected:
	/**
	 * Struct for line search results after Newton solves.
	 */
	struct LineSearchResult {
		VectorX newU;
		VectorX newF;
		VectorX newL;
		Scalar stepSize;
		Scalar sErr;
		Scalar acErr;
	};

	/**
	 * @brief Internal implementation of force computation.
	 *
	 * @param[in] timestep: The timestep size
	 * @param[in] gravity: The acceleration from gravity
	 * @param[in, out] contactInfo: The list of contacts
	 * @param[in, out] objects: The list of objects.
	 */
	void fillForcesIntl(const Scalar timestep,
	                    const Vector3& gravity,
	                    std::vector<ContactInformation>& contactInfo,
	                    std::vector<RigidObjectBase*>& pObjects);

	/**
	 * @brief Return the characteristic mass and speed.
	 *
	 * @param[in] timestep: The current timestep size.
	 * @param[in] gravity: The acceleration from gravity.
	 * @param[in] contactInfo: The list of contacts.
	 * @param[in] pObjects: The list of rigid body objects (pointers)
	 *
	 * @return A tuple containing (in order) the characteristic mass and speed.
	 */
	std::tuple<Scalar, Scalar> nonDimensionalParams(
		const Scalar timestep,
		const Vector3& gravity,
		const std::vector<ContactInformation>& contactInfo,
		const std::vector<RigidObjectBase*>& pObjects);

	/**
	 * @brief Calculate residuals.
	 */
	template <typename D>
	void calculateResiduals(bool useStoredConstraints,
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
	                        Eigen::MatrixBase<D>& rl);

	/**
	 * @brief Given a line search direction, find a suitable step size and
	 * projected step direction.
	 */
	LineSearchResult lineSearch(
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
		const int maxLineSearch);

	/**
	 * @brief Calculate the residual error for line searching, given the
	 * residuals.
	 */
	Scalar searchError(Eigen::Ref<const VectorX> ru,
	                   Eigen::Ref<const VectorX> wrf,
	                   Eigen::Ref<const VectorX> rl) {
		// return (ru.squaredNorm() / ru.size() + wrf.squaredNorm() / wrf.size()
		// + rl.squaredNorm() / rl.size());
		return (ru.squaredNorm() + wrf.squaredNorm() + rl.squaredNorm());
	}

	/**
	 * @brief Calculate the residual error for line searching, given the
	 * residuals and Alart-Cournier errors.
	 */
	Scalar searchACError(Eigen::Ref<const VectorX> ru,
	                     Eigen::Ref<const VectorX> ac,
	                     Eigen::Ref<const VectorX> rl) {
		return (ru.squaredNorm() + ac.squaredNorm() + rl.squaredNorm());
	}

	int m_maxIter = 100;
	Scalar m_tol = 1e-6;

	Timer m_forceProcessTimer;
	Timer m_systemBuildTimer;
	Timer m_systemSolveTimer;
	Timer m_lineSearchTimer;
	size_t m_totalIterations = 0;

	std::unique_ptr<NonSmoothForceBase> mp_nonSmoothForce;
	std::vector<std::unique_ptr<SmoothForceBase>> m_smoothForces;
	std::unordered_map<std::pair<size_t, size_t>, std::pair<Scalar, Scalar>>
		m_contactCache, m_contactCacheLocal;
};
}  // namespace Solver
}  // namespace FrictionFrenzy
