#pragma once

#include <memory>
#include <vector>

#include "CollisionObject/RigidObjectBase.h"
#include "Common/MatrixTypes.h"
#include "Contact/ContactInfo.h"

namespace FrictionFrenzy {
namespace Params {
	struct ForceSolver {};
}

namespace Solver {
using CollisionObject::RigidObjectBase;
using Contact::ContactInformation;

typedef Eigen::ConjugateGradient<SparseMat, Eigen::Lower | Eigen::Upper> CG;
typedef Eigen::SimplicialLDLT<SparseMat> LDLT;

enum ForceSolverType { Null, GaussSeidel, PrimalDual };

inline VectorX objToContact(std::vector<ContactInformation>& contactInfo,
                            const Eigen::Ref<const VectorX>& vels,
                            const std::array<bool, 3>& usedDims) {
	const int nDims = usedDims[0] + usedDims[1] + usedDims[2];
	VectorX res(contactInfo.size() * nDims);
	res.setZero();
	Eigen::Matrix<Scalar, -1, 3> a(nDims, 3);
	a.setZero();
	int rDim = 0;
	for (int d = 0; d < 3; ++d) {
		if (usedDims[d]) {
			a(rDim, d) = 1;
			rDim++;
		}
	}
	for (size_t i = 0; i < contactInfo.size(); ++i) {
		res.segment(i * nDims, nDims) += a * contactInfo[i].toLocal(vels);
	}
	return res;
}

/**
 * A base clase for contact force solvers.
 */
class ForceSolver {
   public:
	/**
	 * @brief Contructor for force class.
	 *
	 * @param[in] logging: Pointer to logging parameter
	 */
	ForceSolver(std::shared_ptr<unsigned int> logging) : mp_logging(logging) {}

	/**
	 * Destructor
	 */
	virtual ~ForceSolver() {}

	virtual void fillFromParams(const Params::ForceSolver &params) = 0;

	/**
	 * Get force solver type.
	 *
	 * @return the enumerator for the force solver type.
	 */
	virtual ForceSolverType getType() = 0;

	/**
	 * Reset the force solver.
	 */
	virtual void reset() = 0;

	/**
	 * Calculate the contact forces and record then in `contactInfo` and
	 * `objects`.
	 *
	 * @param[in] timestep: The timestep size
	 * @param[in] gravity: The acceleration from gravity
	 * @param[in, out] contactInfo: The list of contacts
	 * @param[in, out] objects: The list of objects.
	 */
	virtual void fillForces(
		const Scalar timestep,
		const Vector3& gravity,
		std::vector<ContactInformation>& contactInfo,
		std::vector<std::unique_ptr<RigidObjectBase>>& objects) = 0;

	/**
	 * Print the timeing of calculations.
	 * @param[in] totalSteps: The number of total steps to calculate an average.
	 */
	virtual std::string printTimings(size_t totalSteps) = 0;

	/// The logging parameter.
	std::shared_ptr<unsigned int> mp_logging;

	// void saveContactCache(FloatType timestep,
	//                       std::vector<ContactInformation> &m_contactInfo);
	// void loadContactCache(FloatType timestep,
	//                       std::vector<ContactInformation> &m_contactInfo);
};
/**
 * A force solver that does nothing. Solely for debugging.
 */
class NullForceSolver : public ForceSolver {
   public:
	/**
	 * @brief Contructor for force class.
	 *
	 * @param[in] logging: Pointer to logging parameter
	 */
	NullForceSolver(std::shared_ptr<unsigned int> logging)
		: ForceSolver(logging) {}

	/**
	 * Destructor
	 */
	~NullForceSolver() override {}
	void fillFromParams(const Params::ForceSolver &params) override {}

	/**
	 * Get force solver type.
	 *
	 * @return the enumerator for the force solver type.
	 */
	ForceSolverType getType() override { return ForceSolverType::Null; }

	/**
	 * Reset the force solver.
	 */
	void reset() override {}

	/**
	 * Calculate the contact forces and record then in `contactInfo` and
	 * `objects`.
	 *
	 * @param[in] timestep: The timestep size
	 * @param[in] gravity: The acceleration from gravity
	 * @param[in, out] contactInfo: The list of contacts
	 * @param[in, out] objects: The list of objects.
	 */
	void fillForces(
		const Scalar timestep,
		const Vector3& gravity,
		std::vector<ContactInformation>& contactInfo,
		std::vector<std::unique_ptr<RigidObjectBase>>& objects) override{};

	/**
	 * Print the timeing of calculations.
	 * @param[in] totalSteps: The number of total steps to calculate an average.
	 */
	std::string printTimings(size_t totalSteps) override {
		return "Nothing to see here.";
	}

	// void fillFromYAML(const YAML::Node& node) override {}

	/// The logging parameter.
	std::shared_ptr<unsigned int> mp_logging;
};
}  // namespace Solver
}  // namespace FrictionFrenzy
