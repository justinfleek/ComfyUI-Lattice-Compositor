#pragma once

#include <FrictionFrenzy.h>
#include "Common/Scalar.h"
#include "Dynamics/DynamicSystem.h"

namespace Homogenization {
namespace Params {
struct Experiment {
	template <typename P>
	const P& cast() const {
		static_assert(std::is_base_of_v<Experiment, P>,
		              "Cannot convert class to experiment parameters");
		return *static_cast<const P*>(this);
	}
	template <typename P>
	P& cast() {
		static_assert(std::is_base_of_v<Experiment, P>,
		              "Cannot convert class to experiment parameters");
		return *static_cast<P*>(this);
	}
};
struct EmptyExperiment : Experiment {
	FrictionFrenzy::Scalar duration;
};
}  // namespace Params

namespace Experiments {
enum class ExperimentType {
	NONE,
	EMPTY,
	BROWNIAN,
	BOUNDARY_SCALE_SEARCH,
	STATIC_PRESS,
	STATIC_PRESS_SHEAR,
	N_EXPERIMENTS
};

/**
 * @brief Calculate the homogenized Cauchy stress tensor at the current
 * timestep.
 */
FrictionFrenzy::Matrix3 homogenizedStress(
	FrictionFrenzy::Dynamics::DynamicSystem& dynamics);

/**
 * @brief Assign a deformation rate to the rigid body world.
 *
 * @param[in] dynamics: the rigid body dynamics.
 * @param[in] tRate: the speed the center of the periodic domain is moving. For
 *                   most experiments this should be zero.
 * @param[in] scaleRate: the scale rate of the periodic domain
 * @param[in] shearRate: the shear rate of the periodic domain. For most
 * experiments this should be zero.
 */
void assignDeformRate(FrictionFrenzy::Dynamics::DynamicSystem& dynamics,
                      const FrictionFrenzy::Vector3& tRate,
                      const FrictionFrenzy::Vector3& scaleRate,
                      const FrictionFrenzy::Vector3& shearRate);

/**
 * @brief Base class for homogenization experiments
 */
class ExperimentBase {
   public:
	virtual ~ExperimentBase() {}
	/**
	 * @brief Fill in the necessary parameters
	 * @param[in] params: The parameters.
	 */
	virtual void fillFromParams(const Params::Experiment& params) = 0;

	/**
	 * @brief Return the type of the experiment
	 *
	 * @returns Type of the experement as an enum type.
	 */
	virtual ExperimentType getType() { return ExperimentType::NONE; }

	/**
	 * @brief Reset the experiment.
	 */
	virtual void reset() = 0;

	/**
	 * @brief The procedure to run before calculating the rigid body contact
	 * response.
	 *
	 * @param[in] dynamics: The dynamics system.
	 */
	virtual void preprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics){};

	/**
	 * @brief The procedure to run before calculating the rigid body contact
	 * response.
	 *
	 * @param[in] dynamics: The dynamics system.
	 */
	virtual void postprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics){};

	/**
	 * @brief Returns whether the experiment is finished.
	 *
	 * @param[in] dynamics: The dynamics system.
	 */
	virtual bool isRunning(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics) = 0;

	/**
	 * @brief Returns a string for current state. Used only in the GUI.
	 */
	virtual std::string statistics() const = 0;

	/**
	 * @brief Get the name of the experiment as a string.
	 */
	virtual std::string getName() const = 0;

	/**
	 * @brief Set the starting time of the experiment.
	 */

	/**
	 * @brief Set the starting time of the experiment.
	 *
	 * @param[in] time: the starting time of the experiment.
	 */
	void setStartTime(FrictionFrenzy::Scalar time) { m_startTime = time; }

   protected:
	FrictionFrenzy::Scalar m_startTime;
};

/**
 * @brief An empty experiment that does nothing for a predetermined period of
 * time.
 */
class Empty : public ExperimentBase {
   public:
	Empty() {}
	void fillFromParams(const Params::Experiment& params) override {
		const Params::EmptyExperiment& paramsCast =
			*static_cast<const Params::EmptyExperiment*>(&params);
		m_duration = paramsCast.duration;
	}
	ExperimentType getType() override { return ExperimentType::EMPTY; }
	bool isRunning(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override {
		return (dynamics.time() - m_startTime < m_duration);
	}
	std::string statistics() const override { return ""; }

   protected:
	FrictionFrenzy::Scalar m_duration;
};
}  // namespace Experiments
}  // namespace Homogenization
