#pragma once

#include "Common/MatrixTypes.h"
#include "Common/Scalar.h"
#include "ExperimentBase.h"

namespace Homogenization {
namespace Params {
struct StaticPress : public Experiment {
	using Scalar = FrictionFrenzy::Scalar;
	Scalar pressFractionIncrement;
	Scalar decay;
	Scalar speedTol;
	Scalar stressTol;
	Scalar stressUpperLimit;
	Scalar stressSearchFactor;
	Scalar stressLowerLimit;
	Scalar shearIncrements;
	uint16_t pressSearchIterations;
};
}  // namespace Params

namespace Experiments {
using FrictionFrenzy::Scalar;
/**
 * @brief A uniaxial, quasistatic press test, mainly used to determine
 * elasticity.
 */
class StaticPress : public ExperimentBase {
   public:
	StaticPress() { reset(); }
	void fillFromParams(const Params::Experiment& params) override;
	ExperimentType getType() override { return ExperimentType::STATIC_PRESS; }
	void reset() override {
		m_pressMode = PressMode::BEGIN;
		m_isEquilibrium = true;
		m_shouldFinish = false;
		m_currPressInc = 0;
	}
	void preprocess(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	void postprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	bool isRunning(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override {
		return (m_pressMode != PressMode::FINISHED);
	};
	std::string statistics() const override { return m_stats; }
	std::string getName() const override { return "Static press"; }

   protected:
	enum class PressMode {
		BEGIN,
		RELEASE_SEARCH,
		PRESS_SEARCH,
		EXPAND,
		PAUSE,
		FINISHED
	} m_pressMode;
	Scalar m_pressFractionIncrement;
	Scalar m_decay;
	Scalar m_speedTol;
	Scalar m_stressUpperLimit;
	Scalar m_stressSearchFactor;
	Scalar m_stressLowerLimit;
	Scalar m_stressTol;
	Scalar m_particleVolumeSum;
	Scalar m_lastEqTime;
	// uint16_t m_pressIncrements;
	int16_t m_shearIncrements;
	int16_t m_currPressInc;
	bool m_isEquilibrium;
	bool m_isFirstAfterShift;
	bool m_shouldFinish;

	int16_t m_pressSearchIterations;
	int16_t m_pressSearchCurrentIter;

	Scalar m_stressOld;
	std::string m_stats;
};

}  // namespace Experiments
}  // namespace Homogenization
