#pragma once

#include "Common/MatrixTypes.h"
#include "ExperimentBase.h"

namespace Homogenization {

namespace Params {
struct StaticPressShear : public Experiment {
	using Scalar = FrictionFrenzy::Scalar;
	Scalar pressFractionIncrement;
	Scalar shearMax;
	Scalar decay;
	Scalar speedTol;
	Scalar stressTol;
	Scalar stressUpperLimit;
	Scalar stressSearchFactor;
	Scalar stressLowerLimit;
	Scalar shearIncrements;
	Scalar pressSearchIterations;
	Scalar shearMicroInc;
	Scalar biaxialStretch;
	FrictionFrenzy::Vector3i shearDir;
};
}  // namespace Params

namespace Experiments {
using FrictionFrenzy::Scalar;
// A n-axial shear experiment. The shear is volume preserving if more than one
// axis is involved.
class StaticPressShear : public ExperimentBase {
   public:
	StaticPressShear() { reset(); }
	void fillFromParams(const Params::Experiment& params) override;
	ExperimentType getType() override {
		return ExperimentType::STATIC_PRESS_SHEAR;
	}
	void reset() override {
		m_shearMode = ShearMode::BEGIN;
		m_pressMode = PressMode::BEGIN;
		m_isEquilibrium = true;
		m_shouldFinish = false;
		m_currPressInc = 0;
		m_currShearInc = 0;
		m_firstAfterReleaseSearch = false;
		m_positions.clear();
		m_orientations.clear();
		m_velocities.clear();
		m_angVels.clear();
	}
	void preprocess(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	void postprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	bool isRunning(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override {
		return (m_shearMode != ShearMode::FINISHED &&
		        m_pressMode != PressMode::FINISHED);
	};
	std::string statistics() const override { return m_stats; }
	std::string getName() const override { return "Static press shear"; }

   protected:
	enum class ShearMode {
		BEGIN,
		SHEAR_LEFT,
		SHEAR_RIGHT,
		FINISHED
	} m_shearMode;
	enum class PressMode {
		BEGIN,
		RELEASE_SEARCH,
		PRESS_SEARCH,
		EXPAND,
		PAUSE,
		FINISHED
	} m_pressMode;
	Scalar m_initialPressFraction;
	Scalar m_pressFractionIncrement;
	Scalar m_shearMax;
	Scalar m_decay;
	Scalar m_speedTol;
	Scalar m_stressUpperLimit;
	Scalar m_stressSearchFactor;
	Scalar m_stressLowerLimit;
	Scalar m_stressTol;
	Scalar m_particleVolumeSum;
	Scalar m_lastEqTime;
	Scalar m_stressNormMax;
	Scalar m_currentSize;
	// uint16_t m_pressIncrements;
	int16_t m_shearIncrements;
	int16_t m_currPressInc;
	int16_t m_currShearInc;

	FrictionFrenzy::Vector3i m_shearDir;

	bool m_isEquilibrium;
	bool m_isFirstAfterShift;
	bool m_shouldFinish;
	bool m_firstAfterReleaseSearch;
	bool m_stopPressSearch;
	bool m_biaxialStretch = false;

	int16_t m_pressSearchIterations;
	int16_t m_pressSearchCurrentIter;
	int16_t m_shearMicroInc;
	int16_t m_currShearMicroInc;

	std::vector<FrictionFrenzy::Vector3> m_positions;
	std::vector<FrictionFrenzy::Quaternion> m_orientations;
	std::vector<FrictionFrenzy::Vector3> m_velocities;
	std::vector<FrictionFrenzy::Vector3> m_angVels;

	Scalar m_stressOld;
	std::string m_stats;
};

}  // namespace Experiments
}  // namespace Homogenization
