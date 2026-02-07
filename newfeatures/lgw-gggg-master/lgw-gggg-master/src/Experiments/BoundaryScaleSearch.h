#pragma once

#include "Common/Scalar.h"
#include "ExperimentBase.h"

namespace Homogenization {

namespace Params {
	struct BoundaryScaleSearch : public Experiment {
		FrictionFrenzy::Scalar scaleSpeed;
		FrictionFrenzy::Scalar decay;
		FrictionFrenzy::Scalar shrinkThresh;
		FrictionFrenzy::Scalar expandThresh;
		FrictionFrenzy::Scalar haltDur;
		FrictionFrenzy::Scalar iterations;
	};
}

namespace Experiments {
/**
 * @brief Find the threshold where the grains become compressed.
 */
class BoundaryScaleSearch : public ExperimentBase {
   public:
	BoundaryScaleSearch() { reset(); }
	void fillFromParams(const Params::Experiment &params) override;
	ExperimentType getType() override {
		return ExperimentType::BOUNDARY_SCALE_SEARCH;
	}
	void reset() override {
		m_mode = Mode::SHRINK;
		m_currIter = 0;
	}
	void preprocess(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	void postprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	bool isRunning(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override {
		return (m_mode != Mode::FINISHED);
	}
	std::string statistics() const override { return m_stats; }
	std::string getName() const override { return "Boundary scale search"; }

   protected:
	enum class Mode { SHRINK, HALT, EXPAND, FINISHED } m_mode;
	FrictionFrenzy::Vector3 scaleRate(const FrictionFrenzy::Vector3& size);
	FrictionFrenzy::Scalar m_scaleSpeed = 1;
	FrictionFrenzy::Scalar m_shrinkThresh;
	FrictionFrenzy::Scalar m_expandThresh;
	FrictionFrenzy::Scalar m_decay = 1;
	FrictionFrenzy::Scalar m_haltStart;
	FrictionFrenzy::Scalar m_haltDur;
	unsigned short m_iterations = 1;
	unsigned short m_currIter = 0;
	std::string m_stats;
};

}  // namespace Experiments
}  // namespace Homogenization
