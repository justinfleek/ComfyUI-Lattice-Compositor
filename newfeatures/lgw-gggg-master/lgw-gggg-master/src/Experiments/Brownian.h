#pragma once
#include "Common/RNG.h"
#include "Common/Scalar.h"
#include "ExperimentBase.h"

namespace Homogenization {
namespace Params {
struct Brownian : public Experiment {
	FrictionFrenzy::Scalar duration;
	FrictionFrenzy::Scalar magnitudeStd;
	int seed;
};
};  // namespace Params
	//

/**
 * @brief Brownian motion for a predetermined duration.
 */
namespace Experiments {
class Brownian : public ExperimentBase {
   public:
	Brownian() : m_gaussianSampler(0, 1, 3, 0), m_uniformSampler(0, 1, 0) {}
	void fillFromParams(const Params::Experiment &params) override;
	void reset() override{};
	ExperimentType getType() override { return ExperimentType::BROWNIAN; }
	void preprocess(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	void postprocess(
		FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	bool isRunning(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) override;
	std::string statistics() const override { return ""; }
	std::string getName() const override { return "Brownian motion"; }

   protected:
	FrictionFrenzy::Scalar m_duration;
	FrictionFrenzy::Scalar m_magnitudeStd;
	GaussianSampler<FrictionFrenzy::Scalar> m_gaussianSampler;
	UniformSampler<FrictionFrenzy::Scalar> m_uniformSampler;
};
}  // namespace Experiments
}  // namespace Homogenization
