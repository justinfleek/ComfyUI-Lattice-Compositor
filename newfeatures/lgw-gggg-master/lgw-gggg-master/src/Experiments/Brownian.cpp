#include "Brownian.h"
#include <cmath>
// #include "Common/InputParse.h"
#include "Common/MatrixTypes.h"
#include "Common/RNG.h"
#include "Dynamics/DynamicSystem.h"

namespace Homogenization {
namespace Experiments {
namespace ff = FrictionFrenzy;
void Brownian::fillFromParams(const Params::Experiment &params) {
	const auto& paramsCast = params.cast<Params::Brownian>();
	m_duration = paramsCast.duration;
	m_magnitudeStd = paramsCast.magnitudeStd;
	m_gaussianSampler = GaussianSampler<ff::Scalar>(
		0, m_magnitudeStd, m_magnitudeStd * 3, paramsCast.seed);
	m_uniformSampler = UniformSampler<ff::Scalar>(0, 1, time(NULL));
}
void Brownian::preprocess(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) {
	ff::Vector3 shift = ff::Vector3::Zero();
	ff::Scalar totalMass = 0;
	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);

		ff::Scalar z = 1 - 2 * m_uniformSampler.sample();
		ff::Scalar r = std::sqrt(1 - z * z);
		ff::Scalar phi = 2 * M_PI * m_uniformSampler.sample();
		ff::Vector3 unitVec(r * std::cos(phi), r * std::sin(phi), z);
		ff::Vector3 force = m_gaussianSampler.sample() * unitVec;
		obj.velocity() += force;
		shift -= obj.mass() * force;
		totalMass += obj.mass();

		z = 1 - 2 * m_uniformSampler.sample();
		r = std::sqrt(1 - z * z);
		phi = 2 * M_PI * m_uniformSampler.sample();
		unitVec = ff::Vector3(r * std::cos(phi), r * std::sin(phi), z);
		force = m_gaussianSampler.sample() * 10 * unitVec;
		obj.angularVel() += force;
	}
	shift /= totalMass;
	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);
		obj.velocity() += shift;
	}
}
void Brownian::postprocess(ff::Dynamics::DynamicSystem& dynamics) {}
bool Brownian::isRunning(ff::Dynamics::DynamicSystem& dynamics) {
	return (dynamics.time() - m_startTime < m_duration);
}
}  // namespace Experiments
}  // namespace Homogenization
