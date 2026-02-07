#include "BoundaryScaleSearch.h"
#include "Dynamics/DynamicSystem.h"
#include "Experiments/ExperimentBase.h"

namespace Homogenization {
namespace Experiments {
namespace ff = FrictionFrenzy;
void BoundaryScaleSearch::fillFromParams(const Params::Experiment& params) {
	const auto& paramsCast = params.cast<Params::BoundaryScaleSearch>();
	m_scaleSpeed = paramsCast.scaleSpeed;
	m_scaleSpeed = std::abs(m_scaleSpeed);
	m_decay = paramsCast.decay;
	m_shrinkThresh = paramsCast.shrinkThresh;
	m_expandThresh = paramsCast.expandThresh;
	m_haltDur = paramsCast.haltDur;
	m_iterations = paramsCast.iterations;
	m_mode = Mode::SHRINK;
}
ff::Vector3 BoundaryScaleSearch::scaleRate(const ff::Vector3& size) {
	switch (m_mode) {
	case Mode::SHRINK: {
		return -size * m_scaleSpeed;
		break;
	}
	case Mode::HALT: {
		return ff::Vector3::Zero();
	}
	case Mode::EXPAND: {
		return size * m_scaleSpeed;
		break;
	}
	default:
		return ff::Vector3::Zero();
	}
}
void BoundaryScaleSearch::preprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());

	assignDeformRate(dynamics, ff::Vector3::Zero(),
	                 scaleRate(periodic->getScale()), ff::Vector3::Zero());

	// If the domain is expanding, make the object velocities exponentially
	// decay.
	if (m_mode == Mode::EXPAND) {
#pragma omp parallel for
		for (size_t i = 0; i < dynamics.nObjects(); i++) {
			dynamics.getObject(i).velocity() *= m_decay;
			dynamics.getObject(i).angularVel() *= m_decay;
		}
	}
}
void BoundaryScaleSearch::postprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());
	ff::Matrix3 stress = homogenizedStress(dynamics);

	// If the domain is shrinking, and the stress is past the threshold, halt.
	if (m_mode == Mode::SHRINK && std::abs(stress.norm()) > m_shrinkThresh) {
		m_mode = Mode::HALT;
		m_haltStart = dynamics.time();
	} else if (m_mode == Mode::HALT &&
	           (dynamics.time() - m_haltStart >= m_haltDur)) {
		// If halted for a fixed duration, start expanding
		m_mode = Mode::EXPAND;

		// if (m_currIter == m_iterations - 1) {
		// 	const auto default_precision{std::cout.precision()};
		// 	std::cout << "Final compression stress:\n"
		// 			  << std::setprecision(
		// 					 std::numeric_limits<ff::Scalar>::digits10)
		// 			  << stress << std::endl;
		// 	std::cout << std::setprecision(default_precision);
		// }
	} else if (m_mode == Mode::EXPAND &&
	           (std::abs(stress.norm()) < m_expandThresh ||
	            stress.trace() > 0)) {
		// If done for a fixed number of durations, we finish.
		if (m_currIter == m_iterations - 1) {
			m_mode = Mode::FINISHED;
			periodic->assignDeformRate(ff::Vector3::Zero(), ff::Vector3::Zero(),
			                           ff::Vector3::Zero());
#pragma omp parallel for
			for (size_t i = 0; i < dynamics.nObjects(); i++) {
				dynamics.getObject(i).velocity() *= 0;
				dynamics.getObject(i).angularVel() *= 0;
			}
		} else {
			m_mode = Mode::SHRINK;
			m_currIter++;
		}
	}

	std::stringstream ss;
	ss << "Current iteration: " << m_currIter + 1
	   << "\nStress norm: " << stress.norm() << std::endl;
	m_stats = ss.str();
}
}  // namespace Experiments
}  // namespace Homogenization
