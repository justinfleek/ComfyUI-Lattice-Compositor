#include "StaticPress.h"
#include <iomanip>
#include <limits>
// #include "Common/InputParse.h"
#include "Dynamics/DynamicSystem.h"
#include "Dynamics/PeriodicWorld.h"
#include "Experiments/ExperimentBase.h"

namespace Homogenization {
namespace Experiments {
namespace ff = FrictionFrenzy;
void StaticPress::fillFromParams(const Params::Experiment& params) {
	const auto& paramsCast = params.cast<Params::StaticPress>();
	m_pressFractionIncrement = paramsCast.pressFractionIncrement;
	m_decay = paramsCast.decay;
	m_speedTol = paramsCast.speedTol;
	m_stressTol = paramsCast.stressTol;
	m_stressUpperLimit = paramsCast.stressUpperLimit;
	m_stressSearchFactor = paramsCast.stressSearchFactor;
	m_stressLowerLimit = paramsCast.stressLowerLimit;
	m_shearIncrements = paramsCast.shearIncrements;
	m_pressSearchIterations = paramsCast.pressSearchIterations;
	m_stressOld = std::numeric_limits<ff::Scalar>::infinity();
}
void StaticPress::preprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto* periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());

	// Start with a release search
	if (m_pressMode == PressMode::BEGIN) {
		m_pressMode = PressMode::RELEASE_SEARCH;
		m_pressSearchCurrentIter = 0;
		m_isEquilibrium = true;
		std::cout << "Beginning press search..." << std::endl;
		m_particleVolumeSum = 0;
		for (auto& obj : dynamics.getObjectArray()) {
			m_particleVolumeSum += obj->mass() / obj->density();
		}
	}

	// If an equilibrium is reached, go to next increment.
	if (m_isEquilibrium) {
		Scalar pressInc = 0;
		if (m_pressMode == PressMode::RELEASE_SEARCH) {
			pressInc = m_pressFractionIncrement * periodic->getScale()[1] *
			           m_stressSearchFactor;
		}
		if (m_pressMode == PressMode::PRESS_SEARCH) {
			pressInc = -m_pressFractionIncrement * periodic->getScale()[1] /
			           (1 + m_pressFractionIncrement);
		} else {
			if (m_pressMode == PressMode::EXPAND) {
				pressInc = m_pressFractionIncrement * periodic->getScale()[1];
				m_pressMode = PressMode::PAUSE;
			}
		}
		ff::Vector3 pressIncVec(0, pressInc, 0);
		periodic->updateDeformation(
			periodic->getCenter(), periodic->getScale() + pressIncVec,
			periodic->getShear(), {dynamics.getObjectArray()});
		m_isEquilibrium = false;
		m_isFirstAfterShift = true;
		m_stressOld = std::numeric_limits<ff::Scalar>::infinity();

		m_lastEqTime = dynamics.time();
	}
}
void StaticPress::postprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto* periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());
	auto& contactInfo = dynamics.contactInfo();

	// Calculate average speed
	ff::Scalar avgSpeed = 0;
	for (int i = 0; i < contactInfo.size(); ++i) {
		ff::Vector3 relVel = ff::Vector3::Zero();
		for (int j = 0; j < 2; ++j) {
			size_t objid = contactInfo[i].objId[j];
			auto& obj = dynamics.getObject(objid);
			ff::Vector6 vel =
				(ff::Vector6() << obj.velocity() + obj.acceleration(),
			     obj.angularVel() + obj.angularAcc())
					.finished();
			relVel += contactInfo[i].toLocal(j, vel);
		}
		avgSpeed += relVel.norm();
	}
	if (!contactInfo.empty()) {
		avgSpeed /= contactInfo.size();
	}

	// Generate a GUI message
	ff::Matrix3 stress = homogenizedStress(dynamics);
	ff::Scalar stressNorm = stress.norm();
	ff::Scalar stressRatio = stressNorm / m_stressOld;
	std::stringstream ss;
	switch (m_pressMode) {
	case PressMode::RELEASE_SEARCH: {
		ss << "Searching for press threshold...\n";
		break;
	}
	case PressMode::PRESS_SEARCH: {
		ss << "Searching for press threshold...\n";
		break;
	}
	case PressMode::EXPAND: {
		ss << "Expanding...\n";
		break;
	}
	default:;
	}
	ss << "Average contact speed: " << avgSpeed << "\n";
	ss << "Stress ratio: " << stressRatio;
	m_stats = ss.str();

	auto isEquilibrium = [&]() {
		if (!m_isFirstAfterShift && avgSpeed < m_speedTol) {
			if (stressNorm <= m_stressLowerLimit ||
			    (stressRatio < 1. / m_stressTol && stressRatio > m_stressTol)) {
				return true;
			}
		} else if (dynamics.time() - m_lastEqTime > 0.2) {
			return true;
		}
		return false;
	};
	auto printStress = [&]() {
		const auto default_precision{std::cout.precision()};
		std::cout << std::setprecision(std::numeric_limits<Scalar>::digits10)
				  << "Equilibrium reached.\nScale "
				  << periodic->getScale().transpose() << "\nPacking fraction: "
				  << m_particleVolumeSum / periodic->getScale().prod()
				  << "\n# Contacts: " << dynamics.contactInfo().size()
				  << "\nHomogenized stress:\n"
				  << stress << std::endl;
		std::cout << std::setprecision(default_precision);
	};
	if (isEquilibrium()) {
		m_isEquilibrium = true;

		if (m_pressMode == PressMode::RELEASE_SEARCH) {
			// Start press search if in release search and lower limit is
			// reached.
			if (stressNorm <= m_stressLowerLimit) {
				std::cout << "Release search finished, starting press "
							 "threshold search"
						  << std::endl;
				if (m_pressSearchCurrentIter == m_pressSearchIterations - 1) {
					printStress();
				}
				m_pressMode = PressMode::PRESS_SEARCH;
			}
		} else if (m_pressMode == PressMode::PRESS_SEARCH) {
			// If in press search mode...
			Scalar fac =
				(m_pressSearchCurrentIter < m_pressSearchIterations - 1)
					? m_stressSearchFactor
					: 1;
			if (m_pressSearchCurrentIter == m_pressSearchIterations - 1) {
				printStress();
			}
			if (stressNorm >= m_stressUpperLimit * fac) {
				m_pressSearchCurrentIter++;
				if (m_pressSearchCurrentIter >= m_pressSearchIterations) {
					std::cout << "Press search finished" << std::endl;
					m_pressMode = PressMode::FINISHED;
				} else {
					m_pressMode = PressMode::RELEASE_SEARCH;
				}
			}
		} else {
			const auto default_precision{std::cout.precision()};
			std::cout << std::setprecision(
							 std::numeric_limits<Scalar>::digits10)
					  << "Equilibrium reached.\nScale "
					  << periodic->getScale().transpose()
					  << "\nPacking fraction: "
					  << m_particleVolumeSum / periodic->getScale().prod()
					  << "\n# Contacts: " << dynamics.contactInfo().size()
					  << "\nHomogenized stress:\n"
					  << stress << std::endl;
			std::cout << std::setprecision(default_precision);
			if (stressNorm < m_stressLowerLimit) {
				m_pressMode = PressMode::FINISHED;
			} else {
				m_pressMode = PressMode::EXPAND;
			}
		}
	}
	m_stressOld = stressNorm;
	m_isFirstAfterShift = false;

	std::unordered_set<size_t> touchingObj;
	for (const auto& c : dynamics.contactInfo()) {
		touchingObj.insert(c.objId[0]);
		touchingObj.insert(c.objId[1]);
	}
	Scalar decay = m_pressMode == PressMode::RELEASE_SEARCH ? 0.999 : m_decay;
#pragma omp parallel for
	for (size_t i = 0; i < dynamics.nObjects(); i++) {
		auto& obj = dynamics.getObject(i);
		if (!touchingObj.count(obj.getID())) {
			obj.velocity() *= decay;
			obj.angularVel() *= decay;
		}
	}
}
}  // namespace Experiments
}  // namespace Homogenization
