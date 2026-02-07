#include "StaticPressShear.h"
#include <iomanip>
#include <limits>
#include "Common/MatrixTypes.h"
#include "Dynamics/DynamicSystem.h"
#include "Dynamics/PeriodicWorld.h"
#include "Experiments/ExperimentBase.h"

namespace Homogenization {
namespace Experiments {
namespace ff = FrictionFrenzy;
void StaticPressShear::fillFromParams(const Params::Experiment& params) {
	const auto& paramsCast = params.cast<Params::StaticPressShear>();
	m_pressFractionIncrement = paramsCast.pressFractionIncrement;
	m_shearMax = paramsCast.shearMax;
	m_decay = paramsCast.decay;
	m_speedTol = paramsCast.speedTol;
	m_stressTol = paramsCast.stressTol;
	m_stressUpperLimit = paramsCast.stressUpperLimit;
	m_stressSearchFactor = paramsCast.stressSearchFactor;
	m_stressLowerLimit = paramsCast.stressLowerLimit;
	m_shearIncrements = paramsCast.shearIncrements;
	m_pressSearchIterations = paramsCast.pressSearchIterations;
	m_shearMicroInc = paramsCast.shearMicroInc;
	m_biaxialStretch = paramsCast.biaxialStretch;
	m_shearDir = paramsCast.shearDir;
	m_stressOld = std::numeric_limits<ff::Scalar>::infinity();
}
void StaticPressShear::preprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto* periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());

	// Reset everything if this is the first timestep.
	if (m_shearMode == ShearMode::BEGIN && m_pressMode == PressMode::BEGIN) {
		m_isEquilibrium = true;
		m_initialPressFraction = periodic->getScale()[0];
		m_pressMode = PressMode::RELEASE_SEARCH;
		m_pressSearchCurrentIter = 0;
		m_stopPressSearch = false;
		m_firstAfterReleaseSearch = false;
		m_currShearMicroInc = 0;
		std::cout << "Beginning press search..." << std::endl;
		m_particleVolumeSum = 0;
		for (auto& obj : dynamics.getObjectArray()) {
			m_particleVolumeSum += obj->mass() / obj->density();
		}
	}

	ff::Vector3 scaleOld = periodic->getScale();
	ff::Vector3 scaleNew = periodic->getScale();
	if (m_isEquilibrium) {
		// If in static equilibrium, determine shear and press increments.
		Scalar pressInc = 0;
		Scalar shearInc = 1;
		if (m_pressMode == PressMode::RELEASE_SEARCH) {
			pressInc = m_pressFractionIncrement * periodic->getScale()[2] *
			           m_stressSearchFactor;
		}
		if (m_pressMode == PressMode::PRESS_SEARCH) {
			pressInc = -m_pressFractionIncrement * periodic->getScale()[2] /
			           (1 + m_pressFractionIncrement);
		} else {
			if (m_pressMode == PressMode::EXPAND) {
				pressInc = m_pressFractionIncrement * periodic->getScale()[2];
				m_currentSize = periodic->getScale()[2] + pressInc;
				m_pressMode = PressMode::PAUSE;
			}
			int16_t shearNumInc = (m_shearMode == ShearMode::SHEAR_LEFT    ? 1
			                       : m_shearMode == ShearMode::SHEAR_RIGHT ? -1
			                                                               : 0);
			shearInc = std::pow(1 + m_shearMax,
			                    1. / m_shearIncrements / m_shearMicroInc);
			shearInc = m_shearMode == ShearMode::SHEAR_LEFT    ? shearInc
			           : m_shearMode == ShearMode::SHEAR_RIGHT ? 1. / shearInc
			                                                   : 1;
			m_currShearMicroInc = 1;

			m_currShearInc += shearNumInc;
		}
		ff::Vector3 pressIncVec(pressInc, pressInc, pressInc);
		ff::Vector3 shearDims(0, 0, 0);
		ff::Vector3 shearIncVec(shearInc, 1. / shearInc, 1);

		// Determine the scale of the periodic domain from the shear and press
		// increments.
		int nExpand = 0, nContract = 0;
		for (int d = 0; d < 3; ++d) {
			if (m_shearDir[d] > 0) {
				nExpand++;
			} else if (m_shearDir[d] < 0) {
				nContract++;
			}
		}
		for (int d = 0; d < 3; ++d) {
			ff::Scalar shearPower = 0;
			if (m_shearDir[d] > 0) {
				shearPower = 1. / nExpand;
			} else if (m_shearDir[d] < 0) {
				shearPower = -1. / nContract;
			}
			shearIncVec[d] = std::pow(shearInc, shearPower);
		}
		scaleNew =
			(periodic->getScale() + pressIncVec).cwiseProduct(shearIncVec);
		m_isEquilibrium = false;
		m_isFirstAfterShift = true;
		m_stressOld = std::numeric_limits<ff::Scalar>::infinity();

		m_lastEqTime = dynamics.time();
	} else {
		if (m_pressMode == PressMode::PAUSE &&
		    m_currShearMicroInc < m_shearMicroInc) {
			// If currently doing micro-increments from shearing, add new
			// increments.
			Scalar shearInc = 1;
			shearInc = std::pow(1 + m_shearMax,
			                    1. / m_shearIncrements / m_shearMicroInc);
			shearInc = m_shearMode == ShearMode::SHEAR_LEFT    ? shearInc
			           : m_shearMode == ShearMode::SHEAR_RIGHT ? 1. / shearInc
			                                                   : 1;
			m_currShearMicroInc++;

			ff::Vector3 shearIncVec(shearInc, 1. / shearInc, 1);
			int nExpand = 0, nContract = 0;
			for (int d = 0; d < 3; ++d) {
				if (m_shearDir[d] > 0) {
					nExpand++;
				} else if (m_shearDir[d] < 0) {
					nContract++;
				}
			}
			for (int d = 0; d < 3; ++d) {
				ff::Scalar shearPower = 0;
				if (m_shearDir[d] > 0) {
					shearPower = 1. / nExpand;
				} else if (m_shearDir[d] < 0) {
					shearPower = -1. / nContract;
				}
				shearIncVec[d] = std::pow(shearInc, shearPower);
			}
			scaleNew = periodic->getScale().cwiseProduct(shearIncVec);
			m_stressOld = std::numeric_limits<ff::Scalar>::infinity();
			m_lastEqTime = dynamics.time();
		}
	}
	if (!(scaleNew - scaleOld).isZero()) {
		assignDeformRate(dynamics, ff::Vector3::Zero(),
		                 (scaleNew - scaleOld) / dynamics.timestep(),
		                 ff::Vector3::Zero());
	} else {
		periodic->assignDeformRate(ff::Vector3::Zero(), ff::Vector3::Zero(),
		                           ff::Vector3::Zero());
	}
}
void StaticPressShear::postprocess(ff::Dynamics::DynamicSystem& dynamics) {
	auto* periodic =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());
	auto& contactInfo = dynamics.contactInfo();

	// Get average speed at contacts
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
	default: {
	}
	}
	switch (m_shearMode) {
	case ShearMode::SHEAR_LEFT:
		ss << "Shearing left...\n";
		break;
	case ShearMode::SHEAR_RIGHT:
		ss << "Shearing right...\n";
		break;
	case ShearMode::BEGIN:
		ss << "No shearing...\n";
		break;
	default: {
	}
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

	if (isEquilibrium()) {
		m_isEquilibrium = true;

		// If currently expanding or paused (i.e. we are measuring stress)
		// output the stress to stdout.
		if (m_pressMode == PressMode::EXPAND ||
		    m_pressMode == PressMode::PAUSE) {
			const auto default_precision{std::cout.precision()};
			std::cout << std::setprecision(
							 std::numeric_limits<Scalar>::digits10)
					  << "Equilibrium reached.\nScale "
					  << periodic->getScale().transpose()
					  << "\nShear: " << periodic->getShear().transpose()
					  << "\nPacking fraction: "
					  << m_particleVolumeSum / periodic->getScale().prod()
					  << "\n# Contacts: " << dynamics.contactInfo().size()
					  << "\nHomogenized stress:\n"
					  << stress << std::endl;
			std::cout << std::setprecision(default_precision);
		}

		m_stressNormMax = std::max(m_stressNormMax, stressNorm);

		// If we're in release search mode, and the lower stress limit is
		// reached, switch to press search mode.
		if (m_pressMode == PressMode::RELEASE_SEARCH) {
			if (stressNorm <= m_stressLowerLimit) {
				std::cout << "Release search finished, starting press "
							 "threshold search"
						  << std::endl;
				m_initialPressFraction = periodic->getScale()[2];
				m_firstAfterReleaseSearch = true;
				m_pressMode = PressMode::PRESS_SEARCH;
			}
		} else if (m_pressMode == PressMode::PRESS_SEARCH) {
			// If we're in press search mode, go to expand mode if max.
			// iterations is reached. Otherwise go back to release search mode.
			Scalar fac =
				(m_pressSearchCurrentIter < m_pressSearchIterations - 1)
					? m_stressSearchFactor
					: 1;
			if (stressNorm >= m_stressUpperLimit * fac) {
				m_pressSearchCurrentIter++;
				if (m_pressSearchCurrentIter >= m_pressSearchIterations) {
					std::cout << "Press search finished, starting shearing test"
							  << std::endl;
					m_pressMode = PressMode::EXPAND;
					m_stressNormMax = 0;
				} else {
					m_pressMode = PressMode::RELEASE_SEARCH;
				}
			}
			if (m_firstAfterReleaseSearch) {
				if (stressNorm >= m_stressLowerLimit) {
					m_stopPressSearch = true;
				}
				m_firstAfterReleaseSearch = false;
			}
		} else {
			// The experiment is currently in expand mode (i.e. measurements are
			// made.)
			if (m_shearMode == ShearMode::BEGIN) {
				// Stress lower limit reached. Finish after this round.
				if (stressNorm <= m_stressLowerLimit) {
					m_shouldFinish = true;
				}
				// Record the current object positions/orientations.
				m_shearMode = ShearMode::SHEAR_LEFT;
				m_currentSize = periodic->getScale()[2];
				m_positions.resize(dynamics.nObjects());
				m_orientations.resize(dynamics.nObjects());
				m_velocities.resize(dynamics.nObjects());
				m_angVels.resize(dynamics.nObjects());
				for (int i = 0; i < dynamics.nObjects(); ++i) {
					auto& obj = dynamics.getObject(i);
					m_positions[i] = obj.getTranslation();
					m_orientations[i] = obj.getRotation();
				}
			}
			if (m_shearMode == ShearMode::SHEAR_LEFT &&
			    m_currShearInc == m_shearIncrements) {
				// If the maximum increments are reached, set everything back to
				// before shearing.
				for (int i = 0; i < dynamics.nObjects(); ++i) {
					auto& obj = dynamics.getObject(i);
					obj.setTranslation(m_positions[i]);
					obj.setRotation(m_orientations[i]);
					obj.velocity().setZero();
					obj.angularVel().setZero();
					obj.angularAcc().setZero();
					obj.acceleration().setZero();
				}
				periodic->getShear().setZero();
				periodic->getScale().setConstant(m_currentSize);
				m_currShearInc = 0;

				// Finish or keep expanding.
				if (m_shouldFinish) {
					m_shearMode = ShearMode::FINISHED;
					m_pressMode = PressMode::FINISHED;
				} else {
					m_shearMode = ShearMode::BEGIN;
					m_pressMode = PressMode::EXPAND;
				}
				m_stressNormMax = 0;
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
