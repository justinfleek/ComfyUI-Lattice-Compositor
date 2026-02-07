#pragma once

#include <memory>
#include <vector>

#include "Common/MatrixTypes.h"
#include "Dynamics/DynamicSystem.h"
#include "Experiments/ExperimentBase.h"

namespace Homogenization {
namespace UI {

/**
 * Simulation scene for the GUI program, which includes information for cameras,
 * rendered 3D meshes, and shaders.
 */
class SimulationSceneCLI {
   public:
	SimulationSceneCLI();

	/**
	 * Advance one frame of the simulation. This can consist of mny substeps.
	 */
	virtual void advanceOneFrame();

	/**
	 * Clear dynamics.
	 */
	virtual void clearAll();

	/**
	 * Access rigid body world
	 */

	FrictionFrenzy::Dynamics::DynamicSystem& dynamicSystem() {
		return m_dynamics;
	}

	// Accessors

	/**
	 * Set whether scene is running.
	 */
	void setSimulate(bool sim) { m_simulate = sim; }

	/**
	 * Check if scene is running.
	 */
	bool isSimulating() { return m_simulate; }

	/**
	 * Step simulation
	 */
	bool& stepSimulation() { return m_stepSimulation; }

	std::list<std::unique_ptr<Experiments::ExperimentBase>>& getExperiments() {
		return m_experiments;
	}
	std::list<std::unique_ptr<Experiments::ExperimentBase>>::iterator&
	getCurrentExperiment() {
		return m_currExperiment;
	}

	std::shared_ptr<unsigned int> mp_logging;  /// Logging parameters.

	FrictionFrenzy::Matrix3 m_stress = FrictionFrenzy::Matrix3::Zero();
	bool m_tileX = false, m_tileY = false, m_tileZ = false;

   protected:
	bool m_simulate = false;
	bool m_stepSimulation = false;
	bool m_experimentStart = true;

	FrictionFrenzy::Dynamics::DynamicSystem m_dynamics;  /// Rigid body world.
	std::list<std::unique_ptr<Experiments::ExperimentBase>> m_experiments;
	std::list<std::unique_ptr<Experiments::ExperimentBase>>::iterator
		m_currExperiment;
};
}  // namespace UI
}  // namespace Homogenization
