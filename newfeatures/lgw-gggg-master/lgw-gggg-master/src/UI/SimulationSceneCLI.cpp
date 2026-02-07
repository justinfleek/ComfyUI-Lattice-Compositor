#include "SimulationSceneCLI.h"
#include <filesystem>
#include <functional>
#include <memory>
#include "Common/LoggingOptions.h"
#include "Common/MatrixTypes.h"
#include "Dynamics/PeriodicWorld.h"
#include "Dynamics/RigidBodyWorld.h"
#include "Experiments/ExperimentBase.h"
namespace Homogenization {
namespace UI {
SimulationSceneCLI::SimulationSceneCLI()
	: mp_logging(new unsigned int(0)),
	  m_experimentStart(true),
	  m_dynamics(mp_logging) {}

void SimulationSceneCLI::clearAll() {
	m_experiments.clear();
	m_dynamics.clear();

	m_experimentStart = true;
	m_currExperiment = m_experiments.begin();
}
void SimulationSceneCLI::advanceOneFrame() {
	if (m_simulate || m_stepSimulation) {
		if (m_currExperiment != m_experiments.end()) {
			if ((*m_currExperiment)->isRunning(m_dynamics) == false) {
				m_currExperiment++;
				std::cout << "Experiment finished" << std::endl;
				m_experimentStart = true;
			}
		}

		if (m_currExperiment != m_experiments.end()) {
			if (m_experimentStart) {
				std::cout << "Starting experiment: "
						  << (*m_currExperiment)->getName() << std::endl;
				m_experimentStart = false;
			}
			(*m_currExperiment)->preprocess(m_dynamics);
		}

		m_dynamics.fillForces(m_dynamics.timestep());
		m_stress = Experiments::homogenizedStress(m_dynamics);

		if (m_currExperiment != m_experiments.end()) {
			(*m_currExperiment)->postprocess(m_dynamics);
		}
		m_dynamics.updateAllObjects(m_dynamics.timestep());
		if (m_stepSimulation) {
			m_stepSimulation = false;
		}

		if (m_currExperiment == m_experiments.end()) {
			m_simulate = false;
			m_stepSimulation = false;
		}
	}
}

}  // namespace UI
}  // namespace Homogenization
