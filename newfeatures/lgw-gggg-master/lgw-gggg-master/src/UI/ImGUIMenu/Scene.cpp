#include "Scene.h"
#include <imgui.h>
#include <stdexcept>

#include "Common/LoggingOptions.h"
#include "Dynamics.h"
#include "Experiments/ExperimentBase.h"
#include "ImGUIUtils.h"
namespace Homogenization {
namespace UI {
namespace ff = FrictionFrenzy;
void showImGUIMenu(SimulationScene& scene) {
	ff::Dynamics::DynamicSystem& dyn = scene.dynamicSystem();
	showImGUIMenu(dyn);
	ImGui::Checkbox("Tile X", &scene.m_tileX);
	ImGui::SameLine();
	ImGui::Checkbox("Tile Y", &scene.m_tileY);
	ImGui::SameLine();
	ImGui::Checkbox("Tile Z", &scene.m_tileZ);
	if (ImGui::CollapsingHeader("Experiments")) {
		auto& exps = scene.getExperiments();
		for (auto it = exps.begin(); it != exps.end(); ++it) {
			auto& expe = *(it->get());
			ImGui::Text("%s", expe.getName().c_str());
		}
	}
	if (scene.hasDrawables()) {
		if (ImGui::CollapsingHeader("Simulation Playback",
		                            ImGuiTreeNodeFlags_DefaultOpen)) {
			if (scene.isSimulating()) {
				if (ImGui::Button("Stop simulation")) {
					scene.setSimulate(false);
				}
			} else {
				if (ImGui::Button("Start simulation")) {
					scene.setSimulate(true);
				}
			}
			ImGui::SameLine();
			if (ImGui::Button("Step simulation")) {
				scene.stepSimulation() = true;
			}
			ImGui::SameLine();
			if (ImGui::Button("Reset")) {
				dyn.reset();
				scene.getCurrentExperiment() = scene.getExperiments().begin();
			}
		}
		if (ImGui::CollapsingHeader("Simulation logging")) {
			auto logOption = [&](const std::string& name,
			                     ff::LoggingOptions opt) {
				bool logOn = (*scene.mp_logging) & (unsigned int)opt;
				if (ImGui::Checkbox(name.c_str(), &logOn)) {
					setLoggingOption(scene.mp_logging, opt, logOn);
				}
			};
			logOption("Time per step", ff::LoggingOptions::PER_STEP_TIME);
			logOption("Error per iteration",
			          ff::LoggingOptions::PER_ITER_ERRORS);
			logOption("Error per step", ff::LoggingOptions::PER_STEP_ERRORS);
			logOption("Contacts per step",
			          ff::LoggingOptions::PER_STEP_CONTACTS);
			logOption("Max tangential speed",
			          ff::LoggingOptions::PER_STEP_SPEEDS);
			logOption("Non-dimensionalizing parameters",
			          ff::LoggingOptions::PER_STEP_CHARFACTOR);
			logOption("Max penetration depth",
			          ff::LoggingOptions::MAX_PENETRATION_DEPTH);
			logOption("Friction coefficient",
			          ff::LoggingOptions::PER_STEP_FRICTION_COEFF);
			logOption("Log misc", ff::LoggingOptions::MISC_DEBUG);
		}
	}
	if (!scene.getExperiments().empty() &&
	    scene.getCurrentExperiment() != scene.getExperiments().end()) {
		ImGui::Text("%s",
		            (*scene.getCurrentExperiment())->statistics().c_str());
	}
	std::stringstream ss;
	ss << "Homogenized stress:\n" << scene.m_stress << std::endl;
	ImGui::Text("%s", ss.str().c_str());
}
}  // namespace UI
}  // namespace Homogenization
