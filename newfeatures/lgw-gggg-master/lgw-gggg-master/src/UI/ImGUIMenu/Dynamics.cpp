#include "Dynamics.h"

#include "RigidWorld.h"
#include "./Solver/Solver.h"
#include "ImGUIUtils.h"
namespace Homogenization {
namespace UI {
void showImGUIMenu(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) {
	if(dynamics.rigidBodyWorld())  {
		showImGUIMenu(*dynamics.rigidBodyWorld(), dynamics);
	}
	
	if (ImGui::CollapsingHeader("Simulation Parameters")) {
		ImGui::Text("%.6f", dynamics.time());
		if (ImGui::SliderFloatType("Timestep", &dynamics.timestep(), 1e-4, 1e-1,
		                           "%.4f", ImGuiSliderFlags_Logarithmic)) {
		}
		// ImGui::Checkbox("Adaptive timestep", &dynamics.adaptiveTimestep());
		// if (dynamics.adaptiveTimestep()) {
		// 	ImGui::SliderFloatType("Substep Factor", &dynamics.substepFactor(),
		// 	                       1, 5);
		// }
		// ImGui::SliderInt("Substeps", &dynamics.substeps(), 1, 10);
		ImGui::SliderFloatType3("Gravity", dynamics.gravity().data(), -50, 50);

		if (dynamics.forceSolver()) {
			showImGUIMenu(*dynamics.forceSolver());
		}
	}
}
void showImGUICollisionMenu(FrictionFrenzy::Dynamics::DynamicSystem& dynamics) {
	std::stringstream ss;
	ss << "Contacts (" << dynamics.nContacts() << " total)";
	if (ImGui::TreeNodeEx(ss.str().c_str())) {
		for (size_t i = 0; i < dynamics.nContacts(); ++i) {
			ss.str(std::string());
			ss << "Collision " << i << " (objects "
			   << dynamics.contactInfo()[i].objId[0] << ", "
			   << dynamics.contactInfo()[i].objId[1] << ")";
			if (ImGui::CollapsingHeader(ss.str().c_str())) {
				ImGui::Text("%s", dynamics.contactInfo()[i].toString().c_str());
			}
		}
		ImGui::TreePop();
	}
}
}  // namespace UI
}  // namespace FrictionFrenzy
