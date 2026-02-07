#include "RigidWorld.h"
#include "UI/ImGUIMenu/ImGUIUtils.h"
#include "Dynamics/PeriodicWorld.h"
#include "Dynamics/RigidBodyWorld.h"
namespace Homogenization {
namespace UI {
void showImGUIMenu(FrictionFrenzy::Dynamics::RigidBodyWorld& world,
                   FrictionFrenzy::Dynamics::DynamicSystem& dynamics) {
	namespace ff = FrictionFrenzy;
	switch (world.getType()) {
	case ff::Dynamics::RigidWorldType::EUCLIDEAN: {
		if (ImGui::CollapsingHeader("Euclidean World")) {
			ImGui::Text("The world is flat!!");
		}
		break;
	}
	case ff::Dynamics::RigidWorldType::PERIODIC: {
		if (ImGui::CollapsingHeader("Periodic World")) {
			auto periodicWorld =
				dynamic_cast<FrictionFrenzy::Dynamics::PeriodicWorld*>(&world);
			ff::Vector3 center = periodicWorld->getCenter();
			ff::Vector3 scale = periodicWorld->getScale();
			ff::Vector3 shear = periodicWorld->getShear();
			bool changed = false;

			changed = ImGui::SliderFloatType3("Center", center.data(), -5, 5);
			changed |=
				ImGui::SliderFloatType("Scale X", &scale[0], 0.2, 1.2, "%.6f");
			changed |=
				ImGui::SliderFloatType("Scale Y", &scale[1], 0.2, 1.2, "%.6f");
			changed |=
				ImGui::SliderFloatType("Scale Z", &scale[2], 0.2, 1.2, "%.6f");
			// ImGui::SliderFloatType3("Scale",
			// periodicWorld->getScale().data(),
			//                         0.001, 10);
			changed |=
				ImGui::SliderFloatType("Shear X", &shear[0], -1, 1, "%.6f");
			changed |=
				ImGui::SliderFloatType("Shear Y", &shear[1], -1, 1, "%.6f");
			changed |=
				ImGui::SliderFloatType("Shear Z", &shear[2], -1, 1, "%.6f");
			// changed |= ImGui::SliderFloatType3("Shear", shear.data(), -1, 1);

			if (changed) {
				periodicWorld->updateDeformation(center, scale, shear,
				                                 dynamics.getObjectArray());
			}
			// ImGui::Checkbox("Show periodic", &periodicWorld->showPeriodic());
		}
		break;
	}
	default: {
	}
	}
}
}  // namespace UI
}  // namespace ContactSimulation
