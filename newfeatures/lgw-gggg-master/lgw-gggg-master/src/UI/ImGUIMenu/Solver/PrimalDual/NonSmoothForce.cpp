#include "NonSmoothForce.h"

#include <imgui.h>
#include <stdexcept>
#include "../../ImGUIUtils.h"
#include "Solver/PrimalDual/NonSmoothForces/NormalizedContactForce.h"

namespace Homogenization {
namespace UI {
using namespace FrictionFrenzy::Solver;
void showImGUIMenu(NonSmoothForceBase& nonSmoothForce) {
	switch (nonSmoothForce.getType()) {
	case NonSmoothForceType::ONLY_NORMAL_FORCE: {
		auto* pForce = dynamic_cast<OnlyNormalForce*>(&nonSmoothForce);
		showImGUIMenu(*pForce);
		break;
	}
	case NonSmoothForceType::NON_SMOOTH_CONTACTS: {
		auto* pForce = dynamic_cast<NonSmoothContactForce*>(&nonSmoothForce);
		showImGUIMenu(*pForce);
		break;
	}
	case NonSmoothForceType::SECOND_ORDER_CONE: {
		auto* pForce = dynamic_cast<SecondOrderConeForce*>(&nonSmoothForce);
		showImGUIMenu(*pForce);
		break;
	}
	case NonSmoothForceType::NON_SMOOTH_CONTACTS_NORMALIZED: {
		auto* pForce = dynamic_cast<NormalizedContactForce*>(&nonSmoothForce);
		showImGUIMenu(*pForce);
		break;
	}
	default:
		throw std::runtime_error("ImGUI: unknown non-smooth force type");
	}
}
void showImGUIMenu(OnlyNormalForce& nonSmoothForce) {
	if (ImGui::TreeNodeEx("Normal force only",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::Checkbox("Spring-based force",
		                &nonSmoothForce.m_springBasedForce);
		if (nonSmoothForce.m_springBasedForce) {
			ImGui::SliderFloatType("Spring K", &nonSmoothForce.m_springK, 1e1,
			                       1e6, "%.6g", ImGuiSliderFlags_Logarithmic);
			ImGui::SliderFloatType("Dampening (rel. to K)",
			                       &nonSmoothForce.m_springDamp, 0., 10.,
			                       "%.4g", ImGuiSliderFlags_Logarithmic);
		} else {
			ImGui::SliderFloatType("Restitution", &nonSmoothForce.m_restitution,
			                       0., 1.);
		}
		ImGui::TreePop();
	}
}
void showImGUIMenu(NonSmoothContactForce& nonSmoothForce) {
	if (ImGui::TreeNodeEx("Non-smooth contact force",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::Checkbox("Spring-based force",
		                &nonSmoothForce.m_springBasedForce);
		if (nonSmoothForce.m_springBasedForce) {
			ImGui::Checkbox("Area-weighted springs",
			                &nonSmoothForce.m_areaBasedK);
			ImGui::SliderFloatType(
				nonSmoothForce.m_areaBasedK ? "Youngs Modulus" : "Spring K",
				&nonSmoothForce.m_springK, 1e1, 1e6, "%.6g",
				ImGuiSliderFlags_Logarithmic);
			ImGui::SliderFloatType("Dampening (rel. to K)",
			                       &nonSmoothForce.m_springDamp, 0., 10.,
			                       "%.4g", ImGuiSliderFlags_Logarithmic);
		} else {
			ImGui::SliderFloatType("Restitution", &nonSmoothForce.m_restitution,
			                       0., 1.);
		}
		ImGui::SliderFloatType("Friction",
		                       nonSmoothForce.mp_frictionCoeff.get(), 0, 2);
		ImGui::TreePop();
	}
}
void showImGUIMenu(NormalizedContactForce& nonSmoothForce) {
	if (ImGui::TreeNodeEx("Normalized non-smooth contact force",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::Checkbox("Spring-based force",
		                &nonSmoothForce.m_springBasedForce);
		if (nonSmoothForce.m_springBasedForce) {
			ImGui::SliderFloatType("Spring K", &nonSmoothForce.m_springK, 1e1,
			                       1e6, "%.6g", ImGuiSliderFlags_Logarithmic);
			ImGui::SliderFloatType("Dampening (rel. to K)",
			                       &nonSmoothForce.m_springDamp, 0., 10.,
			                       "%.4g", ImGuiSliderFlags_Logarithmic);
		} else {
			ImGui::SliderFloatType("Restitution", &nonSmoothForce.m_restitution,
			                       0., 1.);
		}
		ImGui::SliderFloatType("Friction",
		                       nonSmoothForce.mp_frictionCoeff.get(), 0, 2);
		ImGui::TreePop();
	}
}
void showImGUIMenu(SecondOrderConeForce& nonSmoothForce) {
	if (ImGui::TreeNodeEx("Second-order cone problem",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::SliderFloatType("Restitution", &nonSmoothForce.m_restitution, 0.,
		                       1.);
		ImGui::SliderFloatType("Friction",
		                       nonSmoothForce.mp_frictionCoeff.get(), 0, 2);
		ImGui::TreePop();
	}
}
}  // namespace UI
}  // namespace Homogenization
