#include "Solver.h"

#include <stdexcept>
#include "../ImGUIUtils.h"
#include "PrimalDual/NonSmoothForce.h"

namespace Homogenization {
namespace UI {
namespace Solver = FrictionFrenzy::Solver;
void showImGUIMenu(Solver::ForceSolver& solver) {
	switch (solver.getType()) {
	case Solver::ForceSolverType::PrimalDual: {
		auto* p_solver = dynamic_cast<Solver::PrimalDualForceSolver*>(&solver);
		showImGUIMenu(*p_solver);
		break;
	}
	case Solver::ForceSolverType::Null: {
		auto* p_solver = dynamic_cast<Solver::NullForceSolver*>(&solver);
		showImGUIMenu(*p_solver);
		break;
	}
	default:
		throw std::runtime_error("ImGUI: unknown solver type");
	}
}
void showImGUIMenu(Solver::PrimalDualForceSolver& solver) {
	if (ImGui::TreeNodeEx("Solver: Primal Dual Solver",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::SliderInt("Iterations", &solver.maxIter(), 1, 50);
		ImGui::SliderFloatType("Tolerance", &solver.tolerance(), 1e-8, 1e-1,
		                       "%.4g", ImGuiSliderFlags_Logarithmic);

		ImGui::TreePop();
	}
}
void showImGUIMenu(Solver::NullForceSolver& solver) {
	if (ImGui::TreeNodeEx("Solver: Primal Dual Solver",
	                      ImGuiTreeNodeFlags_DefaultOpen)) {
		ImGui::Text("Use the force...or maybe not.");
		ImGui::TreePop();
	}
}
}  // namespace UI
}  // namespace FrictionFrenzy
