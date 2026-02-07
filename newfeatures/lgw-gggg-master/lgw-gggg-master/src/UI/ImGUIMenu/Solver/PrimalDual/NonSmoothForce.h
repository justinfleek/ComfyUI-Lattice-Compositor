#pragma once

#include "Solver/PrimalDual/NonSmoothForces/NonSmoothForces.h"

namespace Homogenization {
namespace UI {
void showImGUIMenu(FrictionFrenzy::Solver::NonSmoothForceBase& nonSmoothForce);
void showImGUIMenu(FrictionFrenzy::Solver::OnlyNormalForce& nonSmoothForce);
void showImGUIMenu(
	FrictionFrenzy::Solver::NonSmoothContactForce& nonSmoothForce);
void showImGUIMenu(
	FrictionFrenzy::Solver::SecondOrderConeForce& nonSmoothForce);
void showImGUIMenu(
	FrictionFrenzy::Solver::NormalizedContactForce& nonSmoothForce);
}  // namespace UI
}  // namespace ContactSimulation
