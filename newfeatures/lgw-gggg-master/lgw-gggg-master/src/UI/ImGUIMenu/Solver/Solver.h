#pragma once

#include "Solver/Solver.h"
namespace Homogenization {
namespace UI {
void showImGUIMenu(FrictionFrenzy::Solver::ForceSolver& solver);
void showImGUIMenu(FrictionFrenzy::Solver::PrimalDualForceSolver& solver);
void showImGUIMenu(FrictionFrenzy::Solver::NullForceSolver& solver);
}  // namespace UI
}  // namespace FrictionFrenzy
