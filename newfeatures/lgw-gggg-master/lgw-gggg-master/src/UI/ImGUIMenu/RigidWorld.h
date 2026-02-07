#pragma once

#include "Dynamics/DynamicSystem.h"
#include "Dynamics/RigidBodyWorld.h"
namespace Homogenization {
namespace UI {
void showImGUIMenu(FrictionFrenzy::Dynamics::RigidBodyWorld& world,
                   FrictionFrenzy::Dynamics::DynamicSystem& dynamics);
}
}  // namespace ContactSimulation
