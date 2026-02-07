#pragma once
#include <stdexcept>
#include <FrictionFrenzy.h>
#include "InputParse.h"
#include "Dynamics/PeriodicWorld.h"
#include "Dynamics/RigidBodyWorld.h"
#include "Experiments/BoundaryScaleSearch.h"
#include "Experiments/Brownian.h"
#include "Experiments/ExperimentBase.h"
#include "Experiments/StaticPress.h"
#include "Experiments/StaticPressShear.h"
#include "yaml-cpp/node/node.h"
namespace Homogenization {
namespace IO {
using FrictionFrenzy::Scalar;
using FrictionFrenzy::Vector3i;
namespace ffp = FrictionFrenzy::Params;
void loadParams(const YAML::Node& node, ffp::NonSmoothContactForce& params);
void loadParams(const YAML::Node& node, ffp::NormalizedContactForce& params);
void loadParams(const YAML::Node& node, ffp::SecondOrderConeForce& params);
void loadParams(const YAML::Node& node, ffp::OnlyNormalForce& params);
void loadParams(const YAML::Node& node, ffp::PrimalDualForceSolver& params);
void loadParams(const YAML::Node& node, ffp::PeriodicWorld& params);
void loadParams(const YAML::Node& node, ffp::DynamicSystem& params);
void loadExpParams(const YAML::Node& node, Params::StaticPressShear& params);
void loadExpParams(const YAML::Node& node, Params::StaticPress& params);
void loadExpParams(const YAML::Node& node, Params::EmptyExperiment& params);
void loadExpParams(const YAML::Node& node, Params::Brownian& params);
void loadExpParams(const YAML::Node& node, Params::BoundaryScaleSearch& params);
}  // namespace IO
}  // namespace Homogenization
