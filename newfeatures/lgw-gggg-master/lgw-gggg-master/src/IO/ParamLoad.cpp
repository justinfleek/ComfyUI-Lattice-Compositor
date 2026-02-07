#include "ParamLoad.h"
namespace Homogenization {
namespace IO {
using FrictionFrenzy::Dynamics::RigidWorldType;
using FrictionFrenzy::Solver::ForceSolverType;
using FrictionFrenzy::Solver::NonSmoothForceType;
using FrictionFrenzy::Solver::SmoothForceType;
void loadParams(const YAML::Node& node, ffp::NonSmoothContactForce& params) {
	params.springBasedForce = parseScalar<bool>(
		node, "spring_based_force", false, "non_smooth_contact_force");
	if (params.springBasedForce) {
		params.areaBasedSpring = parseScalar<bool>(
			node, "area_based_springs", false, "non_smooth_contact_force");
		params.springK = parseScalar<Scalar>(node, "spring_k", 1e6,
		                                     "non_smooth_contact_force");
		params.springDamp = parseScalar<Scalar>(node, "spring_damp", 0.01,
		                                        "non_smooth_contact_force");
	} else {
		params.restitution = parseScalar<Scalar>(node, "restitution", 0.5,
		                                         "non_smooth_contact_force");
	}
	params.frictionCoeff = parseScalar<Scalar>(node, "static_coeff", 0.5,
	                                           "non_smooth_contact_force");
}

void loadParams(const YAML::Node& node, ffp::NormalizedContactForce& params) {
	params.springBasedForce = parseScalar<bool>(
		node, "spring_based_force", false, "non_smooth_contact_force");
	if (params.springBasedForce) {
		params.springK = parseScalar<Scalar>(node, "spring_k", 1e6,
		                                     "non_smooth_contact_force");
		params.springDamp = parseScalar<Scalar>(node, "spring_damp", 0.01,
		                                        "non_smooth_contact_force");
	} else {
		params.restitution = parseScalar<Scalar>(node, "restitution", 0.5,
		                                         "non_smooth_contact_force");
	}
	params.frictionCoeff = parseScalar<Scalar>(node, "static_coeff", 0.5,
	                                           "non_smooth_contact_force");
}
void loadParams(const YAML::Node& node, ffp::SecondOrderConeForce& params) {
	params.restitution = parseScalar<Scalar>(node, "restitution", 0.5,
	                                         "non_smooth_contact_force");
	params.frictionCoeff = parseScalar<Scalar>(node, "static_coeff", 0.5,
	                                           "non_smooth_contact_force");
}
void loadParams(const YAML::Node& node, ffp::OnlyNormalForce& params) {
	params.springBasedForce = parseScalar<bool>(
		node, "spring_based_force", false, "non_smooth_contact_force");
	if (params.springBasedForce) {
		params.areaBasedSpring = parseScalar<bool>(
			node, "area_based_springs", false, "non_smooth_contact_force");
		params.springK = parseScalar<Scalar>(node, "spring_k", 1e6,
		                                     "non_smooth_contact_force");
		params.springDamp = parseScalar<Scalar>(node, "spring_damp", 0.01,
		                                        "non_smooth_contact_force");
	} else {
		params.restitution = parseScalar<Scalar>(node, "restitution", 0.5,
		                                         "non_smooth_contact_force");
	}
}
void loadParams(const YAML::Node& node, ffp::PrimalDualForceSolver& params) {
	params.tolerance =
		parseScalar<Scalar>(node, "tolerance", 1e-6, "simulation");
	params.maxIteration =
		parseScalar<int>(node, "iterations", 100, "simulation");

	if (!node["non_smooth_force"].IsDefined()) {
		throw std::runtime_error("No non-smooth force defined!");
	}
	const YAML::Node nonSmoothForceNode = node["non_smooth_force"];
	if (!nonSmoothForceNode["name"].IsDefined()) {
		throw std::runtime_error("Non-smooth force: no name provided!");
	}
	std::string nonSmoothForceName =
		nonSmoothForceNode["name"].as<std::string>();
	if (nonSmoothForceName == "socp") {
		params.nonSmoothForceType = NonSmoothForceType::SECOND_ORDER_CONE;
		params.p_nonSmoothForce = std::make_unique<ffp::SecondOrderConeForce>();
		loadParams(nonSmoothForceNode,
		           *(static_cast<ffp::SecondOrderConeForce*>(
					   params.p_nonSmoothForce.get())));
	} else if (nonSmoothForceName == "non_smooth_contact") {
		params.nonSmoothForceType = NonSmoothForceType::NON_SMOOTH_CONTACTS;
		params.p_nonSmoothForce =
			std::make_unique<ffp::NonSmoothContactForce>();
		loadParams(nonSmoothForceNode,
		           *(static_cast<ffp::NonSmoothContactForce*>(
					   params.p_nonSmoothForce.get())));
	} else if (nonSmoothForceName == "normalized") {
		params.nonSmoothForceType =
			NonSmoothForceType::NON_SMOOTH_CONTACTS_NORMALIZED;
		params.p_nonSmoothForce =
			std::make_unique<ffp::NormalizedContactForce>();
		loadParams(nonSmoothForceNode,
		           *(static_cast<ffp::NormalizedContactForce*>(
					   params.p_nonSmoothForce.get())));
	} else if (nonSmoothForceName == "only_normal") {
		params.nonSmoothForceType = NonSmoothForceType::ONLY_NORMAL_FORCE;
		params.p_nonSmoothForce = std::make_unique<ffp::OnlyNormalForce>();
		loadParams(nonSmoothForceNode, *(static_cast<ffp::OnlyNormalForce*>(
										   params.p_nonSmoothForce.get())));
	}
}
void loadParams(const YAML::Node& node, ffp::PeriodicWorld& params) {
	params.center = parseVector3<Scalar>(node, "center", "rigid_body_world");
	params.scale = parseVector3<Scalar>(node, "scale", "rigid_body_world");
}
void loadParams(const YAML::Node& node, ffp::DynamicSystem& params) {
	params.timestep = parseScalar<Scalar>(node, "timestep", 1e-2, "simulation");
	if (node["solver"].IsDefined()) {
		const YAML::Node& solverNode = node["solver"];
		std::string solverName = solverNode["name"].as<std::string>();
		if (solverName == "primal_dual") {
			params.forceSolverType = ForceSolverType::PrimalDual;
			params.p_solver = std::make_unique<ffp::PrimalDualForceSolver>();
			loadParams(solverNode, *static_cast<ffp::PrimalDualForceSolver*>(
									   params.p_solver.get()));
		} else if (solverName == "null") {
			params.forceSolverType = ForceSolverType::Null;
			params.p_solver = std::make_unique<ffp::ForceSolver>();
		} else {
			throw std::runtime_error("No solver of name: " + solverName +
			                         "found!");
		}
	} else {
		throw std::runtime_error("No force solver specified!");
	}
	if (node["gravity"].IsDefined()) {
		params.gravity = parseVector3<Scalar>(node, "gravity", "simulation");
	}
	if (node["rigid_body_world"].IsDefined()) {
		const YAML::Node& worldNode = node["rigid_body_world"];
		std::string worldName = worldNode["name"].as<std::string>();
		if (worldName == "euclidean") {
			throw std::invalid_argument(
				"Homogenization program only accepts periodic rigid body "
				"world!");
		} else if (worldName == "periodic") {
			params.worldType = RigidWorldType::PERIODIC;
			params.p_rigidWorld = std::make_unique<ffp::PeriodicWorld>();
			loadParams(worldNode, *static_cast<ffp::PeriodicWorld*>(
									  params.p_rigidWorld.get()));
		} else {
			throw std::runtime_error(
				"No rigid body world of name: " + worldName + "found!");
		}
	} else {
		params.worldType = RigidWorldType::EUCLIDEAN;
		params.p_rigidWorld = std::make_unique<ffp::RigidBodyWorld>();
	}
	params.adaptiveTimestep =
		parseScalar<bool>(node, "adaptive_timestep", false, "simulation");
	if (params.adaptiveTimestep) {
		params.substepFactor =
			parseScalar<Scalar>(node, "substep_factor", 10, "simulation");
	}
}
void loadExpParams(const YAML::Node& node, Params::StaticPressShear& params) {
	params.pressFractionIncrement =
		parseScalar<Scalar>(node, "press_fraction", "StaticPressShearOrtho");
	params.shearMax =
		parseScalar<Scalar>(node, "shear_fraction", "StaticPressShearOrtho");
	params.decay =
		parseScalar<Scalar>(node, "decay", 0.95, "StaticPressShearOrtho");
	params.speedTol =
		parseScalar<Scalar>(node, "speed_tol", 1e-3, "StaticPressShearOrtho");
	params.stressTol =
		parseScalar<Scalar>(node, "stress_tol", 0.95, "StaticPressShearOrtho");
	params.stressUpperLimit =
		parseScalar<Scalar>(node, "stress_limit", 3e4, "StaticPressShearOrtho");
	params.stressSearchFactor = parseScalar<Scalar>(
		node, "stress_search_factor", 0.1, "StaticPressShearOrtho");
	params.stressLowerLimit = parseScalar<Scalar>(node, "stress_lower_limit", 0,
	                                              "StaticPressShearOrtho");
	params.shearIncrements = parseScalar<uint16_t>(node, "shear_increments", 20,
	                                               "StaticPressShearOrtho");
	params.pressSearchIterations = parseScalar<uint16_t>(
		node, "press_iterations", 2, "StaticPressShearOrtho");
	params.shearMicroInc = parseScalar<Scalar>(node, "shear_micro_inc", 1,
	                                           "StaticPressShearOrtho");
	params.biaxialStretch = parseScalar<bool>(node, "biaxial_stretch", false,
	                                          "StaticPressShearOrtho");
	params.shearDir = parseVector3<int>(node, "shear_dir", Vector3i(1, -1, 0),
	                                    "StaticPressShearOrtho");
}
void loadExpParams(const YAML::Node& node, Params::StaticPress& params) {
	params.pressFractionIncrement =
		parseScalar<Scalar>(node, "press_fraction", "StaticPress");
	params.decay = parseScalar<Scalar>(node, "decay", 0.95, "StaticPress");
	params.speedTol =
		parseScalar<Scalar>(node, "speed_tol", 1e-3, "StaticPress");
	params.stressTol =
		parseScalar<Scalar>(node, "stress_tol", 0.95, "StaticPress");
	params.stressUpperLimit =
		parseScalar<Scalar>(node, "stress_limit", 3e4, "StaticPress");
	params.stressSearchFactor =
		parseScalar<Scalar>(node, "stress_search_factor", 0.1, "StaticPress");
	params.stressLowerLimit =
		parseScalar<Scalar>(node, "stress_lower_limit", 0, "StaticPress");
	params.shearIncrements =
		parseScalar<uint16_t>(node, "shear_increments", 20, "StaticPress");
	params.pressSearchIterations =
		parseScalar<uint16_t>(node, "press_iterations", 2, "StaticPressShear");
}
void loadExpParams(const YAML::Node& node, Params::EmptyExperiment& params) {
	params.duration = parseScalar<Scalar>(node, "duration", "EmptyExperiment");
}
void loadExpParams(const YAML::Node& node, Params::Brownian& params) {
	params.duration = parseScalar<Scalar>(node, "duration", "Brownian");
	params.magnitudeStd = parseScalar<Scalar>(node, "std", "Brownian");
	params.seed = parseScalar<Scalar>(node, "seed", time(NULL), "Brownian");
}
void loadExpParams(const YAML::Node& node,
                   Params::BoundaryScaleSearch& params) {
	params.scaleSpeed =
		parseScalar<Scalar>(node, "scale_speed", "BoundaryScaleSearch");
	params.decay =
		parseScalar<Scalar>(node, "decay", 0.5, "BoundaryScaleSearch");
	params.shrinkThresh = parseScalar<Scalar>(node, "shrink_threshold", 3e3,
	                                          "BoundaryScaleSearch");
	params.expandThresh = parseScalar<Scalar>(node, "expand_threshold", 1e-2,
	                                          "BoundaryScaleSearch");
	params.haltDur =
		parseScalar<Scalar>(node, "halt", 1e-2, "BoundaryScaleSearch");
	params.iterations = parseScalar<unsigned short>(node, "iterations", 1,
	                                                "BoundaryScaleSearch");
}
}  // namespace IO
}  // namespace Homogenization
