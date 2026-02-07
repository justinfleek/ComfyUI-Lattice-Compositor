#include "FileLoader.h"
#include <Magnum/Magnum.h>
#include <limits>
#include <memory>
#include <stdexcept>
#include "CollisionObject/CollisionObject.h"
// #include "Common/InputParse.h"
#include "Common/MatrixTypes.h"
#include "Corrade/Utility/Debug.h"
#include "Drawables/ColoredDrawable.h"
#include "Dynamics/DynamicSystem.h"
#include "Dynamics/PeriodicWorld.h"
#include "Dynamics/RigidBodyWorld.h"
#include "Experiments/BoundaryScaleSearch.h"
#include "Experiments/Brownian.h"
#include "Experiments/ExperimentBase.h"
#include "Experiments/StaticPress.h"
#include "Experiments/StaticPressShear.h"
#include "Magnum/Primitives/Cube.h"
#include "Magnum/Primitives/Icosphere.h"
#include "Magnum/Trade/MeshData.h"
#include "UI/SimulationScene.h"

#include "Common/RNG.h"
#include "ParamLoad.h"

namespace Homogenization {
namespace IO {
namespace ff = FrictionFrenzy;
void FileLoader::loadFile(UI::SimulationSceneCLI& sScene,
                          const std::string& fileName,
                          bool GUI) {
	YAML::Node rootNode = YAML::LoadFile(fileName);
	YAML::Node sceneNode = rootNode["scene"];
	std::filesystem::path path(fileName);
	std::cout << "Opening file: " << path << std::endl;

	if (rootNode["simulation"]) {
		YAML::Node simNode = rootNode["simulation"];

		if (!simNode["rigid_body_world"] ||
		    simNode["rigid_body_world"]["name"].as<std::string>() !=
		        "periodic") {
			simNode["rigid_body_world"]["name"] = "periodic";
			YAML::Node rbwNode = simNode["rigid_body_world"];
			rbwNode["center"].push_back(0);
			rbwNode["center"].push_back(0);
			rbwNode["center"].push_back(0);
			rbwNode["scale"].push_back(1);
			rbwNode["scale"].push_back(1);
			rbwNode["scale"].push_back(1);
		}
		if (simNode["gravity"]) {
			YAML::Node gNode = simNode["gravity"];
			if (gNode.IsSequence() && gNode.size() == 3) {
				gNode[0] = 0;
				gNode[1] = 0;
				gNode[2] = 0;
			} else {
				throw std::runtime_error(
					"Gravity setting must be sequence of size 3!");
			}
		} else {
			simNode["gravity"].push_back(0);
			simNode["gravity"].push_back(0);
			simNode["gravity"].push_back(0);
		}
	}

	sScene.clearAll();
	FrictionFrenzy::Params::DynamicSystem params;
	loadParams(rootNode["simulation"], params);
	params.adaptiveTimestep = false;
	params.substepFactor = 1;
	sScene.dynamicSystem().fillFromParams(params);
	// sScene.dynamicSystem().fillFromYAML(rootNode["simulation"]);
	// sScene.dynamicSystem().adaptiveTimestep() = false;
	// sScene.dynamicSystem().substeps() = 1;

	if (sScene.dynamicSystem().rigidBodyWorld()->getType() !=
	    ff::Dynamics::RigidWorldType::PERIODIC) {
		throw std::runtime_error(
			"Homogenization only accepts periodic boundary conditions!");
	}
	if (GUI) {
		sScene.clearAll();
	}
	loadScene(sScene, sceneNode, path, GUI);

	sScene.dynamicSystem().renderCollisionGeometry() = parseScalar<bool>(
		rootNode["baking"], "output_collision_geometry", true, "baking");
	loadLoggingOptions(sScene, rootNode);

	loadExperiments(sScene, rootNode["experiments"]);

	auto rigidWorld = dynamic_cast<ff::Dynamics::PeriodicWorld*>(
		sScene.dynamicSystem().rigidBodyWorld());
	rigidWorld->updateDeformation(
		rigidWorld->getCenter(), rigidWorld->getScale() * 1.5,
		rigidWorld->getShear(), sScene.dynamicSystem().getObjectArray());

	if (GUI) {
		dynamic_cast<UI::SimulationScene*>(&sScene)->initializeRigidWorld();
	}
}
void FileLoader::loadLoggingOptions(UI::SimulationSceneCLI& sScene,
                                    const YAML::Node& node) {
	if (node["logging"].IsDefined()) {
		std::string logOp = node["logging"].as<std::string>();
		if (logOp == "all") {
			*sScene.mp_logging = 0 - 1;
		} else if (logOp == "none") {
			*sScene.mp_logging = 0;
		}
	}
}
void FileLoader::loadScene(UI::SimulationSceneCLI& sScene,
                           const YAML::Node& yamlNode,
                           std::filesystem::path& path,
                           bool GUI) {
	const YAML::Node& geoNode = yamlNode["geometry"];
	if (!geoNode.IsSequence()) {
		throw std::runtime_error("Node \"geometry\" is not a sequence!");
	}
	std::vector<ff::CollisionObject::Type> objTypes(geoNode.size());
	for (int i = 0; i < geoNode.size(); ++i) {
		const YAML::Node& geo = geoNode[i];
		const std::string geoType = geo["type"].as<std::string>();

		typedef Magnum::Containers::Optional<Magnum::Trade::MeshData>
			MeshDataOp;
		MeshDataOp mesh;

		if (geoType == "cube") {
			mesh = MeshDataOp(Magnum::Primitives::cubeSolid());
			objTypes[i] = ff::CollisionObject::Type::CUBE;
		} else if (geoType == "ellipsoid") {
			mesh = MeshDataOp(Magnum::Primitives::icosphereSolid(4));
			objTypes[i] = ff::CollisionObject::Type::ELLIPSOID;
		} else if (geoType == "sphere") {
			mesh = MeshDataOp(Magnum::Primitives::icosphereSolid(4));
			objTypes[i] = ff::CollisionObject::Type::SPHERE;
		} else if (geoType == "mesh") {
			objTypes[i] = ff::CollisionObject::Type::MESH;
		} else if (geoType == "convex") {
			mesh = MeshDataOp(Magnum::Primitives::icosphereSolid(4));
			objTypes[i] = ff::CollisionObject::Type::CONVEX;
		} else {
			throw std::runtime_error("Unknown geometry type: " + geoType);
		}
		loadMesh(sScene, geo, path, mesh, GUI);
	}
	UniformIntSampler rngSeed(
		parseScalar<int>(yamlNode, "seed", time(NULL), ""));
	int edgeSize = parseScalar<int>(yamlNode, "edge_size", "loadScene");
	generateObjects(sScene, geoNode, objTypes, edgeSize, rngSeed, GUI);

	auto& dynamics = sScene.dynamicSystem();
	dynamics.initialize();

	ff::Scalar density =
		parseScalar<ff::Scalar>(yamlNode, "density", 1000, "");
	ff::Scalar mass = 0;
	ff::Vector3 shift = ff::Vector3::Zero();
	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);
		obj.updateDensity(density);
		mass += obj.mass();
		shift += obj.getTranslation() * obj.mass();
	}
	shift =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld())
			->getCenter() -
		shift / mass;
	for (int i = 0; i < dynamics.nObjects(); ++i) {
		auto& obj = dynamics.getObject(i);
		ff::Vector3 newTranslate = obj.getTranslation() + shift;
		// obj.setOrigTranslation(newTranslate);
		obj.setTranslation(newTranslate);
	}
}
void FileLoader::generateObjects(
	UI::SimulationSceneCLI& sScene,
	const YAML::Node& node,
	std::vector<ff::CollisionObject::Type>& objTypes,
	int edgeSize,
	UniformIntSampler& rngSeed,
	bool GUI) {
	auto& dynamics = sScene.dynamicSystem();
	auto rigidWorld =
		dynamic_cast<ff::Dynamics::PeriodicWorld*>(dynamics.rigidBodyWorld());
	std::vector<double> fractions(node.size());
	std::vector<size_t> integer(node.size());
	std::vector<ff::Vector3> baseScale(node.size());
	std::vector<int> sdfRes(node.size());

	std::vector<std::unique_ptr<Vector3SamplerBase<ff::Scalar>>> scaleRng(
		node.size());

	ff::Scalar maxScale = 0;
	for (int i = 0; i < node.size(); ++i) {
		const YAML::Node& geo = node[i];
		fractions[i] = geo["fraction"].as<double>();
		integer[i] = i;
		if (geo["base_scale"].IsDefined() && geo["base_scale"].IsSequence()) {
			baseScale[i] = parseVectorEigen<ff::Scalar, 3>(
				geo, "base_scale", "generateObjects: base_scale");
		} else {
			ff::Scalar scale = parseScalar<ff::Scalar>(
				geo, "base_scale", 1, "generateObjects: base_scale");
			baseScale[i] = ff::Vector3(scale, scale, scale);
		}
		scaleRng[i] = makeScaleRNG(geo["scale"], rngSeed);
		sdfRes[i] = parseScalar<int>(geo, "resolution", 0,
		                                 "generateObjects: resolution");
		maxScale = std::max(
			baseScale[i].cwiseProduct(scaleRng[i]->max()).maxCoeff(), maxScale);
	}

	DiscreteRandom<size_t> meshRng(integer, fractions, rngSeed.sample());
	UniformSampler<float> posRng(-0.5, 0.5, rngSeed.sample());
	UniformSampler<float> rotRng(-5, 5, rngSeed.sample());
	UniformSampler<float> rngHue(0, 360, rngSeed.sample());
	UniformSampler<float> rngSat(0.0, 0.3, rngSeed.sample());
	UniformSampler<float> rngVal(0.6, 1.0, rngSeed.sample());

	// maxScale *= 1.74;

	rigidWorld->getScale().setConstant(2 * maxScale * edgeSize);

	ff::Vector3 minExtent =
		rigidWorld->getCenter() - 0.5001 * rigidWorld->getScale();
	ff::Vector3 maxExtent =
		rigidWorld->getCenter() + 0.5001 * rigidWorld->getScale();
	minExtent.array() += maxScale;
	maxExtent.array() -= maxScale;
	for (ff::Scalar i = minExtent[0]; i < maxExtent[0]; i += maxScale * 2) {
		for (ff::Scalar j = minExtent[1]; j < maxExtent[1]; j += maxScale * 2) {
			for (ff::Scalar k = minExtent[2]; k < maxExtent[2];
			     k += maxScale * 2) {
				size_t meshId = meshRng.sample();
				ff::Vector3 translate(i, j, k);
				ff::Vector3 rot(rotRng.sample(), rotRng.sample(),
				                rotRng.sample());
				ff::Vector3 scale = scaleRng[meshId]->sample();
				ff::Affine t = ff::Affine::Identity();
				t = t.translate(translate)
				        .rotate(ff::AngleAxis(rot.norm(), rot.normalized()))
				        .scale(scale)
				        .scale(baseScale[meshId]);
				Magnum::Color4 c = Magnum::Color4::fromHsv(
					Magnum::ColorHsv(Magnum::Deg(rngHue.sample()),
				                     rngSat.sample(), rngVal.sample()),
					1.0);
				switch (objTypes[meshId]) {
				case ff::CollisionObject::Type::MESH: {
					generatePrimitive<ff::CollisionObject::Mesh>(
						sScene, meshId, sdfRes[meshId], t, c, GUI);
					break;
				}
				case ff::CollisionObject::Type::CONVEX: {
					generatePrimitive<ff::CollisionObject::Convex>(
						sScene, meshId, sdfRes[meshId], t, c, GUI);
					break;
				}
				case ff::CollisionObject::Type::CUBE: {
					generatePrimitive<ff::CollisionObject::Cube>(
						sScene, meshId, sdfRes[meshId], t, c, GUI);
					break;
				}
				case ff::CollisionObject::Type::SPHERE: {
					generatePrimitive<ff::CollisionObject::Sphere>(
						sScene, meshId, sdfRes[meshId], t, c, GUI);
					break;
				}
				case ff::CollisionObject::Type::ELLIPSOID: {
					generatePrimitive<ff::CollisionObject::Ellipsoid>(
						sScene, meshId, sdfRes[meshId], t, c, GUI);
					break;
				}
				default:;
				}
			}
		}
	}
}
void FileLoader::loadMesh(
	UI::SimulationSceneCLI& sScene,
	const YAML::Node& node,
	std::filesystem::path& path,
	const Magnum::Containers::Optional<Magnum::Trade::MeshData>& renderMeshData,
	bool GUI) {
	auto convertMagnumMeshData =
		[](const Magnum::Trade::MeshData& data,
	       std::unique_ptr<ff::CollisionObject::CPUMeshData>& meshData) {
			meshData = std::make_unique<ff::CollisionObject::CPUMeshData>();
			for (size_t i = 0; i < data.attributeCount(); ++i) {
				if (data.attributeName(i) ==
			        Magnum::Trade::MeshAttribute::Position) {
					const auto pArray =
						Magnum::Containers::arrayCast<1, const Magnum::Vector3,
				                                      2>(data.attribute(i));
					meshData->positions_Eigen.resize(pArray.size(), 3);
					for (size_t j = 0; j < pArray.size(); ++j) {
						meshData->positions_Eigen.row(j) << pArray[j].x(),
							pArray[j].y(), pArray[j].z();
					}
				}
			}
			auto iArrayRaw = data.indicesAsArray();
			auto iArray =
				Magnum::Containers::arrayCast<Magnum::Vector3ui>(iArrayRaw);
			meshData->indices_Eigen =
				std::make_shared<ff::MatrixX3i>(iArray.size(), 3);
			for (size_t j = 0; j < iArray.size(); ++j) {
				(*meshData->indices_Eigen)(j, 0) = iArray[j][0];
				(*meshData->indices_Eigen)(j, 1) = iArray[j][1];
				(*meshData->indices_Eigen)(j, 2) = iArray[j][2];
			}
		};

	Magnum::PluginManager::Manager<Magnum::Trade::AbstractImporter> manager;
	Corrade::Containers::Pointer<Magnum::Trade::AbstractImporter> importer =
		manager.loadAndInstantiate("AnySceneImporter");

	UI::SimulationScene* p_sSceneGUI =
		dynamic_cast<UI::SimulationScene*>(&sScene);
	auto& dynamics = sScene.dynamicSystem();

	if (renderMeshData) {
		if (GUI) {
			p_sSceneGUI->addMesh(*renderMeshData);
		}
		std::unique_ptr<ff::CollisionObject::CPUMeshData> meshData;
		convertMagnumMeshData(*renderMeshData, meshData);
		dynamics.addMesh(std::move(meshData));
		return;
	}

	std::string fileName = path.parent_path() / node["name"].as<std::string>();
	Magnum::Debug{} << "loading file: " << fileName.c_str();

	if (!importer || !importer->openFile(fileName)) {
		throw std::runtime_error("Cannot open file" + fileName + "!");
	}
	if (importer->meshCount() != 1) {
		throw std::runtime_error("Error in " + fileName +
		                         ": must have exactly one mesh!");
	}

	Magnum::Containers::Optional<Magnum::Trade::MeshData> magnumMeshData =
		importer->mesh(0);
	if (magnumMeshData) {
		std::unique_ptr<ff::CollisionObject::CPUMeshData> cpuMeshData;
		convertMagnumMeshData(*magnumMeshData, cpuMeshData);
		if (GUI) {
			p_sSceneGUI->addMesh(*magnumMeshData);
		}
		dynamics.addMesh(std::move(cpuMeshData));
	} else {
		throw std::runtime_error("Cannot read mesh in " + fileName + "!");
	}
}

std::unique_ptr<Vector3SamplerBase<FrictionFrenzy::Scalar>>
FileLoader::makeScaleRNG(const YAML::Node& node, UniformIntSampler& rng) {
	typedef RNG1DBase<ff::Scalar> scalarSampler;
	auto makeScalarSampler = [](const YAML::Node& node,
	                            UniformIntSampler& rng) {
		std::shared_ptr<scalarSampler> ret = nullptr;
		std::string samplerType = node["type"].as<std::string>();
		if (samplerType == "constant") {
			ff::Scalar scale = parseScalar<ff::Scalar>(
				node, "scale", "makeScaleRNG: constant");
			ret = std::make_shared<ConstSampler<ff::Scalar>>(scale);
		} else if (samplerType == "uniform") {
			ff::Scalar min = parseScalar<ff::Scalar>(
				node, "min", "makeScaleRNG: uniform");
			ff::Scalar max = parseScalar<ff::Scalar>(
				node, "max", "makeScaleRNG: uniform");
			ret = std::make_shared<UniformSampler<ff::Scalar>>(min, max,
			                                                   rng.sample());
		} else if (samplerType == "gaussian") {
			ff::Scalar mean = parseScalar<ff::Scalar>(
				node, "mean", "makeScaleRNG: gaussian");
			ff::Scalar std = parseScalar<ff::Scalar>(
				node, "std", "makeScaleRNG: gaussian");
			ff::Scalar clamp = parseScalar<ff::Scalar>(
				node, "clamp", "makeScaleRNG: gaussian");
			ret = std::make_shared<GaussianSampler<ff::Scalar>>(
				mean, std, clamp, rng.sample());
		}
		return ret;
	};
	std::array<std::shared_ptr<RNG1DBase<ff::Scalar>>, 3> samplers;
	if (node.IsMap()) {
		samplers[0] = makeScalarSampler(node, rng);
		samplers[1] = samplers[0];
		samplers[2] = samplers[0];
		std::string dimensions = node["dimensions"].as<std::string>();
		if (dimensions == "uniform") {
			return std::make_unique<IdenticalVector3Sampler<ff::Scalar>>(
				samplers[0]);
		} else if (dimensions == "independent") {
			return std::make_unique<IIDVector3Sampler<ff::Scalar>>(
				samplers[0], samplers[1], samplers[2]);
		} else {
			throw std::runtime_error("Unknown distribution type: " +
			                         dimensions);
		}
	} else if (node.IsSequence()) {
		if (node.size() != 3) {
			throw std::runtime_error(
				"Scale entry must be a map or sequence of size 3");
		}
		for (int i = 0; i < 3; ++i) {
			samplers[i] = makeScalarSampler(node[i], rng);
		}
		return std::make_unique<IIDVector3Sampler<ff::Scalar>>(
			samplers[0], samplers[1], samplers[2]);
	} else {
		throw std::runtime_error(
			"Scale entry must be a map or sequence of size 3");
	}
}

template <typename T>
void FileLoader::generatePrimitive(UI::SimulationSceneCLI& sScene,
                                   size_t meshId,
                                   int sdfRes,
                                   ff::Affine& transform,
                                   Magnum::Color4& c,
                                   bool GUI) {
	UI::SimulationScene* p_sSceneGUI =
		dynamic_cast<UI::SimulationScene*>(&sScene);
	auto& dynamics = sScene.dynamicSystem();
	size_t objId = dynamics.nObjects();
	ff::CollisionObject::CPUMeshData *meshData = dynamics.getMeshData(meshId),
									 *collMeshData = meshData;
	std::unique_ptr<ff::CollisionObject::RigidObjectBase> obj =
		std::make_unique<T>(objId, meshData, collMeshData);

	if (GUI) {
		Magnum::GL::Mesh* mesh = p_sSceneGUI->getMesh(meshId);
		std::unique_ptr<Magnum::RigidDrawable3D> drb =
			std::make_unique<Magnum::RigidDrawable3D>(
				&p_sSceneGUI->magnumScene(), p_sSceneGUI->getObjectShader(),
				mesh, obj.get(), c, p_sSceneGUI->getDrawableGroup(),
				p_sSceneGUI->lightPositions(), p_sSceneGUI->lightColors(),
				objId, Magnum::Matrix4());
		p_sSceneGUI->addDrawable(std::move(drb));
	}

	obj->setPermanentTrans(transform.matrix());
	if (GUI) {
		p_sSceneGUI->getDrawable(objId).updateTransformation();
	}
	if constexpr (std::is_same<T, ff::CollisionObject::Mesh>::value) {
		dynamic_cast<ff::CollisionObject::Mesh*>(obj.get())->setGridSDF(sdfRes);
	}
	dynamics.addObject(std::move(obj));
}

void FileLoader::loadExperiments(UI::SimulationSceneCLI& sScene,
                                 const YAML::Node& node) {
	if (!node.IsDefined()) {
		throw std::runtime_error(
			"loadExperiments: \"experiments\" must be defined!");
	}
	if (!node.IsSequence()) {
		throw std::runtime_error(
			"loadExperiments: \"experiments\" must be a sequence!");
	}
	for (int i = 0; i < node.size(); ++i) {
		const YAML::Node& expNode = node[i];
		std::string name = expNode["name"].as<std::string>();
		std::unique_ptr<Params::Experiment> params;
		if (name == "brownian") {
			params = std::make_unique<Params::Brownian>();
			loadExpParams(expNode, params->cast<Params::Brownian>());
			sScene.getExperiments().push_back(
				std::make_unique<Experiments::Brownian>());
		} else if (name == "boundary_scale_search") {
			params = std::make_unique<Params::BoundaryScaleSearch>();
			loadExpParams(expNode, params->cast<Params::BoundaryScaleSearch>());
			sScene.getExperiments().push_back(
				std::make_unique<Experiments::BoundaryScaleSearch>());
		} else if (name == "static_press") {
			params = std::make_unique<Params::StaticPress>();
			loadExpParams(expNode, params->cast<Params::StaticPress>());
			sScene.getExperiments().push_back(
				std::make_unique<Experiments::StaticPress>());
		} else if (name == "static_press_shear") {
			params = std::make_unique<Params::StaticPressShear>();
			loadExpParams(expNode, params->cast<Params::StaticPressShear>());
			sScene.getExperiments().push_back(
				std::make_unique<Experiments::StaticPressShear>());
		} else {
			throw std::runtime_error("loadExperiments: no experiment named \"" +
			                         name + "\"!");
		}
		sScene.getExperiments().back()->fillFromParams(*params);
		// sScene.getExperiments().back()->fillFromYAML(expNode);
	}
	sScene.getExperiments().front()->setStartTime(0);
	sScene.getCurrentExperiment() = sScene.getExperiments().begin();
}
}  // namespace IO
}  // namespace Homogenization
