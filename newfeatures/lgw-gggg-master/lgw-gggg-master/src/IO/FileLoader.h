#pragma once

#include <Corrade/Containers/Array.h>
#include <Corrade/Containers/Optional.h>
#include <Corrade/Containers/Pair.h>
#include <Corrade/PluginManager/Manager.h>
#include <Magnum/Magnum.h>
#include <Magnum/Primitives/Cube.h>
#include <Magnum/Primitives/Icosphere.h>
#include <Magnum/Trade/AbstractImporter.h>
#include <Magnum/Trade/MeshData.h>
#include <Magnum/Trade/SceneData.h>
#include <yaml-cpp/yaml.h>

#include <filesystem>
#include <memory>
#include <string>

#include "Common/RNG.h"
#include "UI/SimulationSceneCLI.h"
namespace Homogenization {
namespace IO {
class FileLoader {
   public:
	/**
	 * Load a YAML file
	 */
	void loadFile(UI::SimulationSceneCLI& sScene,
	              const std::string& fileName,
	              bool GUI);
	void loadLoggingOptions(UI::SimulationSceneCLI& sScene,
	                        const YAML::Node& node);
	void loadScene(UI::SimulationSceneCLI& sScene,
	               const YAML::Node& yamlNode,
	               std::filesystem::path& path,
	               bool GUI);

   protected:
	void generateObjects(
		UI::SimulationSceneCLI& sScene,
		const YAML::Node& node,
		std::vector<FrictionFrenzy::CollisionObject::Type>& objTypes,
		int edgeSize,
		UniformIntSampler& rng,
		bool GUI);
	void loadMesh(UI::SimulationSceneCLI& sScene,
	              const YAML::Node& node,
	              std::filesystem::path& path,
	              const Magnum::Containers::Optional<Magnum::Trade::MeshData>&
	                  renderMeshData,
	              bool GUI);
	void loadExperiments(UI::SimulationSceneCLI& sScene,
	                     const YAML::Node& node);
	std::unique_ptr<Vector3SamplerBase<FrictionFrenzy::Scalar>> makeScaleRNG(
		const YAML::Node& node,
		UniformIntSampler& rng);
	template <typename T>
	void generatePrimitive(UI::SimulationSceneCLI& sScene,
	                       size_t meshId,
						   int sdfRes,
	                       FrictionFrenzy::Affine& transform,
	                       Magnum::Color4& c,
	                       bool GUI);
};
}  // namespace IO
}  // namespace Homogenization
