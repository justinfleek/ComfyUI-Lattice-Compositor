#pragma once

#include "SimulationSceneCLI.h"

#include <Magnum/Animation/Track.h>
#include <Magnum/GL/Mesh.h>
#include <Magnum/Magnum.h>
#include <Magnum/MeshTools/Compile.h>
#include <Magnum/Primitives/Axis.h>
#include <Magnum/SceneGraph/Drawable.h>

#include <memory>
#include <vector>

#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/Magnum.h>
#include <Magnum/SceneGraph/SceneGraph.h>
#include <Magnum/Shaders/PhongGL.h>
#include "Cameras/ArcBallCamera.h"
#include "Common/MagnumTypes.h"
#include "Common/MatrixTypes.h"
#include "Drawables/ColoredDrawable.h"
#include "Dynamics/DynamicSystem.h"
#include "Experiments/ExperimentBase.h"

namespace Homogenization {
namespace UI {

using Magnum::SceneGraph::DrawableGroup3D, Magnum::Shaders::PhongGL;

/**
 * Simulation scene for the GUI program, which includes information for cameras,
 * rendered 3D meshes, and shaders.
 */
class SimulationScene : public SimulationSceneCLI {
   public:
	SimulationScene();

	/**
	 * Advance one frame of the simulation. This can consist of mny substeps.
	 */
	void advanceOneFrame() override;

	/**
	 * Clear dynamics.
	 */
	void clearAll() override;

	/**
	 * Draw the current frame
	 */
	void drawScene(Magnum::Camera::ArcBallCamera& camera);

	/**
	 * Update all Magnum drawables.
	 */
	void updateAllDrawables() {
		for (size_t i = 0; i < m_rigidDrawables.size(); ++i) {
			m_rigidDrawables[i]->updateTransformation();
		}
	}

	/**
	 * Update a single Magnum drawables.
	 *
	 * @param[in] id: the drawable id
	 */
	void updateDrawable(size_t id) {
		m_rigidDrawables[id]->updateTransformation();
	}

	// Accessors

	/**
	 * Whether contacts are show in GUI.
	 */
	bool& showContacts() { return m_showContacts; }

	/**
	 * Return scale of the contact visualization.
	 */
	FrictionFrenzy::Scalar& contactAxisScale() { return m_contactAxisScale; }

	/**
	 * Access Magnum scene graph data.
	 */
	Magnum::Scene3D& magnumScene() { return m_scene; }

	/**
	 * Access Phong shader for objects.
	 */
	PhongGL* getObjectShader() { return mp_coloredShader.get(); }

	/**
	 * Access light positions.
	 */
	std::vector<Magnum::Vector4>& lightPositions() { return m_lightPositions; }

	/**
	 * Access light colors.
	 */
	std::vector<Magnum::Color3>& lightColors() { return m_lightColors; }

	/**
	 * Access Magnum drawable group.
	 */
	DrawableGroup3D& getDrawableGroup() { return m_drawables; }

	/**
	 * Return the playback timestep
	 */
	Homogenization::Scalar& playbackTimestep() { return m_playbackTimestep; }

	/**
	 * Return number of GL meshes.
	 */
	size_t nMeshes() { return m_meshes.size(); }

	/**
	 * Access the GL mesh with ID
	 *
	 * @param[in] id: The mesh ID to access.
	 */
	Magnum::GL::Mesh* getMesh(size_t id) { return m_meshes[id].get(); }

	/**
	 * Add a GL mesh from mesh data.
	 *
	 * @params[in] meshData: the mesh data to add.
	 */
	void addMesh(const Magnum::Trade::MeshData& meshData) {
		Magnum::MeshTools::CompileFlags flags;
		m_meshes.push_back(
			std::make_unique<Magnum::GL::Mesh>(Magnum::NoCreate));
		*m_meshes.back() = Magnum::MeshTools::compile(meshData, flags);
	}

	/**
	 * Access the drawable with ID
	 *
	 * @param[in] id: The id to access.
	 */
	Magnum::RigidDrawable3D& getDrawable(size_t id) {
		return *(m_rigidDrawables[id]);
	}
	/**
	 * Does the scene have drawables
	 */
	bool hasDrawables() const { return !m_rigidDrawables.empty(); }

	/**
	 * Add one drawable.
	 *
	 * @param[in] drb: the Magnum drawable to add.
	 */
	void addDrawable(std::unique_ptr<Magnum::RigidDrawable3D> drb) {
		m_rigidDrawables.push_back(std::move(drb));
	}

	void assignRigidWorld(std::unique_ptr<Magnum::GL::Mesh>&& wld) {
		mp_rigidWorldMesh = std::move(wld);
	}

	void initializeRigidWorld();

	std::list<std::unique_ptr<Experiments::ExperimentBase>>& getExperiments() {
		return m_experiments;
	}
	std::list<std::unique_ptr<Experiments::ExperimentBase>>::iterator&
	getCurrentExperiment() {
		return m_currExperiment;
	}

   protected:
	Magnum::Scene3D m_scene;
	DrawableGroup3D m_drawables;
	std::vector<Magnum::Vector4> m_lightPositions{{-5, 1, 5, 0},
	                                              {5, 1, 5, 0},
	                                              {2, 1, -5, 0}};
	std::vector<Magnum::Color3> m_lightColors{Magnum::Color3(1.f, 1.f, 1.f),
	                                          Magnum::Color3(0.5f, 0.5f, 0.5f),
	                                          Magnum::Color3(1, 1, 1)};
	FrictionFrenzy::Scalar m_playbackTimestep = 1. / 60;
	FrictionFrenzy::Scalar m_contactAxisScale = 1.0;
	bool m_showContacts = false;

	std::unique_ptr<Magnum::GL::Mesh> mp_rigidWorldMesh;

	std::vector<std::unique_ptr<Magnum::GL::Mesh>> m_meshes;
	std::vector<std::unique_ptr<Magnum::RigidDrawable3D>> m_rigidDrawables;
	std::unique_ptr<PhongGL> mp_coloredShader;
	std::unique_ptr<Magnum::Shaders::FlatGL3D> mp_axisShader;
	std::unique_ptr<Magnum::Shaders::FlatGL3D> mp_worldShader;
	Magnum::GL::Mesh m_axisMesh;
};
}  // namespace UI
}  // namespace Homogenization
