#include "SimulationScene.h"
#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/Magnum.h>
#include <Magnum/MeshTools/Compile.h>
#include <Magnum/Primitives/Axis.h>
#include <Magnum/Trade/MeshData.h>
#include <imgui.h>
#include <filesystem>
#include <functional>
#include <memory>
#include "Common/LoggingOptions.h"
#include "Common/MagnumTypes.h"
#include "Common/MatrixTypes.h"
#include "Drawables/ColoredDrawable.h"
#include "Dynamics/PeriodicWorld.h"
#include "Dynamics/RigidBodyWorld.h"
#include "Experiments/ExperimentBase.h"
#include "Magnum/Primitives/Cube.h"
#include "Magnum/SceneGraph/SceneGraph.h"
#include "Magnum/Tags.h"
namespace Homogenization {
namespace UI {
namespace ff = FrictionFrenzy;
SimulationScene::SimulationScene() : SimulationSceneCLI() {
	using namespace Magnum::Math::Literals;

	mp_coloredShader = std::make_unique<Magnum::Shaders::PhongGL>(
		Magnum::Shaders::PhongGL::Flag::ObjectId, m_lightPositions.size());
	(*mp_coloredShader)
		.setAmbientColor(0x010101_rgbf)
		.setSpecularColor(0x010101_rgbf)
		.setShininess(2.f);
	mp_axisShader = std::make_unique<Magnum::Shaders::FlatGL3D>(
		Magnum::Shaders::FlatGL3D::Flag::VertexColor);
	mp_worldShader = std::make_unique<Magnum::Shaders::FlatGL3D>();
	(*mp_axisShader).setColor(0xffffff_rgbf);

	m_axisMesh = Magnum::MeshTools::compile(Magnum::Primitives::axis3D());
}

void SimulationScene::initializeRigidWorld() {
	ff::Dynamics::RigidBodyWorld* rigidWorld = m_dynamics.rigidBodyWorld();
	switch (rigidWorld->getType()) {
	case ff::Dynamics::RigidWorldType::PERIODIC: {
		mp_rigidWorldMesh =
			std::make_unique<Magnum::GL::Mesh>(Magnum::NoCreate);
		*mp_rigidWorldMesh =
			Magnum::MeshTools::compile(Magnum::Primitives::cubeWireframe());
		break;
	}
	default:
		mp_rigidWorldMesh = nullptr;
	}
}

void SimulationScene::drawScene(Magnum::Camera::ArcBallCamera& camera) {
	using namespace Magnum::Math::Literals;
	camera.draw(m_drawables);
	if (m_showContacts) {
		for (size_t i = 0; i < m_dynamics.nContacts(); ++i) {
			ff::Matrix3 rot = m_dynamics.contactInfo()[i].localFrame();
			MagnumMatrix4 t =
				MagnumMatrix4::from(
					MagnumMatrix3(rot),
					MagnumVector3(m_dynamics.contactInfo()[i].pos)) *
				MagnumMatrix4::scaling({m_contactAxisScale, m_contactAxisScale,
			                            m_contactAxisScale});
			mp_axisShader->setTransformationProjectionMatrix(
				camera.getProjection() * camera.getMatrix() *
				Magnum::Matrix4(t));
			mp_axisShader->draw(m_axisMesh);
		}
	}
	if (mp_rigidWorldMesh) {
		MagnumMatrix4 t(
			m_dynamics.rigidBodyWorld()->worldDisplayTransformation().matrix());
		(*mp_worldShader)
			.setTransformationProjectionMatrix(camera.getProjection() *
		                                       camera.getMatrix() *
		                                       Magnum::Matrix4(t))
			.setColor(0xff0000_rgbf)
			.draw(*mp_rigidWorldMesh);

		if (m_dynamics.rigidBodyWorld()->getType() ==
		    ff::Dynamics::RigidWorldType::PERIODIC) {
			auto periodicWorld = dynamic_cast<ff::Dynamics::PeriodicWorld*>(
				m_dynamics.rigidBodyWorld());
			const std::vector<std::vector<int>> tileCount = {{0}, {-1, 0, 1}};
			for (auto& i : tileCount[m_tileX]) {
				for (auto& j : tileCount[m_tileY]) {
					for (auto& k : tileCount[m_tileZ]) {
						if (i != 0 || j != 0 || k != 0) {
							ff::Vector3 translateEig =
								periodicWorld->wrapPos(
									periodicWorld->getCenter(),
									ff::Vector3i(i, j, k)) -
								periodicWorld->getCenter();
							MagnumVector3 translate(translateEig);
							MagnumMatrix4 t =
								MagnumMatrix4::translation(translate);
							std::vector<Magnum::Matrix4> transOrig(
								m_rigidDrawables.size());
							for (int idx = 0; idx < m_rigidDrawables.size();
							     ++idx) {
								transOrig[idx] = m_rigidDrawables[idx]
								                     ->transformationMatrix();
								m_rigidDrawables[idx]->setTransformation(
									Magnum::Matrix4(t) * transOrig[idx]);
							}
							camera.draw(m_drawables);
							for (int idx = 0; idx < m_rigidDrawables.size();
							     ++idx) {
								m_rigidDrawables[idx]->setTransformation(
									transOrig[idx]);
							}
						}
					}
				}
			}
		}
	}
}

void SimulationScene::clearAll() {
	m_experiments.clear();
	m_dynamics.clear();
	m_scene.features().clear();
	for (size_t i = m_drawables.size() - 1; !m_drawables.isEmpty(); --i) {
		m_drawables.remove(m_drawables[i]);
	}
	m_meshes.clear();
	m_rigidDrawables.clear();

	m_experimentStart = true;
	m_currExperiment = m_experiments.begin();
}
void SimulationScene::advanceOneFrame() {
	if (m_simulate || m_stepSimulation) {
		if (m_currExperiment != m_experiments.end()) {
			if ((*m_currExperiment)->isRunning(m_dynamics) == false) {
				m_currExperiment++;
				std::cout << "Experiment finished" << std::endl;
				m_experimentStart = true;
			}
		}

		if (m_currExperiment != m_experiments.end()) {
			if (m_experimentStart) {
				std::cout << "Starting experiment: "
						  << (*m_currExperiment)->getName() << std::endl;
				m_experimentStart = false;
			}
			(*m_currExperiment)->preprocess(m_dynamics);
		}

		m_dynamics.fillForces(m_dynamics.timestep());
		m_stress = Experiments::homogenizedStress(m_dynamics);

		if (m_currExperiment != m_experiments.end()) {
			(*m_currExperiment)->postprocess(m_dynamics);
		}
		m_dynamics.updateAllObjects(m_dynamics.timestep());
		if (m_stepSimulation) {
			m_stepSimulation = false;
		}
	}
	updateAllDrawables();
}

}  // namespace UI
}  // namespace Homogenization
