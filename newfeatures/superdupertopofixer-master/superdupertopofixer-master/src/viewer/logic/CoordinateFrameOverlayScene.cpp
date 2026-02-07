#include "CoordinateFrameOverlayScene.h"

#include <iostream>

#include "geom/Primitives.h"

namespace sdtf::viewer::logic {
;

CoordinateFrameOverlayScene::CoordinateFrameOverlayScene() {
	initColors();

	scene_ = std::make_unique<scene::Scene>();

	camera_node_ = scene_->addNode(std::make_unique<scene::Node>());
	scene_->setActiveCameraNode(camera_node_);

	auto cam = std::make_unique<scene::PerspectiveCamera>(1.e-1, 1.e2, 3.14 / 6., 1.);
	camera_ = cam.get();
	scene_->addCamera(std::move(cam));
	scene_->setActiveCamera(camera_);

	// Build the scene for displaying a smaller coordinate system
	auto cyl_mesh = geom::MeshPrimitives<float>::getCylinderIndexed(
	    Eigen::Vector3f::Zero(), Eigen::Vector3f(0.f, 0.f, 1.f), 0.07f, 36, true, true, true, true);
	cylinder_ = std::make_unique<gl::TriangleMesh>(cyl_mesh.vertices, cyl_mesh.triangles);
	cylinder_->setNormals(cyl_mesh.normals);

	auto cone_mesh = geom::MeshPrimitives<float>::getConeIndexed(
	    Eigen::Vector3f(0.f, 0.f, 1.f), Eigen::Vector3f(0.f, 0.f, 1.3f), 0.12f, 36, true, true, true);
	cone_ = std::make_unique<gl::TriangleMesh>(cone_mesh.vertices, cone_mesh.triangles);
	cone_->setNormals(cone_mesh.normals);
	for (int i = 0; i < 3; i++) {
		Eigen::Vector3d forward = Eigen::Vector3d::Zero();
		forward(i) = 1.0;
		Eigen::Matrix3d basis = geom::buildBasis(forward);

		arrow_nodes_[i] =
		    scene_->addNode(std::make_unique<scene::Node>(Eigen::Vector3d::Zero(), basis));
		cylinder_inst_[i] = scene_->addInstance(
		    std::make_unique<scene::TriangleMeshInstance>(cylinder_.get(), arrow_nodes_[i]));
		cylinder_inst_[i]->setFrontColor(colors_[i]);
		cylinder_inst_[i]->setAngleAttenuation(0.2f);

		cone_inst_[i] = scene_->addInstance(
		    std::make_unique<scene::TriangleMeshInstance>(cone_.get(), arrow_nodes_[i]));
		cone_inst_[i]->setFrontColor(colors_[i]);
		cone_inst_[i]->setAngleAttenuation(0.2f);
	}

	auto box_mesh = geom::MeshPrimitives<float>::getUnitCubeTriangles(true, true);
	box_mesh.vertices *= 0.2f;
	box_mesh.vertices.colwise() -= Eigen::Vector3f(0.1f, 0.1f, 0.1f);
	box_ = std::make_unique<gl::TriangleMesh>(box_mesh.vertices);
	box_->setNormals(box_mesh.normals);

	box_node_ = scene_->addNode(std::make_unique<scene::Node>());
	box_inst_ =
	    scene_->addInstance(std::make_unique<scene::TriangleMeshInstance>(box_.get(), box_node_));
	box_inst_->setFrontColor(Eigen::Vector3f(1.f, 1.f, 1.f));
	box_inst_->setAngleAttenuation(0.2f);
}

void CoordinateFrameOverlayScene::mimicCamera(const scene::Node* other_node) {
	// Copy rotation of the camera frame the main scene, and place the camera at
	// a constant distance from the origin of the coordinate system
	const auto& frame = other_node->frame();
	Eigen::Vector3d pos = frame.col(2) * 6.;
	camera_node_->setPosition(pos);
	camera_node_->setFrame(frame);
}

void CoordinateFrameOverlayScene::initColors() {
	colors_[0] = Eigen::Vector3f(230, 25, 75) / 255.;
	colors_[1] = Eigen::Vector3f(210, 245, 60) / 255.;
	colors_[2] = Eigen::Vector3f(0, 0, 128) / 255.;
}

}  // namespace sdtf::viewer::logic