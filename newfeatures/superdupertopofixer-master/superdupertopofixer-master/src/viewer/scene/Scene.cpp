#include "Scene.h"

namespace sdtf::viewer::scene {
;

Scene::Scene() {
}

void Scene::computeViewProjectionMatrix(Eigen::Matrix4d* ret) const {
	Eigen::Matrix4d proj_matrix;
	active_camera_->getProjectionMatrix(&proj_matrix);

	Eigen::Matrix4d view_matrix;
	getViewMatrix(&view_matrix);

	*ret = proj_matrix * view_matrix;
}

void Scene::computeInverseViewProjectionMatrix(Eigen::Matrix4d* ret) const {
	Eigen::Matrix4d ip_matrix;
	active_camera_->getInverseProjectionMatrix(&ip_matrix);

	Eigen::Matrix4d iv_matrix;
	getInverseViewMatrix(&iv_matrix);

	*ret = iv_matrix * ip_matrix;
}

void Scene::getViewMatrix(Eigen::Matrix4d* ret) const {
	ret->template block<3, 3>(0, 0) = active_camera_node_->worldFrame().transpose();
	ret->template block<3, 1>(0, 3) = -ret->template block<3, 3>(0, 0) * active_camera_node_->worldPosition();
	ret->template bottomRows<1>() << 0., 0., 0., 1.;
}

void Scene::getInverseViewMatrix(Eigen::Matrix4d* ret) const {
	ret->template block<3, 3>(0, 0) = active_camera_node_->worldFrame();
	ret->template block<3, 1>(0, 3) = active_camera_node_->worldPosition();
	ret->template bottomRows<1>() << 0., 0., 0., 1.;
}

void Scene::updateWorldTransform() {
	for (auto& node : nodes_)
		node->updateWorldTransform();
}

}  // namespace sdtf::viewer::scene