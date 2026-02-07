#pragma once

#include "LineMeshInstance.h"
#include "Node.h"
#include "OverlayMeshInstance.h"
#include "TriangleMeshInstance.h"
#include "cameras.h"

// A scene contains a scene graph (which is a tree of Node instances), and different instances (such
// as TriangleMeshInstance) as well as cameras attached to these nodes. The Renderer will render the
// scene viewed from the active camera and the active camera node.

namespace sdtf::viewer::scene {
;

class Scene {
 public:
	Scene();

	Node* addNode(std::unique_ptr<Node> node) { return addEntity(&nodes_, std::move(node)); }
	void removeNode(Node* node) { removeEntity(&nodes_, node); }

	Camera* addCamera(std::unique_ptr<Camera> camera) {
		return addEntity(&cameras_, std::move(camera));
	}

	// The application needs to call this function before rendering in order to compute the world
	// transformations in the scene graph.
	void updateWorldTransform();


	// Add different instance types to the scene
	TriangleMeshInstance* addInstance(std::unique_ptr<TriangleMeshInstance> instance) {
		return addEntity(&triangle_mesh_instances_, std::move(instance));
	}
	void removeInstance(TriangleMeshInstance* instance) {
		removeEntity(&triangle_mesh_instances_, std::move(instance));
	}
	const auto& triangleMeshInstances() const { return triangle_mesh_instances_; }

	LineMeshInstance* addInstance(std::unique_ptr<LineMeshInstance> instance) {
		return addEntity(&line_mesh_instances_, std::move(instance));
	}
	void removeInstance(LineMeshInstance* instance) {
		removeEntity(&line_mesh_instances_, std::move(instance));
	}
	const auto& lineMeshInstances() const { return line_mesh_instances_; }

	OverlayMeshInstance* addInstance(std::unique_ptr<OverlayMeshInstance> instance) {
		return addEntity(&overlay_mesh_instances_, std::move(instance));
	}
	void removeInstance(OverlayMeshInstance* instance) {
		removeEntity(&overlay_mesh_instances_, std::move(instance));
	}
	const auto& overlayMeshInstances() const { return overlay_mesh_instances_; }

	// Set active camera and camera node
	void setActiveCamera(Camera* cam) { active_camera_ = cam; }
	auto activeCamera() { return active_camera_; }
	const auto activeCamera() const { return active_camera_; }

	void setActiveCameraNode(Node* node) { active_camera_node_ = node; }
	auto activeCameraNode() { return active_camera_node_; }
	const auto activeCameraNode() const { return active_camera_node_; }

	// Checks if there is an active camera and camera node
	bool isCameraComplete() const {
		return active_camera_node_ != nullptr && active_camera_ != nullptr;
	}

	// Compute view matrix and projection matrix used by the renderer
	void computeViewProjectionMatrix(Eigen::Matrix4d* ret) const;
	void computeInverseViewProjectionMatrix(Eigen::Matrix4d* ret) const;
	void getViewMatrix(Eigen::Matrix4d* ret) const;
	void getInverseViewMatrix(Eigen::Matrix4d* ret) const;

 private:
	std::set<std::unique_ptr<Node>> nodes_;
	Node* active_camera_node_ = nullptr;
	Camera* active_camera_ = nullptr;

	std::set<std::unique_ptr<Camera>> cameras_;
	std::set<std::unique_ptr<TriangleMeshInstance>> triangle_mesh_instances_;
	std::set<std::unique_ptr<LineMeshInstance>> line_mesh_instances_;
	std::set<std::unique_ptr<OverlayMeshInstance>> overlay_mesh_instances_;

	template <typename T>
	T* addEntity(std::set<std::unique_ptr<T>>* collection, std::unique_ptr<T> entity) {
		T* ret = entity.get();
		collection->insert(std::move(entity));
		return ret;
	}

	// Generic function for removing from set; slow, only use for single calls
	template <typename T>
	void removeEntity(std::set<std::unique_ptr<T>>* collection, T* entity) {
		for (auto iter = collection->begin(); iter != collection->end();) {
			if (iter->get() == entity)
				iter = collection->erase(iter);
			else
				iter++;
		}
	}
};
}  // namespace sdtf::viewer::scene