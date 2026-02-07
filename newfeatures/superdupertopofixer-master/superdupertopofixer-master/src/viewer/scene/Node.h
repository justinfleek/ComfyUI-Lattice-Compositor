#pragma once

#include <Eigen/Core>
#include <memory>
#include <set>

// Represents a node in the scene graph. Contains a translation and a rotation that comprise the
// "model matrix" of the subtree.

namespace sdtf::viewer::scene {
;

class Node {
 public:
	Node(const Eigen::Vector3d& position = Eigen::Vector3d::Zero(),
	     const Eigen::Matrix3d& frame = Eigen::Matrix3d::Identity());

	// Sets the local transformation of this node relative to its parent (if it has one)
	void setPosition(const Eigen::Vector3d& position) { position_ = position; }
	void setFrame(const Eigen::Matrix3d& frame) { frame_ = frame; }

	// Returns the local transformation
	const auto& position() const { return position_; }
	const auto& frame() const { return frame_; }

	// Returns the glocal transformation accumulated by multiplying the model matrices on the path to the root.
	const auto& worldPosition() const { return world_position_; }
	const auto& worldFrame() const { return world_frame_; }

	// Add and remove children
	Node* addNode(std::unique_ptr<Node> node);
	void removeNode(Node* node);

	// Returns the model matrix of the local transformation
	void getModelMatrix(Eigen::Matrix4d* ret) const;

	// Pass the model matrix down to this node's children recursively. The parameter-less function is called
	// on the root node by the application. The version with parameters is called by each node on its children.
	void updateWorldTransform();
	void updateWorldTransform(const Eigen::Vector3d& parent_pos, const Eigen::Matrix3d& parent_frame);

 private:
	Eigen::Vector3d position_;
	Eigen::Matrix3d frame_;

	Eigen::Vector3d world_position_;
	Eigen::Matrix3d world_frame_;

	std::set<std::unique_ptr<Node>> children_;
};

}  // namespace sdtf::viewer::scene