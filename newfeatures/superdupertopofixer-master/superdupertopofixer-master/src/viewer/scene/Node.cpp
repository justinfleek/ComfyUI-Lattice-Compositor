#include "scene/Node.h"

namespace sdtf::viewer::scene {
;

Node::Node(const Eigen::Vector3d& position, const Eigen::Matrix3d& frame)
    : position_(position), frame_(frame) {}

void Node::getModelMatrix(Eigen::Matrix4d* ret) const {
	ret->template block<3, 3>(0, 0) = frame_;
	ret->template block<3, 1>(0, 3) = position_;
	ret->template block<1, 4>(3, 0) << 0., 0., 0., 1.;
}

Node* Node::addNode(std::unique_ptr<Node> node) {
	auto ret = node.get();
	children_.insert(std::move(node));
	return ret;
}

void Node::removeNode(Node* node) {
	for (auto iter = children_.begin(); iter != children_.end();) {
		if (iter->get() == node)
			iter = children_.erase(iter);
		else
			iter++;
	}
}

void Node::updateWorldTransform() {
	world_position_ = position_;
	world_frame_ = frame_;
	for (auto& child : children_)
		child->updateWorldTransform(world_position_, world_frame_);
}

void Node::updateWorldTransform(const Eigen::Vector3d& parent_pos,
                                const Eigen::Matrix3d& parent_frame) {
	world_position_ = parent_frame * position_ + parent_pos;
	world_frame_ = parent_frame * frame_;
	for (auto& child : children_)
		child->updateWorldTransform(world_position_, world_frame_);
}

}  // namespace ElRods::DesignerGUI::scene