#pragma once

#include <Eigen/Core>

namespace sdtf::viewer::scene {
class Scene;
}

// The ViewerInterface is implemented by the main application to expose a number of general-purpose
// function to tools.

namespace sdtf::viewer::logic {
;

class ViewerInterface {
 public:
	virtual float contentScale() const { return 1.0f; }
	virtual bool cursorWorldPosition(Eigen::Vector3d* pos) const { return false; }
	virtual bool cursorPixelPosition(Eigen::Vector2d* pos) const { return false; }
	virtual unsigned int cursorIndex() const { return -1; }
	virtual const scene::Scene* scene() const { return nullptr; }
	virtual double canvasWidth() const { return 0.0; }
	virtual double canvasHeight() const { return 0.0; }
	virtual void getDefaultCameraLocation(Eigen::Vector3d* position, Eigen::Matrix3d* frame) const {
		*position << 5., 0., 0.;
		*frame << 0., 0., 1., 1., 0., 0., 0., 1., 0.;
	}
	virtual Eigen::Vector3d sceneCenter() const { return Eigen::Vector3d::Zero(); }
	virtual double sceneDiameter() const { return 2.; }
	virtual void clearSelection(){};
};

}  // namespace sdtf::viewer::logic