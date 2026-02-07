#pragma once

#include <Eigen/Core>

// Camera classes for controlling the physical camera parameters (but not the current camera
// position/rotation). Computes the projection matrix and inverse projection matrix

namespace sdtf::viewer::scene {
;

class Camera {
 public:
	// Call this function whenever the aspect ratio of the window changes
	virtual void setAspectRatio(double aspect_ratio) = 0;
	// Zoom is a value in (0.0, 1.0] that says how much of the
	// total viewing rectangle is visible (in either
	// dimension). E.g. zoom=0.5 implies 200% zoom.
	virtual void setZoom(double zoom) = 0;

	virtual double aspectRatio() const = 0;
	virtual double zoom() const = 0;

	virtual void getProjectionMatrix(Eigen::Matrix4d* mat) const = 0;
	virtual void getInverseProjectionMatrix(Eigen::Matrix4d* mat) const = 0;
};

class PerspectiveCamera : public Camera {
 public:
	PerspectiveCamera(double near, double far, double angle, double aspect_ratio);

	virtual void setAspectRatio(double aspect_ratio) override {
		aspect_ratio_ = aspect_ratio;
		computeProjectionMatrix();
	}
	virtual void setZoom(double zoom) override {
		zoom_ = zoom;
		computeProjectionMatrix();
	}

	virtual double aspectRatio() const override { return aspect_ratio_; }
	virtual double zoom() const override { return zoom_; }

	// Sets all properties of the camera; negative values will be interpreted as "no change".
	void setProperties(double near, double far, double angle, double aspect_ratio);

	virtual void getProjectionMatrix(Eigen::Matrix4d* mat) const override { *mat = proj_mat_; }
	virtual void getInverseProjectionMatrix(Eigen::Matrix4d* mat) const override {
		*mat = inv_proj_mat_;
	}

 private:
	void computeProjectionMatrix();

	double near_, far_;    // near and far planes, far may be infinity
	double angle_;         // horizontal opening angle
	double aspect_ratio_;  // horizontal-by-vertical (e.g. 4./3.)
	double zoom_ = 1.0;

	Eigen::Matrix4d proj_mat_, inv_proj_mat_;
};

}  // namespace sdtf::viewer::scene