#include "scene/cameras.h"

namespace sdtf::viewer::scene {
;

PerspectiveCamera::PerspectiveCamera(double near, double far, double angle, double aspect_ratio)
    : near_(near),
      far_(far),
      angle_(angle),
      aspect_ratio_(aspect_ratio),
      proj_mat_(Eigen::Matrix4d::Zero()),
      inv_proj_mat_(Eigen::Matrix4d::Zero()) {
	computeProjectionMatrix();
}

void PerspectiveCamera::setProperties(double near, double far, double angle, double aspect_ratio) {
	if (near >= 0.)
		near_ = near;
	if (far >= 0.)
		far_ = far;
	if (angle >= 0.)
		angle_ = angle;
	if (aspect_ratio >= 0.)
		aspect_ratio_ = aspect_ratio;

	computeProjectionMatrix();
}

void PerspectiveCamera::computeProjectionMatrix() {
	double nr = 1. / (zoom_ * tan(angle_ * 0.5));
	double nt = nr * aspect_ratio_;
	proj_mat_(0, 0) = nr;
	proj_mat_(1, 1) = nt;
	proj_mat_(3, 2) = -1.;
	inv_proj_mat_(0, 0) = 1. / nr;
	inv_proj_mat_(1, 1) = 1. / nt;
	inv_proj_mat_(2, 3) = -1.;
	if (std::isinf(far_)) {
		proj_mat_(2, 2) = -1.;
		proj_mat_(2, 3) = -2. * near_;
		double z = 1. / (2. * near_);
		inv_proj_mat_(3, 2) = -z;
		inv_proj_mat_(3, 3) = z;
	} else {
		double x = (far_ + near_) / (near_ - far_);
		double y = 2. * far_ * near_ / (near_ - far_);
		proj_mat_(2, 2) = x;
		proj_mat_(2, 3) = y;
		inv_proj_mat_(3, 2) = 1. / y;
		inv_proj_mat_(3, 3) = x / y;
	}
}

}  // namespace sdtf::viewer::scene