#pragma once

namespace sdtf::viewer::logic {
;

// Collecting of tool settings such as mouse sensitivities

struct CameraToolSettings {
	double orbit_yaw_speed = 1.e-2;
	double orbit_pitch_speed = 1.e-2;
	double zoom_scroll_interval = 0.1;
	double dolly_speed_ = 1.e-2;

	CameraToolSettings() = default;
	CameraToolSettings(double orbit_yaw_speed, double orbit_pitch_speed)
	    : orbit_yaw_speed(orbit_yaw_speed), orbit_pitch_speed(orbit_pitch_speed) {}
};

struct VisualizationToolSettings {
	double clipping_plane_speed = 2.e-3;
};

}