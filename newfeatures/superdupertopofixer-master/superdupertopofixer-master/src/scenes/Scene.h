/* Scene.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * This is the header for an abstact scene.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
class Scene {
 public:
	Scene(double max_sim_time) : current_sim_time_(0.0), max_sim_time_(max_sim_time){};
	virtual ~Scene(){};
	virtual void step(double dt) = 0;
	virtual bool isFinished() { return current_sim_time_ >= max_sim_time_; };
	virtual double getCurrentSimTime() { return current_sim_time_; }

 protected:
	virtual void advanceTime(double dt) { current_sim_time_ += dt; }

 private:
	double current_sim_time_;
	double max_sim_time_;
};