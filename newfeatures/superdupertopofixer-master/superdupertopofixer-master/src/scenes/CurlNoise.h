/* CurlNoise.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021-2022
 *
 * Time-consistent curl noise.
 * Adapted from Los Topos.
 */
#pragma once

#include "../datastructures/Mesh3DInterface.h"
#include "Scene.h"

class Noise3 {
 public:
	Noise3(unsigned int seed = 171717);

	void reinitialize(unsigned int seed);
	double operator()(const Vec3d& x) const;

 protected:
	static const unsigned int n = 128;
	std::array<Vec3d, n> basis;
	std::array<int, n> perm;

	unsigned int hash_index(int i, int j, int k) const {
		return perm[(perm[(perm[i % n] + j) % n] + k) % n];
	}
};

class CurlNoiseScene : public Scene {
 public:
	CurlNoiseScene(Mesh3DInterface* mesh, double max_sim_time) : Scene(max_sim_time), mesh_(mesh){};
	virtual void step(double dt) override;

 private:
	Vec3d velocity(const Vec3d& pos);
	Vec3d potential(const Vec3d& pos);
	double noise(const Vec3d& pos);

	// Finite-different approximation.
	double delta_ = 1e-4;

	// Noise params.
	double noise_lengthscale_ = 1.5;
	double noise_gain_ = 1.3;
	Vec3d noise_center_ = Vec3d(0.0, 1.0, 0.0);
	double noise_radius_ = 4.0;
	double noise_height_factor_ = 0.5;

	Mesh3DInterface* mesh_;

	Noise3 noise_;
};
