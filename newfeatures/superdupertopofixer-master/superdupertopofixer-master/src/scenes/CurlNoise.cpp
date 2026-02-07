#include "CurlNoise.h"

#include "../datastructures/Mesh3DVertex.h"

void CurlNoiseScene::step(double dt) {
	for (Mesh3DVertex* v : mesh_->ListVertices()) {
		Vec3d pos = v->getCoords();
		Vec3d k1 = velocity(pos);
		Vec3d k2 = velocity(pos + 0.5 * dt * k1);
		Vec3d k3 = velocity(pos + 0.5 * dt * k2);
		Vec3d k4 = velocity(pos + dt * k3);
		Vec3d vel = (k1 + k2 * 2 + k3 * 2 + k4) / 6;
		v->setCoords(pos + dt * vel);
	}
	advanceTime(dt);
}

Vec3d CurlNoiseScene::velocity(const Vec3d& pos) {
	// Curl of potential.
	Vec3d dx = potential(pos + Vec3d(delta_, 0, 0)) - potential(pos - Vec3d(delta_, 0, 0));
	Vec3d dy = potential(pos + Vec3d(0, delta_, 0)) - potential(pos - Vec3d(0, delta_, 0));
	Vec3d dz = potential(pos + Vec3d(0, 0, delta_)) - potential(pos - Vec3d(0, 0, delta_));
	return Vec3d(dy[2] - dz[1], dz[0] - dx[2], dx[1] - dy[0]) / (2 * delta_);
}

Vec3d CurlNoiseScene::potential(const Vec3d& pos) {
	Vec3d psi_i(0, 0, noise(pos / noise_lengthscale_));
	double dist = mag(pos - noise_center_);
	double scale = std::max((noise_radius_ - dist) / noise_radius_, 0.0);
	return noise_height_factor_ * noise_gain_ * scale * psi_i;
}

double CurlNoiseScene::noise(const Vec3d& pos) {
	// Magic offsets by LosTopos. I have no idea why they do it.
	return noise_({pos[2] - 203.994, pos[0] + 169.47, pos[1] - 205.31});
}

namespace {

template <unsigned int N>
Vec<N, double> sample_sphere(unsigned int& seed) {
	Vec<N, double> v;
	double m2;
	do {
		for (unsigned int i = 0; i < N; ++i) {
			v[i] = LosTopos::randhashf(seed++, -1, 1);
		}
		m2 = mag2(v);
	} while (m2 > 1 || m2 == 0);
	return v / std::sqrt(m2);
}

}  // namespace

Noise3::Noise3(unsigned int seed) {
	for (unsigned int i = 0; i < n; ++i) {
		basis[i] = sample_sphere<3>(seed);
		perm[i] = i;
	}
	reinitialize(seed);
}

void Noise3::reinitialize(unsigned int seed) {
	for (unsigned int i = 1; i < n; ++i) {
		int j = LosTopos::randhash(seed++) % (i + 1);
		std::swap(perm[i], perm[j]);
	}
}

double Noise3::operator()(const Vec3d& pos) const {
	Vec3i floor_pos = floor(pos);
	int i = floor_pos[0];
	int j = floor_pos[1];
	int k = floor_pos[2];
	const Vec3d& n000 = basis[hash_index(i, j, k)];
	const Vec3d& n100 = basis[hash_index(i + 1, j, k)];
	const Vec3d& n010 = basis[hash_index(i, j + 1, k)];
	const Vec3d& n110 = basis[hash_index(i + 1, j + 1, k)];
	const Vec3d& n001 = basis[hash_index(i, j, k + 1)];
	const Vec3d& n101 = basis[hash_index(i + 1, j, k + 1)];
	const Vec3d& n011 = basis[hash_index(i, j + 1, k + 1)];
	const Vec3d& n111 = basis[hash_index(i + 1, j + 1, k + 1)];

	Vec3d f = pos - Vec3d(floor_pos);
	Vec3d s = f * f * f * (Vec3d(10) - f * (Vec3d(15) - f * Vec3d(6)));
	return LosTopos::trilerp(
	    dot(f, n000), dot(f - Vec3d(1, 0, 0), n100), dot(f - Vec3d(0, 1, 0), n010),
	    dot(f - Vec3d(1, 1, 0), n110), dot(f - Vec3d(0, 0, 1), n001), dot(f - Vec3d(1, 0, 1), n101),
	    dot(f - Vec3d(0, 1, 1), n011), dot(f - Vec3d(1, 1, 1), n111), s[0], s[1], s[2]);
}