#ifndef __RNG_H__
#define __RNG_H__

// #include <Common/InputParse.h>
#include <Eigen/Dense>

#include <limits>
#include <memory>
#include <random>

namespace Homogenization {

template <typename T>
class RNG1DBase {
   public:
	RNG1DBase() {}
	virtual ~RNG1DBase() {}
	RNG1DBase(int seed) : m_randomSeed(seed) {}
	RNG1DBase(T avg, int seed) : m_randomSeed(seed), m_avg(avg) {}
	T getAvg() { return m_avg; }
	virtual T sample() = 0;
	virtual T max() = 0;

   protected:
	int m_randomSeed;
	T m_avg;
};

class UniformIntSampler : public RNG1DBase<int> {
   public:
	UniformIntSampler(int seed) { m_gen.seed(seed); }
	int sample() override { return m_gen(); }
	int max() override { return std::numeric_limits<int>::max(); }

   protected:
	std::mt19937 m_gen;
};

template <typename T>
class ConstSampler : public RNG1DBase<T> {
   public:
	ConstSampler(T num, int seed = 0) : RNG1DBase<T>(num, 0){};
	T sample() override { return RNG1DBase<T>::m_avg; }
	T max() override { return RNG1DBase<T>::m_avg; }
};

template <typename T>
class UniformSampler : public RNG1DBase<T> {
   public:
	UniformSampler(T min, T max, int seed) : RNG1DBase<T>(seed) {
		RNG1DBase<T>::m_avg = 0.5 * (min + max);
		m_gen = std::mt19937(RNG1DBase<T>::m_randomSeed);
		m_rng = std::uniform_real_distribution<T>(min, max);
		m_gen.seed(RNG1DBase<T>::m_randomSeed);
	}
	T sample() override { return m_rng(m_gen); }
	T max() override { return m_rng.max(); }

   protected:
	std::mt19937 m_gen;
	std::uniform_real_distribution<T> m_rng;
};

template <typename T>
class GaussianSampler : public RNG1DBase<T> {
   public:
	GaussianSampler(T avg, T std, T clamp, int seed)
		: RNG1DBase<T>(avg, seed), m_std(std), m_clamp(clamp) {
		m_gen = std::mt19937(RNG1DBase<T>::m_randomSeed);
		m_rng = std::normal_distribution<T>(avg, std);
		m_clamp = std::min(m_clamp, 3 * std);
		}
	T sample() override {
		T s;
		do {
			s = m_rng(m_gen);
		} while (m_clamp > 0 && (s < RNG1DBase<T>::m_avg - m_clamp ||
		                         s > RNG1DBase<T>::m_avg + m_clamp));
		return s;
	}
	T max() override { return RNG1DBase<T>::m_avg + m_clamp; }

   protected:
	std::mt19937 m_gen;
	std::normal_distribution<T> m_rng;
	T m_std;
	T m_clamp;
};

template <typename T>
class DiscreteRandom : public RNG1DBase<T> {
   public:
	DiscreteRandom(const std::vector<T>& random,
	               const std::vector<double>& fractions,
	               int seed)
		: RNG1DBase<T>(0, seed) {
		m_numToRand = random;
		m_gen.seed(seed);

		m_rng =
			std::discrete_distribution<>(fractions.begin(), fractions.end());
	}

	T sample() override { return m_numToRand[m_rng(m_gen)]; }
	T max() override { return m_rng.max(); }

   protected:
	std::mt19937 m_gen;
	std::discrete_distribution<> m_rng;
	std::vector<T> m_numToRand;
};

template <typename T>
class Vector3SamplerBase {
   public:
	virtual ~Vector3SamplerBase() {}
	virtual Eigen::Vector<T, 3> sample() = 0;
	virtual Eigen::Vector<T, 3> max() = 0;
};

template <typename T>
class IdenticalVector3Sampler : public Vector3SamplerBase<T> {
   public:
	IdenticalVector3Sampler(std::shared_ptr<RNG1DBase<T>> sampler) {
		m_sampler = sampler;
	}
	Eigen::Vector<T, 3> sample() override {
		T num = m_sampler->sample();
		return Eigen::Vector<T, 3>(num, num, num);
	}
	Eigen::Vector<T, 3> max() override {
		Eigen::Vector<T, 3> ret;
		ret.setConstant(m_sampler->max());
		return ret;
	};

   private:
	std::shared_ptr<RNG1DBase<T>> m_sampler;
};
template <typename T>
class IIDVector3Sampler : public Vector3SamplerBase<T> {
   public:
	IIDVector3Sampler(std::shared_ptr<RNG1DBase<T>> sampler1,
	                  std::shared_ptr<RNG1DBase<T>> sampler2,
	                  std::shared_ptr<RNG1DBase<T>> sampler3) {
		m_sampler = {sampler1, sampler2, sampler3};
	}
	Eigen::Vector<T, 3> sample() override {
		return Eigen::Vector<T, 3>(m_sampler[0]->sample(),
		                           m_sampler[1]->sample(),
		                           m_sampler[2]->sample());
	}
	Eigen::Vector<T, 3> max() override {
		Eigen::Vector<T, 3> ret(m_sampler[0]->max(), m_sampler[1]->max(),
		                        m_sampler[2]->max());
		return ret;
	};

   private:
	std::array<std::shared_ptr<RNG1DBase<T>>, 3> m_sampler;
};
}  // namespace Homogenization

#endif
