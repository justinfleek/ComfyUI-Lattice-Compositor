#ifndef __INPUT_PARSE_H__
#define __INPUT_PARSE_H__

#include <yaml-cpp/yaml.h>
#include <stdexcept>

#include <Eigen/Dense>

namespace Homogenization {
namespace IO {

template <typename T>
inline T parseScalar(const YAML::Node& node,
                     const char* param,
                     const char* structName) {
	static_assert(std::is_scalar_v<T>, "Input must be a scalar!");
	if (node[param] && node[param].IsScalar()) {
		return node[param].as<T>();
	} else {
		throw std::runtime_error(std::string(structName) +
		                         ": No value read for parameter '" + param +
		                         "'!");
	}
}

template <typename T>
inline T parseScalar(const YAML::Node& node,
                     const char* param,
                     const T& defValue,
                     const char* structName) {
	static_assert(std::is_scalar_v<T>, "Input must be a scalar!");
	if (node[param] && node[param].IsScalar()) {
		return node[param].as<T>();
	} else {
		return defValue;
	}
}

template <typename T, unsigned int n>
Eigen::Vector<T, n> parseVectorEigen(const YAML::Node& node,
                                     const char* param,
                                     const char* structName) {
	static_assert(std::is_scalar_v<T>, "Input must be a scalar!");
	if (node[param].IsDefined() && node[param].IsSequence()) {
		Eigen::Vector<T, n> ret;
		for (unsigned int i = 0; i < n; ++i) {
			if (node[param][i].IsDefined() && node[param][i].IsScalar()) {
				ret[i] = node[param][i].as<T>();
			} else {
				throw std::runtime_error(std::string(structName) +
				                         ": invalid input for vector '" +
				                         param + "'!");
			}
		}
		return ret;
	} else {
		throw std::runtime_error(std::string(structName) + ": '" + param +
		                         "' not defined or not a sequence!");
	}
}
template <typename T, unsigned int n>
Eigen::Vector<T, n> parseVectorEigen(
	const YAML::Node& node,
	const char* param,
	Eigen::Ref<const Eigen::Vector<T, n>> defValue,
	const char* structName) {
	static_assert(std::is_scalar_v<T>, "Input must be a scalar!");
	if (node[param].IsDefined() && node[param].IsSequence()) {
		Eigen::Vector<T, n> ret;
		for (unsigned int i = 0; i < n; ++i) {
			if (node[param][i].IsDefined() && node[param][i].IsScalar()) {
				ret[i] = node[param][i].as<T>();
			} else {
				throw std::runtime_error(std::string(structName) +
				                         ": invalid input for vector '" +
				                         param + "'!");
			}
		}
		return ret;
	} else {
		return defValue;
	}
}
template <typename T, typename... Args>
auto parseVector3(Args&&... args)
	-> decltype(parseVectorEigen<T, 3>(std::forward<Args>(args)...)) {
	return parseVectorEigen<T, 3>(std::forward<Args>(args)...);
}
}  // namespace IO
}  // namespace Homogenization

#endif
