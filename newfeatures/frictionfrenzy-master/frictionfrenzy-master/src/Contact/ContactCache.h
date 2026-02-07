#pragma once

#include <Eigen/Dense>
#include <unordered_map>

#include "Common/Hashing.h"
#include "Common/MatrixTypes.h"
namespace FrictionFrenzy {
namespace Contact {
struct ContactForceInfo {
	Vector3 pos;
	Vector2 staticFriction;
	Vector2 dynamicFriction;
	std::vector<Scalar> normalCache;
	Scalar finalShockCache;
	Scalar lcpCache;
};

typedef std::unordered_map<std::pair<unsigned int, unsigned int>,
                           std::vector<ContactForceInfo>>
	ContactCache;

}  // namespace Contact
}  // namespace FrictionFrenzy
