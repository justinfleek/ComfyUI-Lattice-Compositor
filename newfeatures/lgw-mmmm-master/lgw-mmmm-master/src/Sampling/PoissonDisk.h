#pragma once

#include "Common/CustomTypes.hpp"
#include "Geometry/Base3dSurface.hpp"

#include <vector>

namespace Sampling {

using namespace Type;

/**
 * @brief
 * @param results
 * @param start
 * @param end
 * @param radius
 * @param tilable
 * @param maxIters
 */
void poissonDiskSampling3D(
    std::vector<Vec3>& results, Vec3 start, Vec3 end, NumT radius,
    bool tilable = true, size_t maxIters = 30
);

/**
 * @brief
 * @param results
 * @param surfInitPtr
 * @param radius
 * @param tilable
 * @param maxIters
 */
void poissonDiskSampling3DSurf(
    VectorVec3& results, const std::shared_ptr<Base3DSurface> surfInitPtr,
    NumT radius, Vec3 gridSize, NumT padding, bool tilable = true,
    size_t maxIters = 30
);

}  // namespace Sampling
