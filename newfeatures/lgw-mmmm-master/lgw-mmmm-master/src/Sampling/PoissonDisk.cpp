#include "PoissonDisk.h"

#include <limits>
#include <queue>
#include <vector>

#include "Grids/Grid.h"

namespace Sampling {

void poissonDiskSampling3D(
    std::vector<Vec3>& results, Vec3 start, Vec3 end, NumT radius, bool tilable,
    size_t maxIters
) {
    NumT gridDx = radius / static_cast<NumT>(std::sqrt(3));
    NumT radiusSq = radius * radius;
    Grid::DenseGrid3D<int> gridCache(start, end, gridDx);
    gridCache.setConst(-1);
    std::vector<int> q;

    Vec3 diff = end - start;
    Vec3 randInit(
        std::rand() / NumT(RAND_MAX), std::rand() / NumT(RAND_MAX),
        std::rand() / NumT(RAND_MAX)
    );
    randInit = randInit.cwiseProduct(diff);
    randInit += start;

    results.clear();
    results.push_back(randInit);
    gridCache.refAt(randInit) = 0;

    q.push_back(0);
    while (!q.empty()) {
        int idx = std::rand() % q.size();
        Vec3& currPoint = results[q[idx]];

        size_t iters = 0;
        for (iters = 0; iters < maxIters; ++iters) {
            NumT randNumT = std::rand() / NumT(RAND_MAX);
            NumT randSigma =
                2 * static_cast<NumT>(M_PI) * std::rand() / NumT(RAND_MAX);
            NumT randCosPhi = std::rand() / NumT(RAND_MAX) * 2 - 1;
            NumT randSinPhi = std::sqrt(1 - randCosPhi * randCosPhi);
            NumT r = radius * std::pow(7 * randNumT + 1, 1.f / 3);
            Vec3 nextPoint = currPoint +
                             Vec3{
                                 randSinPhi * std::cos(randSigma),
                                 randSinPhi * std::sin(randSigma), randCosPhi} *
                                 r;
            if (nextPoint[0] < start[0]) {
                if (tilable) {
                    nextPoint[0] += diff[0];
                } else {
                    nextPoint[0] = start[0];
                }
            }
            if (nextPoint[0] > end[0]) {
                if (tilable) {
                    nextPoint[0] -= diff[0];
                } else {
                    nextPoint[0] = end[0];
                }
            }
            if (nextPoint[1] < start[1]) {
                if (tilable) {
                    nextPoint[1] += diff[1];
                } else {
                    nextPoint[1] = start[1];
                }
            }
            if (nextPoint[1] > end[1]) {
                if (tilable) {
                    nextPoint[1] -= diff[1];
                } else {
                    nextPoint[1] = end[1];
                }
            }
            if (nextPoint[2] < start[2]) {
                if (tilable) {
                    nextPoint[2] += diff[2];
                } else {
                    nextPoint[2] = start[2];
                }
            }
            if (nextPoint[2] > end[2]) {
                if (tilable) {
                    nextPoint[2] -= diff[2];
                } else {
                    nextPoint[2] = end[2];
                }
            }
            Vec3i nextIdx = gridCache.pos2ijk(nextPoint);
            bool failed = false;
            for (int j = -2; j < 3; ++j) {
                for (int k = -2; k < 3; ++k) {
                    for (int l = -2; l < 3; ++l) {
                        Vec3i otherIdx = nextIdx + Vec3i{j, k, l};
                        Vec3b flags = gridCache.boundFlags(otherIdx);
                        if (!tilable &&
                            (flags[0] != 0 || flags[1] != 0 || flags[2] != 0)) {
                            continue;
                        }
                        int otherId = gridCache(otherIdx);
                        if (otherId != -1) {
                            Vec3 otherPoint = results[otherId];
                            otherPoint += Vec3(flags[0], flags[1], flags[2])
                                              .cwiseProduct(diff);
                            if ((nextPoint - otherPoint).squaredNorm() <
                                radiusSq) {
                                failed = true;
                                break;
                            }
                        }
                    }
                }
                if (failed)
                    break;
            }
            if (failed)
                continue;
            gridCache(nextIdx) = results.size();
            q.push_back(results.size());
            results.push_back(nextPoint);
            break;
        }
        if (iters == maxIters) {
            std::swap(q[idx], q.back());
            q.pop_back();
        }
    }
}

void poissonDiskSampling3DSurf(
    VectorVec3& results, const std::shared_ptr<Base3DSurface> surfInitPtr,
    NumT radius, Vec3 gridSize, NumT padding, bool tilable, size_t maxIters
) {
    const VectorVec3& surfPos = surfInitPtr->getSurfacePos();
    Vec3 posMin(
        std::numeric_limits<NumT>::infinity(),
        std::numeric_limits<NumT>::infinity(),
        std::numeric_limits<NumT>::infinity()
    );
    Vec3 posMax(
        -std::numeric_limits<NumT>::infinity(),
        -std::numeric_limits<NumT>::infinity(),
        -std::numeric_limits<NumT>::infinity()
    );
    posMin = surfInitPtr->getImplGridNC().getStartPos();
    posMax = surfInitPtr->getImplGridNC().getEndPos();
    std::vector<Vec3> tmpRes;
    results.clear();

    posMin.array() += padding;
    posMax.array() -= padding;
    // for (unsigned int j = 0; j < 3; ++j) {
    //     posMin[j] = std::max(posMin[j], padding);
    //     posMax[j] = std::min(posMax[j], gridSize[j] - padding);
    // }  // j
    // Sample
    poissonDiskSampling3D(tmpRes, posMin, posMax, radius, tilable, maxIters);
#pragma omp parallel
    {
        // Prune
        VectorVec3 subResults;
#pragma omp for schedule(dynamic, 1)
        for (unsigned int i = 0; i < tmpRes.size(); ++i) {
            const Vec3& pos = tmpRes[i];
            if (surfInitPtr->isInside(pos)) {
                subResults.push_back(pos);
            }
        }  // i

#pragma omp critical
        { results.insert(results.end(), subResults.begin(), subResults.end()); }

    }  // parallel

    // #pragma omp parallel
    //     {
    //         //         // Get bounding box
    //         //         Vec3 posMinLoc(
    //         //             std::numeric_limits<NumT>::infinity(),
    //         //             std::numeric_limits<NumT>::infinity(),
    //         //             std::numeric_limits<NumT>::infinity()
    //         //         );
    //         //         Vec3 posMaxLoc(
    //         //             -std::numeric_limits<NumT>::infinity(),
    //         //             -std::numeric_limits<NumT>::infinity(),
    //         //             -std::numeric_limits<NumT>::infinity()
    //         //         );
    //         // #pragma omp parallel for
    //         //         for (unsigned int i = 0; i < surfPos.size(); ++i) {
    //         //             const Vec3& pos = surfPos[i];
    //         //             for (unsigned int j = 0; j < 3; ++j) {
    //         //                 posMinLoc[j] = std::min(posMinLoc[j], pos[j]);
    //         //                 posMaxLoc[j] = std::max(posMaxLoc[j], pos[j]);
    //         //             }  // j
    //         //         }  // i
    //         //
    //         // #pragma omp critical
    //         //         {
    //         //             for (unsigned int j = 0; j < 3; ++j) {
    //         //                 posMin[j] = std::min(posMin[j], posMinLoc[j]);
    //         //                 posMax[j] = std::max(posMax[j], posMaxLoc[j]);
    //         //             }  // j
    //         //         }  // critical
    //         //
    //         // #pragma omp barrier
    //
    // #pragma omp master
    //         {
    //             posMin.array() += padding;
    //             posMax.array() -= padding;
    //             // for (unsigned int j = 0; j < 3; ++j) {
    //             //     posMin[j] = std::max(posMin[j], padding);
    //             //     posMax[j] = std::min(posMax[j], gridSize[j] -
    //             padding);
    //             // }  // j
    //             // Sample
    //             poissonDiskSampling3D(
    //                 tmpRes, posMin, posMax, radius, tilable, maxIters
    //             );
    //         }  // master
    //
    // #pragma omp barrier
    //
    //         // Prune
    //         VectorVec3 subResults;
    // #pragma omp for
    //         for (unsigned int i = 0; i < tmpRes.size(); ++i) {
    //             const Vec3& pos = tmpRes[i];
    //             if (surfInitPtr->isInside(pos)) {
    //                 subResults.push_back(pos);
    //             }
    //         }  // i
    //
    // #pragma omp critical
    //         { results.insert(results.end(), subResults.begin(),
    //         subResults.end()); }
    //
    //     }  // parallel
}

}  // namespace Sampling
