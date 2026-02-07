#include "Base3dSurface.hpp"
#include <limits>
#include "Common/Utils.hpp"
#include "Geometry/marchingCube.hpp"
// #include "levelset.hpp"

Base3DSurface::Base3DSurface(
    Params::Grid gridParams, Params::Surface surfParams
)
    : m_gridParams(gridParams),
      m_surfParams(surfParams),
      m_distUp(3 * m_gridParams.gridEnd.maxCoeff()) {
    m_gImpSurf = Grid::DenseGrid3D<NumT>(m_gridParams);
    m_gSurfPos = Grid::DenseGrid3D<VectorVec3>(m_gridParams);
    m_gSurfPosEdge = Grid::DenseGrid3D<std::vector<Edge3D>>(m_gridParams);
    m_gSurfIndex = Grid::DenseGrid3D<VectorI>(m_gridParams);
    m_gTriangles = Grid::DenseGrid3D<VectorI>(m_gridParams);
    // m_gDistFieldGrad = Grid::DenseGrid3D<Vec3>(m_gridParams);
}

const Params::Grid& Base3DSurface::getGridParameters() const {
    return m_gridParams;
}
const Params::Surface& Base3DSurface::getSurfParameters() const {
    return m_surfParams;
}

void Base3DSurface::compute(bool sdfFillAll) {
    // Volume field must be computed before somewhere else
    // computeImplicitSurface();
    computeImplicitSurfaceNoSoup();
    computeSurfaceNormals();
    computeDistanceField();
}

NumT Base3DSurface::getVolume() const {
    const int resX = m_gSurfPos.getCellRes()[0];
    const int resY = m_gSurfPos.getCellRes()[1];
    const int resZ = m_gSurfPos.getCellRes()[2];
    const NumT dx =
        (m_gridParams.gridEnd[0] - m_gridParams.gridStart[0]) / resX;
    const NumT dy =
        (m_gridParams.gridEnd[1] - m_gridParams.gridStart[1]) / resY;
    const NumT dz =
        (m_gridParams.gridEnd[2] - m_gridParams.gridStart[2]) / resZ;
    const NumT cellVol = dx * dy * dz;

    const Grid::DenseGrid3D<NumT>& m_gDistField = m_gImpSurf;

    NumT vol = 0;
#pragma omp parallel for collapse(3) reduction(+ : vol)
    for (int i = 0; i < resX; ++i) {
        for (int j = 0; j < resY; ++j) {
            for (int k = 0; k < resZ; ++k) {
                bool allInside = true;
                bool allOutside = false;
                bool cornerInside[2][2][2];
                for (int di = 0; di < 2; ++di) {
                    for (int dj = 0; dj < 2; ++dj) {
                        for (int dk = 0; dk < 2; ++dk) {
                            const bool thisCornerInside =
                                m_gDistField(i + di, j + dj, k + dk) <= 0;
                            cornerInside[di][dj][dk] = thisCornerInside;
                            allInside &= thisCornerInside;
                            allOutside &= (!thisCornerInside);
                        }  // dk
                    }      // di
                }          // di
                if (allInside) {
                    vol += cellVol;
                } else if (allOutside) {
                    continue;
                } else {
                    // No double cell!
                    /*
                    VectorVec3 pts = m_gSurfTriangles(i, j, k);
                    for (int di = 0; di < 2; ++di) {
                        for (int dj = 0; dj < 2; ++dj) {
                            for (int dk = 0; dk < 2; ++dk) {
                                if (cornerInside[di][dj][dk]) {
                                    pts.emplace_back(Vec3((i + di) * dx,
                                                          (j + dj) * dy,
                                                          (k + dk) * dk));
                                }
                            } // dk
                        } // di
                    } // di
                    vol += volumePolyhedra(pts);
                    */
                    // Voxel approx
                    for (int di = 0; di < 2; ++di) {
                        for (int dj = 0; dj < 2; ++dj) {
                            for (int dk = 0; dk < 2; ++dk) {
                                if (cornerInside[di][dj][dk]) {
                                    vol += cellVol / 8;
                                }
                            }  // dk
                        }      // dj
                    }          // di
                }

            }  // k
        }      // j
    }          // i

    return vol;
}

const Grid::DenseGrid3D<NumT>& Base3DSurface::getImplGrid() const {
    return m_gImpSurf;
}
Grid::DenseGrid3D<NumT>& Base3DSurface::getImplGridNC() {
    return m_gImpSurf;
}

const VectorVec3& Base3DSurface::getSurfacePos() const {
    return m_surfPos;
}

const Grid::DenseGrid3D<VectorI>& Base3DSurface::getSurfaceIdsOnGrid() const {
    return m_gSurfIndex;
}

const VectorUi& Base3DSurface::getTriangles() const {
    return m_triangles;
}
const Grid::DenseGrid3D<VectorI>& Base3DSurface::getTrianglesGrid() const {
    return m_gTriangles;
}

void Base3DSurface::computeSurfaceNormals() {
    const size_t nbPoints = m_surfPos.size();

    if (m_triangles.empty()) {
        m_surfNormals.resize(nbPoints);
#pragma omp parallel for
        for (size_t tId = 0; tId < nbPoints / 3; ++tId) {
            const Vec3& p0 = m_surfPos[3 * tId];
            const Vec3& p1 = m_surfPos[3 * tId + 1];
            const Vec3& p2 = m_surfPos[3 * tId + 2];
            const Vec3 normal = (p1 - p0.cross(p2 - p0)).normalized();
            m_surfNormals[3 * tId] = normal;
            m_surfNormals[3 * tId + 1] = normal;
            m_surfNormals[3 * tId + 2] = normal;
        }  // tId

    } else {
        m_surfNormals.assign(nbPoints, Zero3);
#pragma omp parallel
        {
#pragma omp for
            for (size_t tId = 0; tId < m_triangles.size() / 3; ++tId) {
                const Vec3i vIds(
                    m_triangles[3 * tId], m_triangles[3 * tId + 1],
                    m_triangles[3 * tId + 2]
                );
                const Vec3& p0 = m_surfPos[vIds[0]];
                const Vec3& p1 = m_surfPos[vIds[1]];
                const Vec3& p2 = m_surfPos[vIds[2]];
                const Vec3 normal = (p1 - p0.cross(p2 - p0)).normalized()
                    //
                    ;
                for (unsigned int i = 0; i < 3; ++i) {
                    for (unsigned int j = 0; j < 3; ++j) {
#pragma omp atomic
                        m_surfNormals[vIds[i]][j] += normal[j];
                    }  // j
                }      // i
            }          // tId

#pragma omp for
            for (size_t vId = 0; vId < nbPoints; ++vId) {
                m_surfNormals[vId] = m_surfNormals[vId].normalized();
            }
        }  // omp parallel
    }
}

const VectorVec3& Base3DSurface::getSurfaceNormals() const {
    return m_surfNormals;
}

const Grid::DenseGrid3D<VectorVec3>& Base3DSurface::getSurfacePosOnGrid(
) const {
    return m_gSurfPos;
}

const Grid::DenseGrid3D<std::vector<Edge3D>>&
Base3DSurface::getSurfaceSidesOnGrid() const {
    return m_gSurfPosEdge;
}

bool Base3DSurface::isInside(const Vec3& pos) const {
    const NumT dist = getSDF(pos);
    return (dist <= 0);
}

NumT Base3DSurface::getSDF(const Vec3& pos) const {
    const Grid::DenseGrid3D<NumT>& m_gDistField = m_gImpSurf;
    return m_gDistField.interpolate(pos);
}

// const Vec3 Base3DSurface::getSDFGrad(const Vec3& pos) const {
//     return m_gDistFieldGrad.interpolate(pos);
// }

NumT Base3DSurface::getSDFCubic(const Vec3& pos) const {
    const Grid::DenseGrid3D<NumT>& m_gDistField = m_gImpSurf;
    return m_gDistField.interpolateCubic(pos);
}

// const Vec3 Base3DSurface::getSDFGradCubic(const Vec3& pos) const {
//     // return m_gDistFieldGrad.interpolate(pos);
//     return m_gDistFieldGrad.interpolateCubic(pos);
// }

// Vec3 Base3DSurface::projectOnIsoSurf(const Vec3& xPos, NumT eps) const {
//     // const NumT eps = 1.e-7;
//     NumT sdf = getSDFCubic(xPos);
//     Vec3 x   = xPos;
//     //
//     Vec3       searchDir;
//     NumT       rho;
//     NumT       sdfNext;
//     Vec3       xNext;
//     const NumT rhoMin = 1.e-5;
//     while (std::fabs(sdf) > eps) {
//         searchDir = -sdf * getSDFGradCubic(x);
//         rho       = 1;
//         while (rho > rhoMin) {
//             xNext = x + rho * searchDir;
//             try {
//                 sdfNext = getSDFCubic(xNext);
//             } catch (const std::out_of_range& e) {
//                 rho /= 2;
//                 continue;
//             }
//             if (std::fabs(sdfNext) < std::fabs(sdf)) {
//                 break;
//             } else {
//                 rho /= 2;
//             }
//         }
//         if (rho < rhoMin) {
//             break;
//         }
//         x   = xNext;
//         sdf = sdfNext;
//     }
//
//     return x;
// }

const Grid::DenseGrid3D<NumT>& Base3DSurface::getSDFGrid() const {
    return m_gImpSurf;  // m_gDistField;
}

// const Grid::DenseGrid3D<Vec3>& Base3DSurface::getSDFGradGrid() const {
//     return m_gDistFieldGrad;
// }

void Base3DSurface::computeImplicitSurface() {
    // Shortcuts
    const size_t gResX = m_gImpSurf.getCellRes()[0];
    const size_t gResY = m_gImpSurf.getCellRes()[1];
    const size_t gResZ = m_gImpSurf.getCellRes()[2];
    const NumT gDx = static_cast<NumT>(m_gridParams.gridEnd[0] / gResX);
    const NumT gDy = static_cast<NumT>(m_gridParams.gridEnd[1] / gResY);
    const NumT gDz = static_cast<NumT>(m_gridParams.gridEnd[2] / gResZ);
    const NumT valThr = 0.;  // static_cast<NumT>(m_surfParams.impThr );//*
                             // m_mpmSimPtr->getPhysParameters().pVol);

    m_surfPos.clear();

    /*
    m_surfPos.emplace_back(Vec3(0, 0, 0.4));
    m_surfPos.emplace_back(Vec3(1, 0, 0.4));
    m_surfPos.emplace_back(Vec3(0.5, 1, 0.4));
    m_surfPos.emplace_back(Vec3(0, 0, 0.4));
    m_surfPos.emplace_back(Vec3(0.5, 0, 0.0));
    m_surfPos.emplace_back(Vec3(1, 0, 0.4));
    return;
    */
    // Parallel marching cubes

    /// Triangle soup version
#pragma omp parallel
    {
        VectorVec3 subPosSurf;

#pragma omp for collapse(3)
        for (size_t i = 0; i <= gResX; ++i) {
            for (size_t j = 0; j <= gResY; ++j) {
                for (size_t k = 0; k <= gResZ; ++k) {
                    m_gSurfPos(i, j, k).clear();
                    const NumT val000 = m_gImpSurf(i, j, k);
                    const NumT val100 = m_gImpSurf(i + 1, j, k);
                    const NumT val010 = m_gImpSurf(i, j + 1, k);
                    const NumT val110 = m_gImpSurf(i + 1, j + 1, k);
                    const NumT val001 = m_gImpSurf(i, j, k + 1);
                    const NumT val101 = m_gImpSurf(i + 1, j, k + 1);
                    const NumT val011 = m_gImpSurf(i, j + 1, k + 1);
                    const NumT val111 = m_gImpSurf(i + 1, j + 1, k + 1);
                    // Triplets define a triangle
                    std::vector<std::pair<Face3D, NumT>> edgesBar;
                    marchingCube(
                        val000, val100, val010, val110, val001, val101, val011,
                        val111, valThr, edgesBar
                    );
                    for (const auto& bar : edgesBar) {
                        const Vec3 pos =
                            evalPosEdge3D(i, j, k, gDx, gDy, gDz, bar);
                        subPosSurf.push_back(pos);
                        m_gSurfPos(i, j, k).push_back(pos);
                    }  // p
                }      // k
            }          // j
        }              // i

#pragma omp critical
        {
            m_surfPos.insert(
                m_surfPos.end(), subPosSurf.begin(), subPosSurf.end()
            );
        }  // omp critical

    }  // omp parallel
}

void Base3DSurface::computeImplicitSurfaceNoSoup() {
    // Shortcuts
    const size_t gResX = m_gImpSurf.getCellRes()[0];
    const size_t gResY = m_gImpSurf.getCellRes()[1];
    const size_t gResZ = m_gImpSurf.getCellRes()[2];
    const NumT gDx = static_cast<NumT>(
        (m_gridParams.gridEnd[0] - m_gridParams.gridStart[0]) / gResX
    );
    const NumT gDy = static_cast<NumT>(
        (m_gridParams.gridEnd[1] - m_gridParams.gridStart[1]) / gResY
    );
    const NumT gDz = static_cast<NumT>(
        (m_gridParams.gridEnd[2] - m_gridParams.gridStart[2]) / gResZ
    );
    const NumT valThr = 0.;  // static_cast<NumT>(m_surfParams.impThr );//*
                             // m_mpmSimPtr->getPhysParameters().pVol);

    const int iMax = gResX;
    const int jMax = gResY;
    const int kMax = gResZ;

    // Clean
    m_surfPos.clear();
    m_triangles.clear();

    // Indexed version
    // #pragma omp parallel
    //     {
    // #pragma omp for collapse(3)
    //         for (int i = 0; i <= iMax; ++i) {
    //             for (int j = 0; j <= jMax; ++j) {
    //                 for (int k = 0; k <= kMax; ++k) {
    GRID_LOOP3_IJK(i, j, k, Vec3i(iMax, jMax, kMax)) {
        m_gSurfPos(i, j, k).clear();
        m_gSurfPosEdge(i, j, k).clear();
        const NumT val000 = m_gImpSurf(i, j, k);
        const NumT val100 = m_gImpSurf(i + 1, j, k);
        const NumT val010 = m_gImpSurf(i, j + 1, k);
        const NumT val110 = m_gImpSurf(i + 1, j + 1, k);
        const NumT val001 = m_gImpSurf(i, j, k + 1);
        const NumT val101 = m_gImpSurf(i + 1, j, k + 1);
        const NumT val011 = m_gImpSurf(i, j + 1, k + 1);
        const NumT val111 = m_gImpSurf(i + 1, j + 1, k + 1);
        // Triplets define a triangle
        std::vector<std::pair<Face3D, NumT>> edgesBar;
        marchingCube(
            val000, val100, val010, val110, val001, val101, val011, val111,
            valThr, edgesBar
        );
        for (const auto& bar : edgesBar) {
            const Vec3 pos = evalPosEdge3D(i, j, k, gDx, gDy, gDz, bar);
            m_gSurfPos(i, j, k).push_back(pos);
            m_gSurfPosEdge(i, j, k).push_back(bar.first);
        }  // p
    }
    //             }  // k
    //         }  // j
    //     }  // i
    // }  // omp parallel

    const NumT epsMerge = 1.e-3 * gDx;
    const int idError = std::numeric_limits<int>::min();
    // Lambda to look for a point;
    auto lookPoint = [&epsMerge](
                         const Vec3& pointPos, const Face3D pointFace,
                         const VectorVec3& knownPoints,
                         const std::vector<Face3D> knownFaces,
                         const VectorI& knownIds
                     ) {
        for (int i = 0; i < knownPoints.size(); ++i) {
            if (((pointPos - knownPoints[i]).norm() < epsMerge) &&
                (pointFace == knownFaces[i])) {
                return knownIds[i];
            }
        }
        return idError;
    };

    // Parse by diagonal
    const int nbDiag3 = iMax + jMax + kMax;
    for (int iPjPk = 0; iPjPk <= nbDiag3; ++iPjPk) {
        // Create new indices for vertices that did not belong
        // to the previous diagonal
        const int iStart = std::max(iPjPk - jMax - kMax, 0);
        const int iEnd = std::min(iPjPk, iMax);
#pragma omp parallel for
        for (int i = iStart; i <= iEnd; ++i) {
            const int jPk = iPjPk - i;
            const int jStart = std::max(jPk - kMax, 0);
            const int jEnd = std::min(jPk, jMax);
#pragma omp parallel for
            for (int j = jStart; j <= jEnd; ++j) {
                const int k = jPk - j;
                // Data
                const Vec3i cellId(i, j, k);
                VectorVec3& cellPos = m_gSurfPos(cellId);
                std::vector<Face3D>& cellEdge = m_gSurfPosEdge(cellId);
                // Init
                VectorVec3 surfPosMerged;
                std::vector<Face3D> surfPosEdgeMerged;
                m_gSurfIndex(cellId).clear();
                m_gTriangles(cellId).clear();
                // Local index for new vertices
                for (int tId = 0; tId < cellPos.size() / 3; ++tId) {
                    Vec3i triangleIds(0, 0, 0);
                    for (int vNbLoc = 0; vNbLoc < 3; ++vNbLoc) {
                        const int vNbGlob = 3 * tId + vNbLoc;
                        const Vec3& vPos = cellPos[vNbGlob];
                        const Edge3D vEdge = cellEdge[vNbGlob];
                        // Look inside the cell
                        int vId = lookPoint(
                            vPos, vEdge, surfPosMerged, surfPosEdgeMerged,
                            m_gSurfIndex(cellId)
                        );
                        // Second search: in previous cell
                        constexpr Face3D prevDiag =
                            (Face3D::XMINUS | Face3D::YMINUS | Face3D::ZMINUS);
                        if ((vId == idError) && (iPjPk > 0) &&
                            (vEdge & prevDiag)) {
                            const Vec3i neighCellId =
                                crossFaceDown(cellId, vEdge);
                            if (m_gSurfPos.isIdValid(neighCellId)) {
                                const Edge3D vOppEdge = crossFaceDown(vEdge);
                                vId = lookPoint(
                                    vPos, vOppEdge, m_gSurfPos(neighCellId),
                                    m_gSurfPosEdge(neighCellId),
                                    m_gSurfIndex(neighCellId)
                                );
                            }
                        }  // Second search
                        if (vId == idError) {
                            // New vertex: new local id
                            const int newVLocId = -surfPosMerged.size() - 1;
                            surfPosMerged.emplace_back(vPos);
                            surfPosEdgeMerged.emplace_back(vEdge);
                            m_gSurfIndex(cellId).push_back(newVLocId);
                            triangleIds[vNbLoc] = newVLocId;
                        } else {
                            // Known vertex
                            triangleIds[vNbLoc] = vId;
                        }
                    }  // vNb
                    for (int cmp = 0; cmp < 3; ++cmp) {
                        m_gTriangles(cellId).emplace_back(triangleIds[cmp]);
                    }
                }  // tId
                cellPos = surfPosMerged;
                cellEdge = surfPosEdgeMerged;
            }  // j - parallel
        }      // i - parallel

        // Vectorise indices
        for (int i = iStart; i <= iEnd; ++i) {
            const int jPk = iPjPk - i;
            const int jStart = std::max(jPk - kMax, 0);
            const int jEnd = std::min(jPk, jMax);
            for (int j = jStart; j <= jEnd; ++j) {
                const int k = jPk - j;
                // Data
                const Vec3i cellId(i, j, k);
                const int offset = m_surfPos.size();
                /// Flip indices
                for (int& vId : m_gSurfIndex(cellId)) {
                    if (vId < 0) {
                        vId = -(vId + 1) + offset;
                    }  // vId
                }      // vId
                for (int tId = 0; tId < m_gTriangles(cellId).size(); ++tId) {
                    int& vId = m_gTriangles(cellId)[tId];
                    if (vId < 0) {
                        vId = -(vId + 1) + offset;
                    }  // vId
                }      // tId
                /// Merge
                m_surfPos.insert(
                    m_surfPos.end(), m_gSurfPos(cellId).begin(),
                    m_gSurfPos(cellId).end()
                );
                // NB: implicit cast
                m_triangles.insert(
                    m_triangles.end(), m_gTriangles(cellId).begin(),
                    m_gTriangles(cellId).end()
                );
            }  // j - serial
        }      // i - serial
    }          // iPjPk
}

void Base3DSurface::computeDistanceField() {
    const Grid::DenseGrid3D<NumT>& m_gDistField = m_gImpSurf;

    // Shortcuts
    const size_t gResX = m_gDistField.getCellRes()[0];
    const size_t gResY = m_gDistField.getCellRes()[1];
    const size_t gResZ = m_gDistField.getCellRes()[2];
    const NumT dx =
        (m_gridParams.gridEnd[0] - m_gridParams.gridStart[0]) / gResX;
    const NumT dy =
        (m_gridParams.gridEnd[1] - m_gridParams.gridStart[1]) / gResY;
    const NumT dz =
        (m_gridParams.gridEnd[2] - m_gridParams.gridStart[2]) / gResZ;
    const Vec3 delta(dx, dy, dz);

    const NumT infinity = std::numeric_limits<NumT>::infinity();

    // Params
    const int searchRange = 2;

#pragma omp parallel
    {
        // SDF Gradient
#pragma omp for collapse(3)
        for (int i = 1; i < gResX; ++i) {
            for (int j = 1; j < gResY; ++j) {
                for (int k = 1; k < gResZ; ++k) {
                    const Vec3i base(i, j, k);
                    const NumT val = m_gDistField(base);
                    if (val <= -infinity) {
                        // m_gDistFieldGrad(base) = Zero3;
                        continue;
                    }

                    Vec3 grad;
                    bool valid = true;

                    for (int cmp = 0; cmp < 3; ++cmp) {
                        Vec3i offset(0, 0, 0);
                        offset[cmp] = 1;
                        const NumT valBwd = m_gDistField(base - offset);
                        const bool validBwd = (valBwd > -infinity);
                        const NumT valFwd = m_gDistField(base + offset);
                        const bool validFwd = (valFwd > -infinity);

                        if (validBwd && validFwd) {
                            grad[cmp] = (valFwd - valBwd) / (2 * delta[cmp]);
                        } else if (validBwd) {
                            grad[cmp] = (val - valBwd) / delta[cmp];
                        } else if (validFwd) {
                            grad[cmp] = (valFwd - val) / delta[cmp];
                        } else {
                            valid = false;
                            break;
                        }
                    }  // cmp

                    // if (valid) {
                    //     m_gDistFieldGrad(base) = grad;
                    // } else {
                    //     m_gDistFieldGrad(base) = Zero3;
                    // }

                }  // k
            }      // j
        }          // i

    }  // omp parallel
}
