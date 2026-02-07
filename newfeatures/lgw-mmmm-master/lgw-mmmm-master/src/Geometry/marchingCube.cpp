#include "marchingCube.hpp"
#include "Common/Utils.hpp"

using namespace Type;

Face3D findSide(
    const Vec3& pos, unsigned int i, unsigned int j, unsigned int k, NumT dx,
    NumT dy, NumT dz
) {
#warning TODO
    return Face3D::None;
}

Vec3i crossFaceDown(const Vec3i cellId, const Face3D& side) {
    Vec3i neighId = cellId;
    if (side & Face3D::XMINUS) {
        neighId[0] -= 1;
    }
    if (side & Face3D::YMINUS) {
        neighId[1] -= 1;
    }
    if (side & Face3D::ZMINUS) {
        neighId[2] -= 1;
    }
    return neighId;
}

Edge3D crossFaceDown(const Edge3D edge) {
    Edge3D neighEdge = edge;
    if (edge & Face3D::XMINUS) {
        neighEdge = (neighEdge & ~Face3D::XMINUS) | Face3D::XPLUS;
    }
    if (edge & Face3D::YMINUS) {
        neighEdge = (neighEdge & ~Face3D::YMINUS) | Face3D::YPLUS;
    }
    if (edge & Face3D::ZMINUS) {
        neighEdge = (neighEdge & ~Face3D::ZMINUS) | Face3D::ZPLUS;
    }
    return neighEdge;
}

std::array<Vec3i, 2> getEdgeVertices(Edge3D edge) {
    std::array<Vec3i, 2> res;
    switch (edge) {
    case (EdgeX00):
        res = {Vec3i(0, 0, 0), Vec3i(1, 0, 0)};
        break;
    case (Edge10Z):
        res = {Vec3i(1, 0, 0), Vec3i(1, 0, 1)};
        break;
    case (EdgeX01):
        res = {Vec3i(0, 0, 1), Vec3i(1, 0, 1)};
        break;
    case (Edge00Z):
        res = {Vec3i(0, 0, 0), Vec3i(0, 0, 1)};
        break;
    // Back face
    case (EdgeX10):
        res = {Vec3i(0, 1, 0), Vec3i(1, 1, 0)};
        break;
    case (Edge11Z):
        res = {Vec3i(1, 1, 0), Vec3i(1, 1, 1)};
        break;
    case (EdgeX11):
        res = {Vec3i(0, 1, 1), Vec3i(1, 1, 1)};
        break;
    case (Edge01Z):
        res = {Vec3i(0, 1, 0), Vec3i(0, 1, 1)};
        break;
    // Other
    case (Edge0Y0):
        res = {Vec3i(0, 0, 0), Vec3i(0, 1, 0)};
        break;
    case (Edge1Y0):
        res = {Vec3i(1, 0, 0), Vec3i(1, 1, 0)};
        break;
    case (Edge1Y1):
        res = {Vec3i(1, 0, 1), Vec3i(1, 1, 1)};
        break;
    case (Edge0Y1):
        res = {Vec3i(0, 0, 1), Vec3i(0, 1, 1)};
        break;
    default:
        break;
    };
    return res;
}

Vec3 evalPosEdge3D(
    unsigned int i, unsigned int j, unsigned int k, NumT dx, NumT dy, NumT dz,
    const std::pair<Edge3D, NumT>& bar
) {
    const std::array<Vec3i, 2> vOffset = getEdgeVertices(bar.first);
    const NumT alpha = bar.second;

    const Vec3i base(i, j, k);
    const Vec3 d(dx, dy, dz);

    const Vec3 posFirst = ((base + vOffset[0]).cast<NumT>()).cwiseProduct(d);
    const Vec3 posSecond = ((base + vOffset[1]).cast<NumT>()).cwiseProduct(d);

    return (1 - alpha) * posFirst + alpha * posSecond;
}

/// Helpers of the marching cube
/// Adapted from https://github.com/nihaljn/marching-cubes/
#include "marchingCube.data"

// Convention for the values: see in marchingCube
// Mark corners inside
int computeCubeIndex(const std::array<NumT, 8>& vals, NumT valThr) {
    int cubeIndex = 0;
#pragma unroll
    for (int i = 0; i < 8; i++) {
        if (vals[i] < valThr) {
            cubeIndex |= (1 << i);
        }
    }
    return cubeIndex;
}

// Dark magic
// Compute intersections with each edge that is around an inside corner
// Return barycentric coodrinate on the edge
std::array<NumT, 12> getIntersectionCoordinates(
    int cubeIndex, const std::array<NumT, 8>& vals, NumT valThr
) {
    std::array<NumT, 12> barIntersec;

    int intersectionsKey = edgeTable[cubeIndex];

    int idx = 0;
    while (intersectionsKey) {
        if (intersectionsKey & 1) {
            const int v1 = edgeToVertices[idx].first;
            const int v2 = edgeToVertices[idx].second;
            const NumT bar = barycenter(vals[v1], vals[v2], valThr);
            barIntersec[idx] = bar;
        }  // ?
        idx++;
        intersectionsKey >>= 1;
    }  // ?

    return barIntersec;
}

void getTriangles(
    int cubeIndex, const std::array<NumT, 12>& barIntersec,
    std::vector<std::pair<Edge3D, NumT>>& res
) {
    // Clean
    res.clear();

    // Load triangles
    for (int i = 0; triangleTable[cubeIndex][i] != -1; i += 3) {
        // Read by triplet
        // for (int j = 0; j < 3; j++) {
        for (int j = 2; j >= 0; --j) {  // face order
            const int edgeId = triangleTable[cubeIndex][i + j];
            const Edge3D edge = edgeCode[edgeId];
            const NumT barCoord = barIntersec[edgeId];
            res.emplace_back(std::make_pair(edge, barCoord));
        }

    }  // i
}

void triangulateCell(
    const std::array<NumT, 8>& vals, NumT valThr,
    std::vector<std::pair<Edge3D, NumT>>& res
) {
    // Compute intersection type
    const int cubeIndex = computeCubeIndex(vals, valThr);
    // Cell intersection
    const std::array<NumT, 12> barIntersec =
        getIntersectionCoordinates(cubeIndex, vals, valThr);
    // Generate triangles
    getTriangles(cubeIndex, barIntersec, res);
}

void marchingCube(
    NumT val000, NumT val100, NumT val010, NumT val110, NumT val001,
    NumT val101, NumT val011, NumT val111, NumT valThr,
    std::vector<std::pair<Edge3D, NumT>>& res
) {
    // Conventions
    const std::array<NumT, 8> vals = {val000, val100, val101, val001,
                                      val010, val110, val111, val011};

    // Call internal computation
    triangulateCell(vals, valThr, res);
}
