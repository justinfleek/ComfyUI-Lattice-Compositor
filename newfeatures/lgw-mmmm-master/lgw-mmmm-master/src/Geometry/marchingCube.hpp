#ifndef MARCHING_CUBE_HPP
#define MARCHING_CUBE_HPP

#include <utility>
#include <vector>

#include "Common/CustomTypes.hpp"

using namespace Type;

// Geom
//// Face data

// Bad - duplicate
struct Face3D {
    int m_val;
    constexpr Face3D(int val) : m_val(val) {}
    explicit constexpr operator bool() const { return (m_val) != 0; }
    constexpr operator int() const { return m_val; }
    static const Face3D None, XPLUS, XMINUS, YPLUS, YMINUS, ZPLUS, ZMINUS;
};
#define DEF_FACE3D_VALUE constexpr const Face3D Face3D
DEF_FACE3D_VALUE::None{0};
DEF_FACE3D_VALUE::XPLUS{1 << 0};
DEF_FACE3D_VALUE::XMINUS{1 << 1};
DEF_FACE3D_VALUE::YPLUS{1 << 2};
DEF_FACE3D_VALUE::YMINUS{1 << 3};
DEF_FACE3D_VALUE::ZPLUS{1 << 4};
DEF_FACE3D_VALUE::ZMINUS{1 << 5};
#undef DEF_FACE3D_VALUE
constexpr inline Face3D operator|(Face3D a, Face3D b) {
    return static_cast<Face3D>(static_cast<int>(a) | static_cast<int>(b));
}
constexpr inline Face3D operator&(Face3D a, Face3D b) {
    return static_cast<Face3D>(static_cast<int>(a) & static_cast<int>(b));
}
constexpr inline Face3D operator~(Face3D a) {
    return static_cast<Face3D>(~static_cast<int>(a));
}
constexpr inline Face3D operator==(Face3D a, Face3D b) {
    return static_cast<Face3D>(static_cast<int>(a) == static_cast<int>(b));
}
constexpr inline Face3D operator!=(Face3D a, Face3D b) {
    return static_cast<Face3D>(static_cast<int>(a) != static_cast<int>(b));
}
inline Face3D& operator|=(Face3D& a, Face3D b) {
    a.m_val = a.m_val | b.m_val;
    return a;
}

/**
 * @brief
 * @param pos
 * @param i
 * @param j
 * @param dx
 * @param dy
 * @return
 */
Face3D findSide(
    const Vec3& pos, unsigned int i, unsigned int j, unsigned int k, NumT dx,
    NumT dy, NumT dz
);

/**
 * @brief
 * @return
 */
Vec3i crossFaceDown(const Vec3i cellId, const Face3D& side);

/// Edge data

// An edge is the intersection of two faces
typedef Face3D Edge3D;
constexpr const Edge3D EdgeX00 = Face3D::YMINUS | Face3D::ZMINUS;
constexpr const Edge3D EdgeX10 = Face3D::YPLUS | Face3D::ZMINUS;
constexpr const Edge3D EdgeX01 = Face3D::YMINUS | Face3D::ZPLUS;
constexpr const Edge3D EdgeX11 = Face3D::YPLUS | Face3D::ZPLUS;

constexpr const Edge3D Edge0Y0 = Face3D::XMINUS | Face3D::ZMINUS;
constexpr const Edge3D Edge1Y0 = Face3D::XPLUS | Face3D::ZMINUS;
constexpr const Edge3D Edge0Y1 = Face3D::XMINUS | Face3D::ZPLUS;
constexpr const Edge3D Edge1Y1 = Face3D::XPLUS | Face3D::ZPLUS;

constexpr const Edge3D Edge00Z = Face3D::XMINUS | Face3D::YMINUS;
constexpr const Edge3D Edge10Z = Face3D::XPLUS | Face3D::YMINUS;
constexpr const Edge3D Edge01Z = Face3D::XMINUS | Face3D::YPLUS;
constexpr const Edge3D Edge11Z = Face3D::XPLUS | Face3D::YPLUS;

/**
 * @brief
 * @param
 * @return
 */
std::array<Vec3i, 2> getEdgeVertices(Edge3D edge);

/**
 * @brief
 * @return
 */
Edge3D crossFaceDown(const Edge3D edge);

/**
 * @brief
 * @param i
 * @param j
 * @param k
 * @param dx
 * @param dy
 * @param dz
 * @param bar
 * @return
 */
Vec3 evalPosEdge3D(
    unsigned int i, unsigned int j, unsigned int k, NumT dx, NumT dy, NumT dz,
    const std::pair<Edge3D, NumT>& bar
);

/**
 * @brief Marching cubes
 * @param val000
 * @param val100
 * @param val010
 * @param val110
 * @param val001
 * @param val101
 * @param val011
 * @param val111
 * @param valThr
 * @param res
 */
void marchingCube(
    NumT val000, NumT val100, NumT val010, NumT val110, NumT val001,
    NumT val101, NumT val011, NumT val111, NumT valThr,
    std::vector<std::pair<Edge3D, NumT>>& res
);

#endif  // MARCHING_CUBE_HPP
