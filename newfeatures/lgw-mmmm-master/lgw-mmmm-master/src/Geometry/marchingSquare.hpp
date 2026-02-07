#ifndef MARCHING_SQUARE_HPP
#define MARCHING_SQUARE_HPP

#include <iostream>
#include <sstream>
#include <utility>
#include <vector>

#include "Common/CustomTypes.hpp"
#include "Grids/Grid.h"

using namespace Type;

// Geom
struct Face2D {
    int m_val;
    constexpr Face2D(int val) : m_val(val) {}
    explicit constexpr operator bool() const { return (m_val) != 0; }
    constexpr operator int() const { return m_val; }
    static const Face2D None, TOP, BOT, LEFT, RIGHT;
};
#define DEF_FACE2D_VALUE constexpr const Face2D Face2D
DEF_FACE2D_VALUE::None{0};
DEF_FACE2D_VALUE::BOT{1 << 0};
DEF_FACE2D_VALUE::TOP{1 << 1};
DEF_FACE2D_VALUE::LEFT{1 << 2};
DEF_FACE2D_VALUE::RIGHT{1 << 3};
#undef DEF_FACE2D_VALUE
inline Face2D operator|(Face2D a, Face2D b) {
    return static_cast<Face2D>(static_cast<int>(a) | static_cast<int>(b));
}
inline Face2D operator&(Face2D a, Face2D b) {
    return static_cast<Face2D>(static_cast<int>(a) & static_cast<int>(b));
}
inline Face2D operator==(Face2D a, Face2D b) {
    return static_cast<Face2D>(static_cast<int>(a) == static_cast<int>(b));
}
inline Face2D operator!=(Face2D a, Face2D b) {
    return static_cast<Face2D>(static_cast<int>(a) != static_cast<int>(b));
}
inline Face2D& operator|=(Face2D& a, Face2D b) {
    a.m_val = a.m_val | b.m_val;
    return a;
}

/**
 * @brief
 * @param i
 * @param j
 * @param dx
 * @param dy
 * @param bar
 * @return
 */
Vec2 evalPosFace2D(
    unsigned int i, unsigned int j, NumT dx, NumT dy,
    const std::pair<Face2D, NumT>& bar
);
/**
 * @brief
 * @param pos
 * @param i
 * @param j
 * @param dx
 * @param dy
 * @return
 */
Face2D findSide(
    const Vec2& pos, unsigned int i, unsigned int j, NumT dx, NumT dy
);

/**
 * @brief
 * @param side
 * @return
 */
Face2D getOppositeSide(const Face2D& side);

/**
 * @brief
 * @return
 */
Vec2i goToOppositeSide(const Face2D& side);

/**
 * @brief Marching squares
 * @param blVal
 * @param brVal
 * @param tlVal
 * @param trVal
 * @param valThr
 * @param res
 */
void marchingSquare(
    NumT blVal, NumT brVal, NumT tlVal, NumT trVal, NumT valThr,
    std::vector<std::pair<Face2D, NumT>>& res
);

#endif  // MARCHING_SQUARE_HPP
