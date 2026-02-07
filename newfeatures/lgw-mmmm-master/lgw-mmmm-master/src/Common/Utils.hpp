#ifndef _UTILS_HPP
#define _UTILS_HPP

#include <iostream>
#include <sstream>
#include <utility>
#include <vector>

#include "Common/CustomTypes.hpp"

// #define TEST_SETUP // NOT HERE

#define SQRT2_2 (0.7071067811865476)
#define COS_3PI_8 (0.38268343236508984)

using namespace Type;

/**
 * @tparam T
 * @brief Sign function
 * @return
 */
template <typename T>
int sgn(T val);

/**
 * @tParam T
 * @brief Clamp
 * @param val
 * @param valMin
 * @param valMax
 */
template <typename T>
void clamp(T& val, T valMin, T valMax);
/**
 * @tParam T
 * @brief Clamp
 * @param val
 * @param valMin
 * @param valMax
 */
template <typename T>
T clamp(const T& val, T valMin, T valMax);

/**
 * @brief Linear interpolation
 * @tParam T
 * @param val0
 * @param val1
 * @param k
 * @return
 */
template <typename T>
T lerp(const T& val0, const T& val1, NumT k);

/**
 * @brief Bilinear interpolation
 * @tParam T
 * @param val00
 * @param val10
 * @param val01
 * @param val11
 * @param ku
 * @param kv
 * @return
 */
template <typename T>
T bilerp(
    const T& val00,
    const T& val10,
    const T& val01,
    const T& val11,
    NumT ku,
    NumT kv
);

/**
 * @brief Trilinear interpolation
 * @tParam T
 * @param val000
 * @param val100
 * @param val010
 * @param val110
 * @param val001
 * @param val101
 * @param val011
 * @param val111
 * @param ku
 * @param kv
 * @param kw
 * @return
 */
template <typename T>
T trilerp(
    const T& val000,
    const T& val100,
    const T& val010,
    const T& val110,
    const T& val001,
    const T& val101,
    const T& val011,
    const T& val111,
    NumT ku,
    NumT kv,
    NumT kw
);

/**
 * @brief Cubic interpolation - Catmull-Rom
 * @tParam T
 * @param valm
 * @param val0
 * @param val1
 * @param val2
 * @param k
 * @return
 */
template <typename T>
T cerp(const T& valm, const T& val0, const T& val1, const T& val2, NumT k);

/**
 * @brief Bicubic interpolation
 * @tParam T
 * @return
 */
template <typename T>
T bicerp(
    const T& valmm,
    const T& val0m,
    const T& val1m,
    const T& val2m,
    const T& valm0,
    const T& val00,
    const T& val10,
    const T& val20,
    const T& valm1,
    const T& val01,
    const T& val11,
    const T& val21,
    const T& valm2,
    const T& val02,
    const T& val12,
    const T& val22,
    NumT ku,
    NumT kv
);

/**
 * @brief Tricubic interpolation
 * @tParam T
 * @tParam Array3DT
 * @return
 */
template <typename T, template <class> typename Array3D>
T tricerp(
    const Array3D<T>& vals,
    int i,
    int j,
    int k,
    NumT ku,
    NumT kv,
    NumT kw
);

template <typename T, typename Vec, template <class> typename Array3D>
T tricerpGrad(
    const Array3D<T>& vals,
    int i,
    int j,
    int k,
    NumT ku,
    NumT kv,
    NumT kw,
    NumT dx,
    const Array3D<Vec>& grad
);

/**
 * @brief Triquintic interpolation
 * @tParam T
 * @tParam Array3DT
 * @return
 */
template <typename T, template <class> typename Array3D>
T triqerp(
    const Array3D<T>& vals,
    int i,
    int j,
    int k,
    NumT ku,
    NumT kv,
    NumT kw
);

/**
 * @brief Inv bilerp interpolation
 * @tParam T
 * @param val00
 * @param val10
 * @param val01
 * @param val11
 * @return
 */
NumT invBilerpApprox(
    const Vec3& pos,
    const Vec3& pos00,
    const Vec3& pos10,
    const Vec3& pos01,
    const Vec3& pos11,
    const Vec2& uv00,
    const Vec2& uv10,
    const Vec2& uv01,
    const Vec2& uv11,
    const Vec3& normal00,
    const Vec3& normal10,
    const Vec3& normal01,
    const Vec3& normal11,
    bool& isInside,
    Vec2& uv,
    Vec3& normal
);

/**
 * @brief Inv bilerp interpolation
 * @param pos
 * @param pos00
 * @param pos10
 * @param pos01
 * @param pos11
 * @param isInside
 * @param bar
 * @return
 */
void invBilerp2D(
    const Vec2& pos,
    const Vec2& pos00,
    const Vec2& pos10,
    const Vec2& pos01,
    const Vec2& pos11,
    bool& isInside,
    Vec2& bar
);

/**
 * @brief
 * @param positions
 * @return
 */
NumT areaPolygon(const VectorVec2& positions);

/**
 * @brief
 * @param positions
 * @return
 */
NumT volumePolyhedra(const VectorVec3& positions);

/**
 * @brief Integer direction
 * @return
 */
Vec2i vecToOctant(const Vec2& dir);

/**
 * @brief
 * @param lVal
 * @param rVal
 * @param val
 * @return
 */
NumT barycenter(NumT lVal, NumT rVal, NumT val);

template <typename V2, typename V3>
void triangleBarycenter(
    const V2& p,
    const V2& a,
    const V2& b,
    const V2& c,
    V3& bar,
    NumT tol = 0
);
template <typename V2>
NumT triangleInterpolation(
    const V2& p,
    const V2& a,
    NumT aVal,
    const V2& b,
    NumT bVal,
    const V2& c,
    NumT cVal,
    NumT tol = 0
);

/**
 * @brief Distance between a point and a segment
 * @param point
 * @param edge1
 * @param edge2
 * @return distance
 */
NumT distancePointEdge(
    const Vec2& point,
    const Vec2& eEnd1,
    const Vec2& eEnd2,
    Vec2* projection = nullptr
);
/**
 * @brief Distance between a point and a segment
 * @param point
 * @param edge1
 * @param edge2
 * @param boundToSegment
 * @return distance
 */
NumT distancePointLine(
    const Vec2& point,
    const Vec2& eEnd1,
    const Vec2& eEnd2,
    Vec2* projection = nullptr,
    bool boundToSegment = false
);

/**
 * @brief Distance between a point and a triangle
 * @param p
 * @param a
 * @param b
 * @param c
 * @param projection
 * @return distance
 */
NumT distancePointTriangle(
    const Vec3& p,
    const Vec3& a,
    const Vec3& b,
    const Vec3& c,
    Vec3* projPtr = nullptr,
    Vec3* barCoordPtr = nullptr,
    bool* isInsidePtr = nullptr
);

/**
 * @brief
 * @param p
 * @param dir
 * @param a
 * @param b
 * @param c
 * @param interPtr
 * @param barCoordPtr
 * @param distPtr
 */
bool intersectionRayTriangle(
    const Vec3& p,
    const Vec3& dir,
    const Vec3& a,
    const Vec3& b,
    const Vec3& c,
    Vec3* interPtr = nullptr,
    Vec3* barCoordPtr = nullptr,
    NumT* distPtr = nullptr
);
/**
 * @brief
 */
NumT triangleDistance(
    const Vec3& s0,
    const Vec3& s1,
    const Vec3& s2,
    const Vec3& t0,
    const Vec3& t1,
    const Vec3& t2,
    Vec3& P,  // sClosestPtr,
    Vec3& Q   // tClosestPtr
);
/**
 * @brief
 */
NumT distancePointEllipsoid(
    const Vec3& point,
    const Vec3& center,
    NumT eX,
    NumT eY,
    NumT eZ
);

/// @brief Thread-safe "bool" vector
class VectorBool {
public:
    /// @brief Default
    VectorBool() {}
    /**
     * @brief Constructor
     * @param size
     */
    VectorBool(size_t size);
    /**
     * @brief Get
     * @param pos
     * @return
     */
    bool get(size_t pos) const;
    /**
     * @brief Get
     * @param pos
     * @param val
     */
    void set(size_t pos, bool val);
    /**
     * @brief Get
     * @param pos
     * @param val
     * @return
     */
    bool getAndSet(size_t pos, bool val);

    /**
     * @brief
     * @param newSize
     */
    void resize(size_t newSize);

    /// @brief Reset to false
    void reset();

private:
    std::vector<uint32_t> m_data;
};

/**
 * @tparam T
 * @brief
 * @param currMin
 * @param testVal
 */
template <typename T>
void atomicMin(T& currMin, T& testVal);

/**
 * @tparam T
 * @brief
 * @param currMax
 * @param testVal
 */
template <typename T>
void atomicMax(T& currMax, T& testVal);

#if 1

// Ugly and not generic (-:

#define PARTICLE_LOOP(P) \
    _Pragma("omp parallel for") for (size_t P = 0; P < m_nPart; ++P)

#define GRID_LOOP2(I, J, GS)               \
    _Pragma("omp parallel for collapse(2)" \
    ) for (size_t J = 0; J < GS; ++J) for (size_t I = 0; I < GS; ++I)

#define GRID_LOOP2_IJ(I, J, GSI, GSJ)      \
    _Pragma("omp parallel for collapse(2)" \
    ) for (size_t J = 0; J < GSJ; ++J) for (size_t I = 0; I < GSI; ++I)

#define GRID_LOOP3(I, J, K, GS)                                            \
    _Pragma("omp parallel for collapse(3)"                                 \
    ) for (size_t K = 0; K < GS; ++K) for (size_t J = 0; J < GS;           \
                                           ++J) for (size_t I = 0; I < GS; \
                                                     ++I)

#define GRID_LOOP3_INT(I, J, K, GS)                        \
    _Pragma("omp parallel for collapse(3)"                 \
    ) for (int K = 0; K < GS; ++K) for (int J = 0; J < GS; \
                                        ++J) for (int I = 0; I < GS; ++I)

#define GRID_LOOP3_IJK(I, J, K, GS)                                    \
    _Pragma("omp parallel for collapse(3)"                             \
    ) for (size_t K = 0; K < GS[2]; ++K) for (size_t J = 0; J < GS[1]; \
                                              ++J) for (size_t I = 0;  \
                                                        I < GS[0]; ++I)

#else  // Parallel

#define PARTICLE_LOOP(P) for (size_t P = 0; P < m_nPart; ++P)

#define GRID_LOOP2(I, J, GS)        \
    for (size_t I = 0; I < GS; ++I) \
        for (size_t J = 0; J < GS; ++J)

#define GRID_LOOP2_IJ(I, J, GSI, GSJ) \
    for (size_t I = 0; I < GSI; ++I)  \
        for (size_t J = 0; J < GSJ; ++J)

#define GRID_LOOP3(I, J, K, GS)         \
    for (size_t I = 0; I < GS; ++I)     \
        for (size_t J = 0; J < GS; ++J) \
            for (size_t K = 0; K < GS; ++K)

#define GRID_LOOP3_INT(I, J, K, GS)  \
    for (int I = 0; I < GS; ++I)     \
        for (int J = 0; J < GS; ++J) \
            for (int K = 0; K < GS; ++K)

#define GRID_LOOP3_IJK(I, J, K, GSI, GSJ, GSK) \
    for (size_t I = 0; I < GSI; ++I)           \
        for (size_t J = 0; J < GSJ; ++J)       \
            for (size_t K = 0; K < GSK; ++K)

#endif  // Parallel

#define PARTICLE_LOOP_NP(P) for (size_t P = 0; P < m_nPart; ++P)

#define GRID_LOOP3_NP(I, J, K, GS)      \
    for (size_t K = 0; K < GS; ++K)     \
        for (size_t J = 0; J < GS; ++J) \
            for (size_t I = 0; I < GS; ++I)

#define GRID_LOOP3_NP_IJK(I, J, K, GS)     \
    for (size_t K = 0; K < GS[2]; ++K)     \
        for (size_t J = 0; J < GS[1]; ++J) \
            for (size_t I = 0; I < GS[0]; ++I)

#include "Common/Utils.tpp"

#endif  // _UTILS_HPP
