#ifndef DENSE_GRID_3D_HPP
#define DENSE_GRID_3D_HPP

#include <type_traits>
#include <vector>
#include "Common/CustomTypes.hpp"
#include "GridParameters.hpp"

namespace Grid {

using namespace Type;

static constexpr int Dynamic = -1;
template <class T, int N>
struct GridData {
    using type = std::array<T, N * N * N>;
};
template <class T>
struct GridData<T, Dynamic> {
    using type = std::vector<T>;
};
template <class T, int N>
using GridDataType = typename GridData<T, N>::type;

/**
 * @brief Axis-aligned grid
 * The grid resolution is specified in terms of number of *cells*, as oppose to
 * number of *nodes*. e.g. A "64^3" grid will have in fact 65^3 node values, and
 * 64^3 cells. This makes certain grid operations easier to write.
 */

template <class T, int N = Dynamic>
class DenseGrid3D {
public:
    /// Constructors

    /**
     * @brief Default
     */
    DenseGrid3D();

    /**
     * @brief Uniform spatial resolution
     */
    DenseGrid3D(const Vec3& start, const Vec3& end, NumT dx);
    /**
     * @brief Uniform grid resolution
     */
    DenseGrid3D(const Vec3& start, const Vec3& end, unsigned int res);

    /**
     * @brief Varying spatial resolution
     */
    DenseGrid3D(const Vec3& start, const Vec3& end, const Vec3& dx);
    /**
     * @brief Varying grid resolution
     */
    DenseGrid3D(const Vec3& start, const Vec3& end, const Vec3i& res);
    DenseGrid3D(const Vec3& start, const Vec3& end);
    DenseGrid3D(const Params::Grid& params);

    /// Data
    /**
     * @brief Spatial resolution
     */
    Vec3 getDx() const;
    Vec3 getInvDx() const;
    /**
     * @brief Grid resolution
     */
    Vec3i getCellRes() const;
    /**
     * @brief Grid resolution
     */
    Vec3i getNodeRes() const;
    /**
     * @brief Corner
     */
    Vec3 getStartPos() const;
    /**
     * @brief Corner
     */
    Vec3 getEndPos() const;
    /**
     * @brief Mid
     */
    Vec3 getMidPos() const;

    /**
     * @brief Size
     */
    size_t getDataSize() const;

    // bool isTiled() const { return isTiled; }

    /// Index operators
    /**
     * @brief 3D to 1D index
     */
    unsigned int ijk2idx(int x, int y, int z) const;
    /**
     * @brief 3D to 1D index
     */
    unsigned int ijk2idx(const Vec3i& ijk) const;
    /**
     * @brief 3D to 1D index
     */
    unsigned int ijk2idx(const int ijk[3]) const;
    /**
     * @brief 1D to 3D index
     */
    Vec3i idx2ijk(unsigned int idx) const;

    /// Grid access operators
    /**
     * @brief Read and write
     */
    T& operator()(int x, int y, int z);
    /**
     * @brief Read only
     */
    const T& operator()(int x, int y, int z) const;
    /**
     * @brief Read and write
     */
    T& operator()(const Vec3i& ijk);
    /**
     * @brief Read only
     */
    const T& operator()(const Vec3i& ijk) const;
    /**
     * @brief Read and write
     */
    T& operator()(const int ijk[3]);
    /**
     * @brief Read only
     */
    const T& operator()(const int ijk[3]) const;
    /**
     * @brief Read and write
     */
    T& operator()(unsigned int idx);
    /**
     * @brief Read only
     */
    const T& operator()(unsigned int idx) const;

    T& ref(int i, int j, int k);
    T& ref(const Vec3i& ijk);
    T& ref(const int ijk[3]);

    /**
     * @brief Fill
     */
    void setConst(const T& val);

    /// OOB checks
    /**
     * @brief OOB per component
     */
    Vec3b boundFlags(int i, int j, int k) const;
    /**
     * @brief OOB per component
     */
    Vec3b boundFlags(const Vec3i& ijk) const;
    /**
     * @brief OOB per component
     */
    Vec3i boundFlagsLayer(int i, int j, int k, int layer) const;
    /**
     * @brief OOB per component
     */
    Vec3i boundFlagsLayer(const Vec3i& ijk, int layer) const;
    /**
     * @brief OOB
     */
    bool isIdValid(const Vec3i& ijk) const;
    /**
     * @brief OOB
     */
    bool isIdValid(int i, int j, int k) const;

    /// Position reads

    /**
     * @brief Index cell of the position
     */
    Vec3i pos2ijk(const Vec3& pos) const;
    /**
     * @brief Fractional index cell of the position. i.e. don't cast to integer.
     */
    Vec3 pos2fracijk(const Vec3& pos) const;
    /**
     * @brief Value cell of the position
     */
    T& refAt(const Vec3& pos);
    /**
     * @brief Value cell of the position
     */
    const T& refAt(const Vec3& pos) const;

    /**
     * @brief Node world position
     */
    Vec3 getIJKPos(int x, int y, int z) const;
    /**
     * @brief Node world position
     */
    Vec3 getIJKPos(const Vec3i& ijk) const;

    /// Interpolation
    /**
     * @brief Interpolate value at world coordinate
     */
    T interpolate(const Vec3& pos) const;
    /**
     * @brief Interpolate value at world coordinate
     */
    T interpolateCubic(const Vec3& pos) const;

protected:
    /// @brief Corners
    Vec3 m_startPos, m_endPos;

    /// @brief Resolution (in cell count)
    Vec3i m_cellCount;
    /// @brief Resolution (in node count). *Always larger than m_cellCount by
    /// 1*.
    Vec3i m_nodeCount;
    /// @brief Resolution (in spatial unit)
    Vec3 m_dx;
    Vec3 m_invDx;

    // Allow evaluations out of the boundary and clamp to closest point
    // bool m_allowOOB;

    /// @brief Data
    // std::vector<T> m_data;
    GridDataType<T, N> m_data;
};  // class DenseGrid3D

template <int N, typename... Types>
void forEach(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    DenseGrid3D<Types, N>&... grids
);

template <int N, typename... Types>
void forEachSerial(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    DenseGrid3D<Types, N>&... grids
);

template <int N, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, DenseGrid3D<Types, N>&... grids
);

template <int N, typename... Types>
void rangeWriteParallel(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, DenseGrid3D<Types, N>&... grids
);

template <int N, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, const Types&...)>&
        callback,
    const Vec3i& lower, const Vec3i& upper,
    const DenseGrid3D<Types, N>&... grids
);

}  // namespace Grid

#endif  // DENSE_GRID_3D_HPP

#include "DenseGrid3d.cpp"
