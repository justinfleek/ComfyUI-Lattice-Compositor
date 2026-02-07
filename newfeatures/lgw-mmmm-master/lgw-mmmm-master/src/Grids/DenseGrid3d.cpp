#ifndef DENSE_GRID_3D_TPP
#define DENSE_GRID_3D_TPP

#include "DenseGrid3d.hpp"
#include <cassert>

#include "Common/Utils.hpp"

namespace Grid {

template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D() {}

template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(const Vec3& start, const Vec3& end, NumT dx)
    : m_startPos(start),
      m_endPos(end),
      m_dx(dx, dx, dx),
      m_invDx(1. / dx, 1. / dx, 1. / dx) {
    static_assert(
        N == Dynamic, "YOU CALLED A CONSTRUCTOR FOR DYNAMIC GRID SIZES"
    );
    const Vec3 diff = end - start;
    const Vec3 gridResFloat =
        Vec3(diff[0] / m_dx[0], diff[1] / m_dx[1], diff[2] / m_dx[2]);
    const Vec3i hasDim(diff[0] > 0, diff[1] > 0, diff[2] > 0);
    m_cellCount = {
        std::max(int(std::ceil(gridResFloat.x())), hasDim[0]),
        std::max(int(std::ceil(gridResFloat.y())), hasDim[1]),
        std::max(int(std::ceil(gridResFloat.z())), hasDim[2])};
    m_nodeCount = m_cellCount.array() + 1;
    m_data.resize(m_nodeCount.prod());
    m_endPos = m_startPos + m_cellCount.cast<NumT>().cwiseProduct(m_dx);
}
template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(
    const Vec3& start, const Vec3& end, unsigned int res
)
    : m_startPos(start), m_endPos(end), m_nodeCount(res, res, res) {
    static_assert(
        N == Dynamic, "YOU CALLED A CONSTRUCTOR FOR DYNAMIC GRID SIZES"
    );
    const Vec3 diff = end - start;
    m_cellCount = m_nodeCount.array() - 1;
    m_dx = diff.cwiseQuotient(m_cellCount.cast<NumT>());
    m_invDx = m_dx.cwiseInverse();
    m_data.resize(m_nodeCount.prod());
}

template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(
    const Vec3& start, const Vec3& end, const Vec3& dx
)
    : m_startPos(start), m_endPos(end), m_dx(dx) {
    static_assert(
        N == Dynamic, "YOU CALLED A CONSTRUCTOR FOR DYNAMIC GRID SIZES"
    );
    m_invDx = m_dx.cwiseInverse();
    const Vec3 diff = end - start;
    const Vec3i hasDim(diff[0] > 0, diff[1] > 0, diff[2] > 0);
    const Vec3 gridResFloat =
        Vec3(diff[0] / m_dx[0], diff[1] / m_dx[1], diff[2] / m_dx[2]);
    m_cellCount = {
        std::max(int(std::ceil(gridResFloat.x())), hasDim[0]),
        std::max(int(std::ceil(gridResFloat.y())), hasDim[1]),
        std::max(int(std::ceil(gridResFloat.z())), hasDim[2])};
    m_nodeCount = m_cellCount.array() + 1;
    m_data.resize(m_nodeCount.prod());
    m_endPos = m_startPos + m_cellCount.cast<NumT>().cwiseProduct(m_dx);
}
template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(
    const Vec3& start, const Vec3& end, const Vec3i& res
)
    : m_startPos(start), m_endPos(end), m_nodeCount(res) {
    static_assert(
        N == Dynamic, "YOU CALLED A CONSTRUCTOR FOR DYNAMIC GRID SIZES"
    );
    const Vec3 diff = end - start;
    m_cellCount = m_nodeCount.array() - 1;

    m_dx = Vec3(
        diff[0] / m_cellCount[0], diff[1] / m_cellCount[1],
        diff[2] / m_cellCount[2]
    );
    m_invDx = m_dx.cwiseInverse();
    m_data.resize(m_nodeCount.prod());
}
template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(const Params::Grid& gridParams)
    : DenseGrid3D<T, N>(
          gridParams.gridStart, gridParams.gridEnd, gridParams.gridResolution
      ) {
    static_assert(
        N == Dynamic, "YOU CALLED A CONSTRUCTOR FOR DYNAMIC GRID SIZES"
    );
}
template <class T, int N>
DenseGrid3D<T, N>::DenseGrid3D(const Vec3& start, const Vec3& end)
    : m_startPos(start), m_endPos(end), m_nodeCount(N, N, N) {
    static_assert(N > 0, "YOU CALLED A CONSTRUCTOR FOR STATIC GRID SIZES");
    const Vec3 diff = end - start;
    m_cellCount = m_nodeCount.array() - 1;

    m_dx = Vec3(
        diff[0] / m_cellCount[0], diff[1] / m_cellCount[1],
        diff[2] / m_cellCount[2]
    );
    m_invDx = m_dx.cwiseInverse();
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getDx() const {
    return m_dx;
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getInvDx() const {
    return m_invDx;
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::getCellRes() const {
    return m_cellCount;
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::getNodeRes() const {
    return m_cellCount;
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getStartPos() const {
    return m_startPos;
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getEndPos() const {
    return m_endPos;
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getMidPos() const {
    return (m_startPos + m_endPos) / 2.;
}

template <class T, int N>
size_t DenseGrid3D<T, N>::getDataSize() const {
    return m_data.size();
}

template <class T, int N>
unsigned int DenseGrid3D<T, N>::ijk2idx(int x, int y, int z) const {
#ifndef NDEBUG
    if (!isIdValid(x, y, z)) {
        std::cerr << "Acessing cell " << x << ", " << y << ", " << z
                  << std::endl;
        throw std::out_of_range("Grid: wrong index");
    }  // oob
#endif
    return (z * m_nodeCount.y() + y) * m_nodeCount.x() + x;
}

template <class T, int N>
unsigned int DenseGrid3D<T, N>::ijk2idx(const Vec3i& ijk) const {
    return ijk2idx(ijk.x(), ijk.y(), ijk.z());
}

template <class T, int N>
unsigned int DenseGrid3D<T, N>::ijk2idx(const int ijk[3]) const {
    return ijk2idx(ijk[0], ijk[1], ijk[2]);
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::idx2ijk(unsigned int idx) const {
    assert(idx < m_data.size());
    Vec3i ijk;
    ijk.x() = idx % m_nodeCount.x();
    idx /= m_nodeCount.x();
    ijk.y() = idx % m_nodeCount.y();
    idx /= m_nodeCount.y();
    ijk.z() = idx % m_nodeCount.z();
    return ijk;
}

template <class T, int N>
T& DenseGrid3D<T, N>::operator()(int x, int y, int z) {
    return m_data[ijk2idx(x, y, z)];
}

template <class T, int N>
const T& DenseGrid3D<T, N>::operator()(int x, int y, int z) const {
    return m_data[ijk2idx(x, y, z)];
}

template <class T, int N>
T& DenseGrid3D<T, N>::operator()(const Vec3i& ijk) {
    return m_data[ijk2idx(ijk)];
}

template <class T, int N>
const T& DenseGrid3D<T, N>::operator()(const Vec3i& ijk) const {
    return m_data[ijk2idx(ijk)];
}

template <class T, int N>
T& DenseGrid3D<T, N>::operator()(const int ijk[3]) {
    return m_data[ijk2idx(ijk[0], ijk[1], ijk[2])];
}

template <class T, int N>
const T& DenseGrid3D<T, N>::operator()(const int ijk[3]) const {
    return m_data[ijk2idx(ijk[0], ijk[1], ijk[2])];
}

template <class T, int N>
T& DenseGrid3D<T, N>::operator()(unsigned int idx) {
    return m_data[idx];
}

template <class T, int N>
const T& DenseGrid3D<T, N>::operator()(unsigned int idx) const {
    return m_data[idx];
}

template <class T, int N>
T& DenseGrid3D<T, N>::ref(int i, int j, int k) {
    return this->operator()(i, j, k);
}
template <class T, int N>
T& DenseGrid3D<T, N>::ref(const Vec3i& ijk) {
    return this->operator()(ijk);
}
template <class T, int N>
T& DenseGrid3D<T, N>::ref(const int ijk[3]) {
    return this->operator()(ijk);
}

template <class T, int N>
void DenseGrid3D<T, N>::setConst(const T& val) {
#pragma omp parallel for
    for (int i = 0; i < m_data.size(); ++i) {
        m_data[i] = val;
    }
}

template <class T, int N>
Vec3b DenseGrid3D<T, N>::boundFlags(int i, int j, int k) const {
    Vec3b res{0, 0, 0};
    res[0] = (i < 0) ? -1 : (i >= m_nodeCount[0]) ? 1 : 0;
    res[1] = (j < 0) ? -1 : (j >= m_nodeCount[1]) ? 1 : 0;
    res[2] = (k < 0) ? -1 : (k >= m_nodeCount[2]) ? 1 : 0;
    return res;
}

template <class T, int N>
Vec3b DenseGrid3D<T, N>::boundFlags(const Vec3i& ijk) const {
    return boundFlags(ijk[0], ijk[1], ijk[2]);
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::boundFlagsLayer(int i, int j, int k, int layer) const {
    Vec3i res{0, 0, 0};
    res[0] = (i < layer) ? -1 : (i >= m_nodeCount[0] - layer) ? 1 : 0;
    res[1] = (j < layer) ? -1 : (j >= m_nodeCount[1] - layer) ? 1 : 0;
    res[2] = (k < layer) ? -1 : (k >= m_nodeCount[2] - layer) ? 1 : 0;
    return res;
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::boundFlagsLayer(const Vec3i& ijk, int layer) const {
    return boundFlagsLayer(ijk[0], ijk[1], ijk[2], layer);
}
template <class T, int N>
bool DenseGrid3D<T, N>::isIdValid(const Vec3i& ijk) const {
    return isIdValid(ijk[0], ijk[1], ijk[2]);
}

template <class T, int N>
bool DenseGrid3D<T, N>::isIdValid(int i, int j, int k) const {
    const Vec3b bf = boundFlags(i, j, k);
    return (!bf[0]) && (!bf[1]) && (!bf[2]);
}

template <class T, int N>
Vec3i DenseGrid3D<T, N>::pos2ijk(const Vec3& pos) const {
    Vec3 frac = pos2fracijk(pos);
    return frac.cast<int>();
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::pos2fracijk(const Vec3& pos) const {
    return (pos - m_startPos).cwiseProduct(m_invDx);
}

template <class T, int N>
T& DenseGrid3D<T, N>::refAt(const Vec3& pos) {
    return this->operator()(pos2ijk(pos));
}
template <class T, int N>
const T& DenseGrid3D<T, N>::refAt(const Vec3& pos) const {
    return this->operator()(pos2ijk(pos));
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getIJKPos(int x, int y, int z) const {
    // Clamp node
    Vec3i realIJK = this->idx2ijk(this->ijk2idx(x, y, z));
    return Vec3(
        m_startPos.x() + realIJK.x() * m_dx.x(),
        m_startPos.y() + realIJK.y() * m_dx.y(),
        m_startPos.z() + realIJK.z() * m_dx.z()
    );
}

template <class T, int N>
Vec3 DenseGrid3D<T, N>::getIJKPos(const Vec3i& ijk) const {
    return getIJKPos(ijk.x(), ijk.y(), ijk.z());
}

template <class T, int N>
T DenseGrid3D<T, N>::interpolate(const Vec3& _pos) const {
    Vec3 pos = _pos;
    const Vec3i trueBase = pos2ijk(pos);
    const Vec3i base =
        trueBase.cwiseMax(0).cwiseMin((m_cellCount.array() - 1).matrix());
    if (!isIdValid(trueBase)) {
        return m_data[ijk2idx(base)];
    }

    const Vec3 xPos = pos2fracijk(pos);

    return trilerp<T>(
        this->operator()(base[0], base[1], base[2]),
        this->operator()(base[0] + 1, base[1], base[2]),
        this->operator()(base[0], base[1] + 1, base[2]),
        this->operator()(base[0] + 1, base[1] + 1, base[2]),
        this->operator()(base[0], base[1], base[2] + 1),
        this->operator()(base[0] + 1, base[1], base[2] + 1),
        this->operator()(base[0], base[1] + 1, base[2] + 1),
        this->operator()(base[0] + 1, base[1] + 1, base[2] + 1),
        xPos[0] - base[0], xPos[1] - base[1], xPos[2] - base[2]
    );
}

template <class T, int N>
T DenseGrid3D<T, N>::interpolateCubic(const Vec3& _pos) const {
    Vec3 pos = _pos;
    const Vec3i trueBase = pos2ijk(pos);
    const Vec3i base = trueBase.cwiseMax(0).cwiseMin(m_cellCount);
    if (!isIdValid(trueBase)) {
        return m_data[ijk2idx(base)];
    }

    const Vec3 xPos = pos2fracijk(pos);

    // Not fine handling of BC
    for (int cmp = 0; cmp < 3; ++cmp) {
        if ((base[cmp] < 1) || (base[cmp] > m_cellCount[cmp] - 3)) {
            return interpolate(pos);
        }
    }

    return tricerp<T, N, DenseGrid3D>(
        *this, base[0], base[1], base[2], xPos[0] - base[0], xPos[1] - base[1],
        xPos[2] - base[2]
    );
}

template <typename T, int N>
constexpr bool sameStructure(const DenseGrid3D<T, N>& grid) {
    return true;
}
template <typename T, typename U, int N, typename... Types>
bool sameStructure(
    const DenseGrid3D<T, N>& grid, const DenseGrid3D<U, N>& other,
    const DenseGrid3D<Types, N>&... grids
) {
    return grid.getNodeRes() == other.getNodeRes() &&
           sameStructure(other, grids...);
}

template <typename T, int N>
size_t gridSize(const DenseGrid3D<T, N>& grid) {
    return grid.getDataSize();
}
template <typename T, int N, typename... Types>
size_t gridSize(
    const DenseGrid3D<T, N>& grid, const DenseGrid3D<Types, N>&... grids
) {
    assert(sameStructure(grid, grids...));
    return grid.getDataSize();
}

template <typename T, int N, typename... Types>
Vec3i gridIdx2ijk(
    size_t idx, const DenseGrid3D<T, N>& grid,
    const DenseGrid3D<Types, N>&... others
) {
    return grid.idx2ijk(idx);
}

template <typename T, int N, typename... Types>
size_t gridIjk2Idx(
    Vec3i ijk, const DenseGrid3D<T, N>& grid,
    const DenseGrid3D<Types, N>&... others
) {
    return grid.ijk2idx(ijk);
}

template <typename T, int N>
std::tuple<T&> getGridRefs(size_t idx, DenseGrid3D<T, N>& grid) {
    return std::tuple<T&>(grid(idx));
}
template <typename T, int N, typename... Types>
std::tuple<T&, Types&...> getGridRefs(
    size_t idx, DenseGrid3D<T, N>& grid, DenseGrid3D<Types, N>&... grids
) {
    return std::tuple_cat(
        std::tuple<T&>(grid(idx)), getGridRefs(idx, grids...)
    );
}

template <typename T, int N>
std::tuple<const T&> getConstGridRefs(
    size_t idx, const DenseGrid3D<T, N>& grid
) {
    return std::tuple<const T&>(grid(idx));
}
template <typename T, int N, typename... Types>
std::tuple<const T&, const Types&...> getConstGridRefs(
    size_t idx, const DenseGrid3D<T, N>& grid,
    const DenseGrid3D<Types, N>&... grids
) {
    return std::tuple_cat(
        std::tuple<const T&>(grid(idx)), getConstGridRefs(idx, grids...)
    );
}

template <int N, typename... Types>
void forEach(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    DenseGrid3D<Types, N>&... grids
) {
    const size_t size = gridSize(grids...);
#pragma omp parallel for
    for (size_t i = 0; i < size; ++i) {
        const Vec3i ijk = gridIdx2ijk(i, grids...);

        std::tuple<const Vec3i&, Types&...> args = std::tuple_cat(
            std::tuple<const Vec3i&>(ijk), getGridRefs(i, grids...)
        );
        std::apply(callback, args);
    }
}
template <int N, typename... Types>
void forEachSerial(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    DenseGrid3D<Types, N>&... grids
) {
    const size_t size = gridSize(grids...);
    for (size_t i = 0; i < size; ++i) {
        const Vec3i ijk = gridIdx2ijk(i, grids...);

        std::tuple<const Vec3i&, Types&...> args = std::tuple_cat(
            std::tuple<const Vec3i&>(ijk), getGridRefs(i, grids...)
        );
        std::apply(callback, args);
    }
}

template <int N, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, DenseGrid3D<Types, N>&... grids
) {
    assert(sameStructure(grids...));
    // These are typically in a parallel loop already, so don't parallelize.
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getGridRefs(gridIjk2Idx(ijk, grids...), grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

template <typename... Types>
void rangeWriteParallel(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, DenseGrid3D<Types>&... grids
) {
    assert(sameStructure(grids...));
#pragma omp parallel for collapse(3)
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getGridRefs(gridIjk2Idx(ijk, grids...), grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

template <typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, const Types&...)>&
        callback,
    const Vec3i& lower, const Vec3i& upper, const DenseGrid3D<Types>&... grids
) {
    assert(sameStructure(grids...));
    // These are typically in a parallel loop already, so don't parallelize.
#pragma unroll
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, const Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getConstGridRefs(gridIjk2Idx(ijk, grids...), grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

}  // namespace Grid

#endif  // DENSE_GRID_3D_TPP
