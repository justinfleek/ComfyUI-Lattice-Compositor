#ifndef BLOCK_GRID_3D_CPP
#define BLOCK_GRID_3D_CPP

#include "BlockGrid3d.hpp"
#include <algorithm>
// #include <format>
#include <iostream>
#include <memory>
#include <span>
#include <stdexcept>
#include <tuple>
#include <unordered_set>

namespace Grid {

template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(){};

template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(const Vec3& start, const Vec3& end, NumT dx)
    : m_startPos(start),
      m_endPos(end),
      m_dx(dx, dx, dx),
      m_invDx(1. / dx, 1. / dx, 1. / dx) {
    const Vec3 diff = end - start;
    const Vec3 gridResFloat =
        Vec3(diff[0] / m_dx[0], diff[1] / m_dx[1], diff[2] / m_dx[2]);
    const Vec3i hasDim(diff[0] > 0, diff[1] > 0, diff[2] > 0);
    m_cellCount = {
        std::max(int(std::ceil(gridResFloat.x())), hasDim[0]),
        std::max(int(std::ceil(gridResFloat.y())), hasDim[1]),
        std::max(int(std::ceil(gridResFloat.z())), hasDim[2])};
    m_nodeCount = m_cellCount.array() + 1;
    m_endPos = m_startPos + m_cellCount.cast<NumT>().cwiseProduct(m_dx);

    initBlocks();
}

template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(
    const Vec3& start, const Vec3& end, unsigned int res
)
    : m_startPos(start), m_endPos(end), m_nodeCount(res, res, res) {
    const Vec3 diff = end - start;
    m_cellCount = m_nodeCount.array() - 1;
    m_dx = diff.cwiseQuotient(m_cellCount.cast<NumT>());
    m_invDx = m_dx.cwiseInverse();

    initBlocks();
}

template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(
    const Vec3& start, const Vec3& end, const Vec3& dx
)
    : m_startPos(start), m_endPos(end), m_dx(dx) {
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
    m_endPos = m_startPos + m_cellCount.cast<NumT>().cwiseProduct(m_dx);

    initBlocks();
}
template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(
    const Vec3& start, const Vec3& end, const Vec3i& res
)
    : m_startPos(start), m_endPos(end), m_nodeCount(res) {
    const Vec3 diff = end - start;
    m_cellCount = m_nodeCount.array() - 1;
    m_dx = Vec3(
        diff[0] / m_cellCount[0], diff[1] / m_cellCount[1],
        diff[2] / m_cellCount[2]
    );
    m_invDx = m_dx.cwiseInverse();

    initBlocks();
}

template <class T, int POW>
BlockGrid3D<T, POW>::BlockGrid3D(const Params::Grid& gridParams)
    : BlockGrid3D<T, POW>(
          gridParams.gridStart, gridParams.gridEnd, gridParams.gridResolution
      ) {}

template <class T, int POW>
void BlockGrid3D<T, POW>::initBlocks() {
    m_blockCount = Vec3i(
        m_nodeCount[0] >> POW, m_nodeCount[1] >> POW, m_nodeCount[2] >> POW
    );
    m_blockCount[0] += (m_nodeCount[0] & BlockMask) > 0;
    m_blockCount[1] += (m_nodeCount[1] & BlockMask) > 0;
    m_blockCount[2] += (m_nodeCount[2] & BlockMask) > 0;
    m_nodeCountActual = Vec3i(
        m_blockCount[0] << POW, m_blockCount[1] << POW, m_blockCount[2] << POW
    );

    m_ptrToData.resize(m_blockCount.prod(), nullptr);
    m_nBlocks = 0;
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getDx() const {
    return m_dx;
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getInvDx() const {
    return m_invDx;
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::getCellRes() const {
    return m_cellCount;
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::getNodeRes() const {
    return m_cellCount;
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getStartPos() const {
    return m_startPos;
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getEndPos() const {
    return m_endPos;
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getMidPos() const {
    return (m_startPos + m_endPos) / 2.;
}

template <class T, int POW>
size_t BlockGrid3D<T, POW>::getDataSize() const {
    return m_nBlocks * BlockDataSize;
}

template <class T, int POW>
size_t BlockGrid3D<T, POW>::blockId(int i, int j, int k) const {
    size_t xBlock = i >> POW, yBlock = j >> POW, zBlock = k >> POW;
    return (zBlock * m_blockCount.y() + yBlock) * m_blockCount.x() + xBlock;
}

template <class T, int POW>
int BlockGrid3D<T, POW>::inBlockId(int i, int j, int k) const {
    int xInBlock = i & BlockMask, yInBlock = j & BlockMask,
        zInBlock = k & BlockMask;
    return (((zInBlock << POW) + yInBlock) << POW) + xInBlock;
}

template <class T, int POW>
std::vector<size_t> BlockGrid3D<T, POW>::positionsToGridBlock(
    const std::vector<Vec3>& pos, NumT stencilSize
) const {
    std::unordered_set<size_t> blockIdx;
#pragma omp parallel
    {
        std::unordered_set<size_t> blockIdxLocal;
#pragma omp for
        for (size_t i = 0; i < pos.size(); ++i) {
            Vec3 mPos = pos2fracijk(pos[i]);
            Vec3i base = (mPos.array() - (stencilSize / 2) + 1).cast<int>();
            Vec3i upper = base + Vec3i::Constant(stencilSize - 1);

            base = Vec3i(
                (base[0] & ~BlockMask), (base[1] & ~BlockMask),
                (base[2] & ~BlockMask)
            );
            upper = Vec3i(
                (upper[0] & ~BlockMask), (upper[1] & ~BlockMask),
                (upper[2] & ~BlockMask)
            );

#pragma unroll
            for (int z = base[2]; z <= upper[2]; z += BlockSize)
                for (int y = base[1]; y <= upper[1]; y += BlockSize)
                    for (int x = base[0]; x <= upper[0]; x += BlockSize)
                        blockIdxLocal.insert(blockId(x, y, z));
        }
#pragma omp critical
        { blockIdx.insert(blockIdxLocal.begin(), blockIdxLocal.end()); }
    }
    std::vector<size_t> blocks;
    blocks.insert(blocks.end(), blockIdx.begin(), blockIdx.end());
    std::sort(blocks.begin(), blocks.end());
    return blocks;
}

template <class T, int POW>
void BlockGrid3D<T, POW>::reserveGridBlocks(const std::vector<size_t>& blockId
) {
    m_ptrData.push_back(std::make_unique<T[]>(blockId.size() * BlockDataSize));
    m_activeBlocks.insert(m_activeBlocks.end(), blockId.begin(), blockId.end());
#pragma omp parallel for
    for (size_t i = 0; i < blockId.size(); ++i) {
        T* block = m_ptrData.back().get() + i * BlockDataSize;
        m_ptrToData[blockId[i]] = block;
        for (size_t j = 0; j < BlockDataSize; ++j) {
            block[j] = m_background;
        }
    }
    m_nBlocks += blockId.size();
}

template <class T, int POW>
T& BlockGrid3D<T, POW>::refUnsafe(int i, int j, int k) {
    T* block = m_ptrToData[blockId(i, j, k)];
    return block[inBlockId(i, j, k)];
}
template <class T, int POW>
T& BlockGrid3D<T, POW>::refUnsafe(size_t bId, int inId) {
    return m_ptrToData[bId][inId];
}

template <class T, int POW>
T& BlockGrid3D<T, POW>::ref(size_t bId, int inId) {
    T* block = m_ptrToData[bId];
    if (block != nullptr) {
        return block[inId];
    } else {
        m_ptrData.push_back(std::make_unique<T[]>(BlockDataSize));
        m_activeBlocks.push_back(bId);
        block = m_ptrData.back().get();
        m_ptrToData[bId] = block;
        std::cout << "Allocator called! idx: " << bId << " " << inId << "\n";
#pragma omp parallel for
        for (size_t j = 0; j < BlockDataSize; ++j) {
            block[j] = m_background;
        }
        m_nBlocks++;
        return block[inId];
    }
}

template <class T, int POW>
const T& BlockGrid3D<T, POW>::ref(size_t bId, int inId) const {
    T* block = m_ptrToData[bId];
    if (block != nullptr) {
        return block[inId];
    } else {
        return m_background;
    }
}

template <class T, int POW>
T& BlockGrid3D<T, POW>::ref(int i, int j, int k) {
    const size_t bid = blockId(i, j, k);
    T* block = m_ptrToData[bid];

    if (block != nullptr) {
    } else {
        m_ptrData.push_back(std::make_unique<T[]>(BlockDataSize));
        m_activeBlocks.push_back(bid);
        block = m_ptrData.back().get();
        m_ptrToData[bid] = block;
#pragma omp parallel for
        for (size_t j = 0; j < BlockDataSize; ++j) {
            block[j] = m_background;
        }
        m_nBlocks++;
    }
    return block[inBlockId(i, j, k)];
}
template <class T, int POW>
T& BlockGrid3D<T, POW>::ref(const Vec3i& ijk) {
    return ref(ijk[0], ijk[1], ijk[2]);
}
template <class T, int POW>
T& BlockGrid3D<T, POW>::ref(const int ijk[3]) {
    return ref(ijk[0], ijk[1], ijk[2]);
}

template <class T, int POW>
BlockGrid3D<T, POW>& BlockGrid3D<T, POW>::set(
    int i, int j, int k, const T& data
) {
    ref(i, j, k) = data;
    return *this;
}

template <class T, int POW>
BlockGrid3D<T, POW>& BlockGrid3D<T, POW>::set(const Vec3i& ijk, const T& data) {
    set(ijk[0], ijk[1], ijk[2], data);
    return *this;
}

template <class T, int POW>
BlockGrid3D<T, POW>& BlockGrid3D<T, POW>::set(const int ijk[3], const T& data) {
    set(ijk[0], ijk[1], ijk[2], data);
    return *this;
}

template <class T, int POW>
const T& BlockGrid3D<T, POW>::operator()(int x, int y, int z) const {
    auto* block = m_ptrToData[blockId(x, y, z)];
    if (!block) {
        return m_background;
    }

    return block[inBlockId(x, y, z)];
}
template <class T, int POW>
const T& BlockGrid3D<T, POW>::operator()(const Vec3i& ijk) const {
    return this->operator()(ijk[0], ijk[1], ijk[2]);
}

template <class T, int POW>
const T& BlockGrid3D<T, POW>::operator()(const int ijk[3]) const {
    return this->operator()(ijk[0], ijk[1], ijk[2]);
}

template <class T, int POW>
void BlockGrid3D<T, POW>::setConst(const T& val) {
    m_ptrData.clear();
    m_activeBlocks.clear();
#pragma omp parallel for
    for (size_t i = 0; i < m_ptrToData.size(); ++i) {
        m_ptrToData[i] = nullptr;
    }
    m_nBlocks = 0;
    m_background = val;
}

template <class T, int POW>
Vec3b BlockGrid3D<T, POW>::boundFlags(int i, int j, int k) const {
    Vec3b res{0, 0, 0};
    res[0] = (i < 0) ? -1 : (i >= m_nodeCount[0]) ? 1 : 0;
    res[1] = (j < 0) ? -1 : (j >= m_nodeCount[1]) ? 1 : 0;
    res[2] = (k < 0) ? -1 : (k >= m_nodeCount[2]) ? 1 : 0;
    return res;
}

template <class T, int POW>
Vec3b BlockGrid3D<T, POW>::boundFlags(const Vec3i& ijk) const {
    return boundFlags(ijk[0], ijk[1], ijk[2]);
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::boundFlagsLayer(int i, int j, int k, int layer)
    const {
    Vec3i res{0, 0, 0};
    res[0] = (i < layer) ? -1 : (i >= m_nodeCount[0] - layer) ? 1 : 0;
    res[1] = (j < layer) ? -1 : (j >= m_nodeCount[1] - layer) ? 1 : 0;
    res[2] = (k < layer) ? -1 : (k >= m_nodeCount[2] - layer) ? 1 : 0;
    return res;
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::boundFlagsLayer(const Vec3i& ijk, int layer) const {
    return boundFlagsLayer(ijk[0], ijk[1], ijk[2], layer);
}
template <class T, int POW>
bool BlockGrid3D<T, POW>::isIdValid(const Vec3i& ijk) const {
    return isIdValid(ijk[0], ijk[1], ijk[2]);
}

template <class T, int POW>
bool BlockGrid3D<T, POW>::isIdValid(int i, int j, int k) const {
    const Vec3b bf = boundFlags(i, j, k);
    return (!bf[0]) && (!bf[1]) && (!bf[2]);
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::pos2ijk(const Vec3& pos) const {
    Vec3 frac = pos2fracijk(pos);
    return frac.cast<int>();
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::pos2fracijk(const Vec3& pos) const {
    return (pos - m_startPos).cwiseProduct(m_invDx);
}

template <class T, int POW>
Vec3i BlockGrid3D<T, POW>::idx2ijk(size_t bId, int inId) const {
    assert(inId < BlockDataSize);

    int inI = inId & BlockMask;
    inId >>= POW;
    int inJ = inId & BlockMask;
    inId >>= POW;
    int inK = inId & BlockMask;

    int bX = bId % m_blockCount.x();
    bId /= m_blockCount.x();
    int bY = bId % m_blockCount.y();
    bId /= m_blockCount.y();
    int bZ = bId;

    Vec3i ret((bX << POW) + inI, (bY << POW) + inJ, (bZ << POW) + inK);
    assert(isIdValid(ret));
    return ret;
}
template <class T, int POW>
T& BlockGrid3D<T, POW>::refAt(const Vec3& pos) {
    return ref(pos2ijk(pos));
}
template <class T, int POW>
const T& BlockGrid3D<T, POW>::refAt(const Vec3& pos) const {
    return this->operator()(pos2ijk(pos));
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getIJKPos(int x, int y, int z) const {
    // Clamp node
    return Vec3(
        m_startPos.x() + x * m_dx.x(), m_startPos.y() + y * m_dx.y(),
        m_startPos.z() + z * m_dx.z()
    );
}

template <class T, int POW>
Vec3 BlockGrid3D<T, POW>::getIJKPos(const Vec3i& ijk) const {
    return getIJKPos(ijk.x(), ijk.y(), ijk.z());
}

template <class T, int POW>
bool BlockGrid3D<T, POW>::isActive(size_t bId, int inId) const {
    return m_ptrToData[bId] != nullptr &&
           m_ptrToData[bId][inId] != m_background;
}

template <class T, int POW>
bool BlockGrid3D<T, POW>::isActive(int i, int j, int k) const {
    size_t bId = blockId(i, j, k);
    return m_ptrToData[bId] != nullptr &&
           m_ptrToData[bId][inBlockId(i, j, k)] != m_background;
}

template <bool Safe, int POW, typename T>
std::tuple<T&> getGridRefs(size_t bId, int inId, BlockGrid3D<T, POW>& grid) {
    if constexpr (Safe) {
        return std::tuple<T&>(grid.ref(bId, inId));
    } else {
        return std::tuple<T&>(grid.refUnsafe(bId, inId));
    }
}
template <bool Safe, int POW, typename T, typename... Types>
std::tuple<T&, Types&...> getGridRefs(
    size_t bId, int inId, BlockGrid3D<T, POW>& grid,
    BlockGrid3D<Types, POW>&... grids
) {
    if constexpr (Safe) {
        return std::tuple_cat(
            std::tuple<T&>(grid.ref(bId, inId)),
            getGridRefs<Safe>(bId, inId, grids...)
        );
    } else {
        return std::tuple_cat(
            std::tuple<T&>(grid.refUnsafe(bId, inId)),
            getGridRefs<Safe>(bId, inId, grids...)
        );
    }
}
template <int POW, typename T>
std::tuple<const T&> getGridRefs(
    size_t bId, int inId, const BlockGrid3D<T, POW>& grid
) {
    return std::tuple<const T&>(grid.ref(bId, inId));
}
template <int POW, typename T, typename... Types>
std::tuple<const T&, const Types&...> getGridRefs(
    size_t bId, int inId, const BlockGrid3D<T, POW>& grid,
    const BlockGrid3D<Types, POW>&... grids
) {
    return std::tuple_cat(
        std::tuple<const T&>(grid.ref(bId, inId)),
        getGridRefs(bId, inId, grids...)
    );
}

template <bool Safe, int POW, typename T>
std::tuple<T&> getGridRefs(int i, int j, int k, BlockGrid3D<T, POW>& grid) {
    if constexpr (!Safe) {
        return std::tuple<T&>(grid.refUnsafe(i, j, k));
    } else {
        return std::tuple<T&>(grid.ref(i, j, k));
    }
}
template <bool Safe, int POW, typename T, typename... Types>
std::tuple<T&, Types&...> getGridRefs(
    int i, int j, int k, BlockGrid3D<T, POW>& grid,
    BlockGrid3D<Types, POW>&... grids
) {
    if constexpr (!Safe) {
        return std::tuple_cat(
            std::tuple<T&>(grid.refUnsafe(i, j, k)),
            getGridRefs<Safe>(i, j, k, grids...)
        );
    } else {
        return std::tuple_cat(
            std::tuple<T&>(grid.ref(i, j, k)),
            getGridRefs<Safe>(i, j, k, grids...)
        );
    }
}

template <int POW, typename T, typename... Types>
std::pair<size_t, int> ijk2Idx(
    int i, int j, int k, const BlockGrid3D<T, POW>& grid,
    const BlockGrid3D<Types, POW>&... grids
) {
    return {grid.blockId(i, j, k), grid.inBlockId(i, j, k)};
}

template <int POW>
bool isActive(size_t bId, int inId) {
    return true;
}

template <int POW, typename T, typename... Types>
bool isActive(size_t bId, int inId, const BlockGrid3D<T, POW>& grid) {
    return grid.isActive(bId, inId);
}

template <int POW, typename T, typename... Types>
bool isActive(
    size_t bId, int inId, const BlockGrid3D<T, POW>& grid,
    const BlockGrid3D<Types, POW>&... grids
) {
#ifdef NDEBUG
    return grid.isActive(bId, inId);
#else
    return grid.isActive(bId, inId) && isActive(bId, inId, grids...);
#endif
}

template <bool OnlyActive = true, int POW, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, BlockGrid3D<Types, POW>&... grids
) {
    // assert(sameStructure(grids...));
    // These are typically in a parallel loop already, so don't parallelize.
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                size_t bId;
                int inId;
                std::tie(bId, inId) = ijk2Idx(i, j, k, grids...);
                // if constexpr (OnlyActive) {
                //     if (!isActive(bId, inId, grids...)) {
                //         continue;
                //     }
                // }
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getGridRefs<!OnlyActive>(bId, inId, grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

template <bool OnlyActive = true, int POW, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, const Types&...)>&
        callback,
    const Vec3i& lower, const Vec3i& upper,
    const BlockGrid3D<Types, POW>&... grids
) {
    // assert(sameStructure(grids...));
    // These are typically in a parallel loop already, so don't parallelize.
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                size_t bId;
                int inId;
                std::tie(bId, inId) = ijk2Idx(i, j, k, grids...);
                // if constexpr (OnlyActive) {
                //     if (!isActive(bId, inId, grids...)) {
                //         continue;
                //     }
                // }
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, const Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getGridRefs(bId, inId, grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

template <bool OnlyActive = true, int POW, typename... Types>
void rangeWriteParallel(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i& lower, const Vec3i& upper, BlockGrid3D<Types, POW>&... grids
) {
    // assert(sameStructure(grids...));
#pragma omp parallel for collapse(3)
    for (int k = lower[2]; k < upper[2]; ++k) {
        for (int j = lower[1]; j < upper[1]; ++j) {
            for (int i = lower[0]; i < upper[0]; ++i) {
                size_t bId;
                int inId;
                std::tie(bId, inId) = ijk2Idx(i, j, k, grids...);
                if constexpr (OnlyActive) {
                    if (!isActive(bId, inId, grids...)) {
                        continue;
                    }
                }
                Vec3i ijk(i, j, k);
                Vec3i offset = ijk - lower;
                std::tuple<const Vec3i&, const Vec3i&, Types&...> args =
                    std::tuple_cat(
                        std::tuple<const Vec3i&, const Vec3i&>(ijk, offset),
                        getGridRefs<!OnlyActive>(bId, inId, grids...)
                    );
                std::apply(callback, args);
            }
        }
    }
}

template <int POW, typename T, typename... Types>
const std::vector<size_t>& getActiveBlocks(
    const BlockGrid3D<T, POW>& grid, const BlockGrid3D<Types, POW>&... grids
) {
    return grid.getActiveBlocks();
}

template <int POW, typename T, typename... Types>
Vec3i getIjk(
    size_t blockId, int inId, const BlockGrid3D<T, POW>& grid,
    const BlockGrid3D<Types, POW>&... grids
) {
    return grid.idx2ijk(blockId, inId);
}

template <int POW, typename... Types>
void forEach(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    BlockGrid3D<Types, POW>&... grids
) {
    const auto& blocks = getActiveBlocks(grids...);
    // constexpr int BlockSize = BlockGrid3D<
    //     typename std::tuple_element<0, Types...>::type, POW>::BlockDataSize;
    constexpr int BlockDataSize = BlockGrid3D<
        typename std::tuple_element<0, std::tuple<Types...>>::type,
        POW>::BlockDataSize;
    // constexpr int BlockSize = std::tuple_element<
    //     0, std::tuple<BlockGrid3D<Types..., POW>>>::type::BlockDataSize;
#pragma omp parallel for
    for (size_t bI = 0; bI < blocks.size(); ++bI) {
        size_t bId = blocks[bI];
        for (int inId = 0; inId < BlockDataSize; ++inId) {
            // if (!isActive(bId, inId, grids...)) {
            //     continue;
            // }
            Vec3i ijk = getIjk(bId, inId, grids...);
            std::tuple<const Vec3i&, Types&...> args = std::tuple_cat(
                std::tuple<const Vec3i&>(ijk),
                getGridRefs<true>(bId, inId, grids...)
            );
            std::apply(callback, args);
        }
    }
}
}  // namespace Grid

#endif  // !BLOCK_GRID_3D_CPP
