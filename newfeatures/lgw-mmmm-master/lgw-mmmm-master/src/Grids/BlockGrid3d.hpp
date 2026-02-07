#ifndef BLOCK_GRID_3D_HPP
#define BLOCK_GRID_3D_HPP

#include <array>
#include <memory>
#include <vector>
#include "Common/CustomTypes.hpp"
#include "GridParameters.hpp"

namespace Grid {
using namespace Type;

template <class T, int POW>
class BlockGrid3D {
public:
    static constexpr int BlockSize = (1 << POW);
    static constexpr int BlockMask = (1 << POW) - 1;
    static constexpr int BlockDataSize = (1 << POW << POW << POW);

    using BlockType = std::array<T, BlockDataSize>;
    using FlagType = std::array<bool, BlockDataSize>;

    BlockGrid3D();
    BlockGrid3D(const Vec3& start, const Vec3& end, NumT dx);
    /**
     * @brief Uniform grid resolution
     */
    BlockGrid3D(const Vec3& start, const Vec3& end, unsigned int res);

    /**
     * @brief Varying spatial resolution
     */
    BlockGrid3D(const Vec3& start, const Vec3& end, const Vec3& dx);
    /**
     * @brief Varying grid resolution
     */
    BlockGrid3D(const Vec3& start, const Vec3& end, const Vec3i& res);
    BlockGrid3D(const Params::Grid& params);

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

    /// Grid memory allocation
    std::vector<size_t> positionsToGridBlock(
        const std::vector<Vec3>& pos, NumT stencilSize
    ) const;

    void reserveGridBlocks(const std::vector<size_t>& blockId);

    /// Grid access operators
    /**
     * @brief Read and write. THIS IS NOT THREAD SAFE
     */
    // T& operator()(int x, int y, int z);
    T& ref(size_t blkId, int inId);
    const T& ref(size_t blkId, int inId) const;
    T& ref(int i, int j, int k);
    T& ref(const Vec3i& ijk);
    T& ref(const int ijk[3]);
    BlockGrid3D<T, POW>& set(int x, int y, int z, const T& data);
    BlockGrid3D<T, POW>& set(const Vec3i& ijk, const T& data);
    BlockGrid3D<T, POW>& set(const int ijk[3], const T& data);
    /**
     * @brief Read only. Thread safe.
     */
    const T& operator()(int x, int y, int z) const;
    const T& operator()(const Vec3i& ijk) const;
    const T& operator()(const int ijk[3]) const;

    /**
     * @brief Get a mutible reference at point. For maximum efficiency, this
     * function is does not check if block is allocated and *will segfault* if
     * not. This is is only used for range iterations.
     */
    T& refUnsafe(int i, int j, int k);
    T& refUnsafe(size_t bId, int inId);

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
    Vec3i idx2ijk(size_t bId, int inId) const;
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

    size_t blockId(int i, int j, int k) const;
    int inBlockId(int i, int j, int k) const;
    bool isActive(size_t bId, int inId) const;
    bool isActive(int i, int j, int k) const;

    const std::vector<size_t>& getActiveBlocks() const {
        return m_activeBlocks;
    }

    T* getBlock(size_t n) { return m_ptrToData[n]; }
    const T* getBlock(size_t n) const { return m_ptrToData[n]; }

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
    void initBlocks();

    T m_background;
    std::vector<std::unique_ptr<T[]>> m_ptrData;
    std::vector<size_t> m_activeBlocks;
    std::vector<T*> m_ptrToData;
    // std::vector<std::unique_ptr<BlockType>> m_data;
    int m_nBlocks;

    /// @brief Corners
    Vec3 m_startPos, m_endPos;

    Vec3i m_cellCount;  /// @brief Resolution (in cell count)
    Vec3i m_nodeCount;  /// @brief Resolution (in node count). *Always larger
                        /// than m_cellCount by 1*.
    Vec3i m_nodeCountActual;  /// @brief Physical node count. Always
                              /// dividible by 2^POW.
    Vec3i m_blockCount;       /// @brief Block count.
    Vec3 m_dx;                /// @brief Resolution (in spatial unit)
    Vec3 m_invDx;
};
/*
template <int POW, typename... Types>
void forEach(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    BlockGrid3D<Types, POW>&... grids
);

template <int POW, typename... Types>
void forEachSerial(
    const std::function<void(const Vec3i&, Types&...)>& callback,
    BlockGrid3D<Types, POW>&... grids
);

template <int POW, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i&                                                      lower,
    const Vec3i&                                                      upper,
    BlockGrid3D<Types, POW>&... grids
);

template <int POW, typename... Types>
void rangeWriteParallel(
    const std::function<void(const Vec3i&, const Vec3i&, Types&...)>& callback,
    const Vec3i&                                                      lower,
    const Vec3i&                                                      upper,
    BlockGrid3D<Types, POW>&... grids
);

template <int POW, typename... Types>
void rangeIter(
    const std::function<void(const Vec3i&, const Vec3i&, const Types&...)>&
                 callback,
    const Vec3i& lower,
    const Vec3i& upper,
    const BlockGrid3D<Types, POW>&... grids
);*/

}  // namespace Grid

#endif

#include "BlockGrid3d.cpp"
