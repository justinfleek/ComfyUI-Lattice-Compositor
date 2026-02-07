#ifndef DENSE_GRID_2D_HPP
#define DENSE_GRID_2D_HPP

#include <vector>
#include "Common/CustomTypes.hpp"
#include "DenseGrid3d.hpp"

namespace Grid {

using namespace Type;

/**
 * @brief Axis-aligned grid
 */
template <class T>
class DenseGrid2D : public DenseGrid3D<T> {
public:
    /// Constructors
    /**
     * @brief Default
     */
    DenseGrid2D();
    /**
     * @brief Uniform spatial resolution
     */
    DenseGrid2D(
        Vec2 start, Vec2 end, NumT dx,
        bool allowOOB = false /*, bool is_tiled = false*/
    );
    /**
     * @brief Uniform grid resolution
     */
    DenseGrid2D(
        Vec2 start, Vec2 end, unsigned int res,
        bool allowOOB = false /*, bool is_tiled = false*/
    );

    /**
     * @brief Varying spatial resolution
     */
    DenseGrid2D(
        Vec2 start, Vec2 end, Vec2 dx,
        bool allowOOB = false /*, bool is_tiled = false*/
    );
    /**
     * @brief Varying grid resolution
     */
    DenseGrid2D(
        Vec2 start, Vec2 end, Vec2i res,
        bool allowOOB = false /*, bool is_tiled = false*/
    );

    /// Data
    /**
     * @brief Spatial resolution
     */
    Vec2 getDx() const;
    /**
     * @brief Grid resolution
     */
    Vec2i getCellRes() const;
    Vec2i getNodeRes() const;
    /**
     * @brief Corner
     */
    Vec2 getStartPos() const;
    /**
     * @brief Corner
     */
    Vec2 getEndPos() const;
    /**
     * @brief Mid
     */
    Vec2 getMidPos() const;

    /// Index operators
    /**
     * @brief 2D to 1D index
     */
    unsigned int ij2idx(int x, int y) const;
    /**
     * @brief 2D to 1D index
     */
    unsigned int ij2idx(Vec2i ij) const;

    /**
     * @brief 1D to 2D index
     */
    Vec2i idx2ij(unsigned int idx) const;

    /// Grid access operators
    /**
     * @brief Read and write
     */
    T& operator()(int x, int y);
    /**
     * @brief Read only
     */
    const T& operator()(int x, int y) const;
    /**
     * @brief Read and write
     */
    T& operator()(Vec2i ij);
    /**
     * @brief Read only
     */
    const T& operator()(Vec2i ij) const;

    /// OOB checks
    /**
     * @brief OOB per component
     */
    Vec2b boundFlags(int i, int j) const;
    /**
     * @brief OOB per component
     */
    Vec2b boundFlags(Vec2i ij) const;
    /**
     * @brief OOB
     */
    bool isIdValid(int i, int j) const;

    /// Position reads
    /**
     * @brief Index cell of the position
     */
    Vec2i pos2ij(const Vec2 pos);
    /**
     * @brief Value cell of the position
     */
    T& refAt(const Vec2 pos);
    /**
     * @brief Value cell of the position
     */
    const T& refAt(const Vec2 pos) const;
    /**
     * @brief Node world position
     */
    Vec2 getIJPos(int x, int y);
    /**
     * @brief Node world position
     */
    Vec2 getIJPos(Vec2i ij);
};
}  // namespace Grid

#include "DenseGrid2d.cpp"

#endif  // DENSE_GRID_2D_HPP
