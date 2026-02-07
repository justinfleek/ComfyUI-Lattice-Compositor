#ifndef MOVING_DENSE_GRID_3D_HPP
#define MOVING_DENSE_GRID_3D_HPP

#include "DenseGrid3d.hpp"

namespace Grid {

using namespace Type;

/**
 * @brief Moving grid
 */

template <class T>
class MovingDenseGrid3D : public DenseGrid3D<T> {
public:
    /// Constructors

    /**
     * @brief Default
     */
    MovingDenseGrid3D();

    /**
     * @brief Uniform spatial resolution
     */
    MovingDenseGrid3D(Vec3 start, Vec3 end, NumT dx);
    /**
     * @brief Uniform grid resolution
     */
    MovingDenseGrid3D(Vec3 start, Vec3 end, unsigned int res);

    /**
     * @brief Varying spatial resolution
     */
    MovingDenseGrid3D(Vec3 start, Vec3 end, Vec3 dx);
    /**
     * @brief Varying grid resolution
     */
    MovingDenseGrid3D(Vec3 start, Vec3 end, Vec3i res);

    /// Control
    /**
     * @brief Translation
     */
    void addTranslation(const Vec3& tr);

protected:
    /// @brief Corners
    Vec3 m_startPosInitial;
    Vec3 m_endPosInitial;

    /// DoFs
    Vec3 m_translation{0., 0., 0.};

};  // class MovingDenseGrid3d

}  // namespace Grid

#include "MovingDenseGrid3d.cpp"

#endif  // MOVING_DENSE_GRID_3D_HPP
