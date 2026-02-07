#ifndef MAGNUM_UTILS_HPP
#define MAGNUM_UTILS_HPP

#include <Magnum/GL/Mesh.h>
#include <Magnum/Math/Color.h>
#include "Common/CustomTypes.hpp"
#include "Drawables/MagnumTypes.h"
#include "Grids/Grid.h"

namespace std {
/**
 * @brief << operator
 * @param os
 * @param vec
 * @return
 */
template <std::size_t size, class T>
std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector<size, T>& vec
);

/**
 * @brief << operator
 * @param os
 * @param vec
 * @return
 */
std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector2<Type::NumT>& vec
);

/**
 * @brief << operator
 * @param os
 * @param vec
 * @return
 */
std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector3<float>& vec
);
}  // namespace std

namespace Magnum {

Color3 hexToRgbf(unsigned long long hexColor);

Color4 hexToRgbaf(unsigned long long hexColor);

template <class T>
Magnum::GL::Mesh gridToGLMesh(const Grid::DenseGrid2D<T>& grid);
template <class T>
Magnum::GL::Mesh gridToGLMesh(const Grid::DenseGrid3D<T>& grid);

}  // namespace Magnum

#include "Drawables/MagnumUtils.tpp"

#endif  // MAGNUM_UTILS_HPP
