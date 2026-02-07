#ifndef MOVING_DENSE_GRID_3D_TPP
#define MOVING_DENSE_GRID_3D_TPP

#include "MovingDenseGrid3d.hpp"

#include <cassert>
#include <iostream>

#include "Common/Utils.hpp"

namespace Grid {

template <class T>
MovingDenseGrid3D<T>::MovingDenseGrid3D() : DenseGrid3D<T>::DenseGrid3D() {}

template <class T>
MovingDenseGrid3D<T>::MovingDenseGrid3D(Vec3 start, Vec3 end, NumT dx)

    : DenseGrid3D<T>::DenseGrid3D(start, end, dx),
      m_startPosInitial(start),
      m_endPosInitial(end) {}

template <class T>
MovingDenseGrid3D<T>::MovingDenseGrid3D(Vec3 start, Vec3 end, unsigned int res)
    : DenseGrid3D<T>::DenseGrid3D(start, end, res),
      m_startPosInitial(start),
      m_endPosInitial(end) {}

template <class T>
MovingDenseGrid3D<T>::MovingDenseGrid3D(Vec3 start, Vec3 end, Vec3 dx)
    : DenseGrid3D<T>::DenseGrid3D(start, end, dx),
      m_startPosInitial(start),
      m_endPosInitial(end) {}

template <class T>
MovingDenseGrid3D<T>::MovingDenseGrid3D(Vec3 start, Vec3 end, Vec3i res)
    : DenseGrid3D<T>::DenseGrid3D(start, end, res),
      m_startPosInitial(start),
      m_endPosInitial(end) {}

template <class T>
void MovingDenseGrid3D<T>::addTranslation(const Vec3& tr) {
    m_translation += tr;
    this->m_startPos += tr;
    this->m_endPos += tr;
}

}  // namespace Grid

#endif  // MOVING_DENSE_GRID_3D_TPP
