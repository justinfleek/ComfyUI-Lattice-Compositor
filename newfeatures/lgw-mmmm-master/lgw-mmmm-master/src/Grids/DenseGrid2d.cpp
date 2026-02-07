#ifndef DENSE_GRID_2D_TPP
#define DENSE_GRID_2D_TPP

#include "DenseGrid2d.hpp"

#include <cassert>
#include <iostream>

#include "Common/Utils.hpp"

namespace Grid {

template <class T>
DenseGrid2D<T>::DenseGrid2D() : DenseGrid3D<T>() {}

template <class T>
DenseGrid2D<T>::DenseGrid2D(
    Vec2 start, Vec2 end, NumT dx, bool allowOOB /*, bool is_tiled*/
)
    : DenseGrid3D<T>(
          Vec3{start[0], start[1], 0}, Vec3{end[0], end[1], 0}, dx, allowOOB
      ) {}

template <class T>
DenseGrid2D<T>::DenseGrid2D(
    Vec2 start, Vec2 end, unsigned int res, bool allowOOB /*, bool is_tiled*/
)
    : DenseGrid3D<T>(
          Vec3{start[0], start[1], 0}, Vec3{end[0], end[1], 0}, res, allowOOB
      ) {}

template <class T>
DenseGrid2D<T>::DenseGrid2D(
    Vec2 start, Vec2 end, Vec2 dx, bool allowOOB /*, bool is_tiled*/
)
    : DenseGrid3D<T>(
          Vec3{start[0], start[1], 0}, Vec3{end[0], end[1], 0},
          Vec3(dx[0], dx[1], 0.), allowOOB
      ) {}

template <class T>
DenseGrid2D<T>::DenseGrid2D(
    Vec2 start, Vec2 end, Vec2i res, bool allowOOB /*, bool is_tiled*/
)
    : DenseGrid3D<T>(
          Vec3{start[0], start[1], 0}, Vec3{end[0], end[1], 0},
          Vec3i(res[0], res[1], 0), allowOOB
      ) {}

template <class T>
Vec2 DenseGrid2D<T>::getDx() const {
    return Vec2(DenseGrid3D<T>::m_dx[0], DenseGrid3D<T>::m_dx[1]);
}

template <class T>
Vec2i DenseGrid2D<T>::getCellRes() const {
    return Vec2(DenseGrid3D<T>::m_cellCount[0], DenseGrid3D<T>::m_cellCount[1]);
}

template <class T>
Vec2i DenseGrid2D<T>::getNodeRes() const {
    return Vec2(DenseGrid3D<T>::m_nodeCount[0], DenseGrid3D<T>::m_nodeCount[1]);
}

template <class T>
Vec2 DenseGrid2D<T>::getStartPos() const {
    return Vec2(DenseGrid3D<T>::m_startPos[0], DenseGrid3D<T>::m_startPos[1]);
}

template <class T>
Vec2 DenseGrid2D<T>::getEndPos() const {
    return Vec2(DenseGrid3D<T>::m_endPos[0], DenseGrid3D<T>::m_endPos[1]);
}

template <class T>
Vec2 DenseGrid2D<T>::getMidPos() const {
    return (this->getStartPos() + this->getEndPos()) / 2.;
}

template <class T>
unsigned int DenseGrid2D<T>::ij2idx(int x, int y) const {
    return this->ijk2idx(x, y, 0);
}

template <class T>
unsigned int DenseGrid2D<T>::ij2idx(Vec2i ij) const {
    return this->ijk2idx(Vec3i{ij, 0});
}

template <class T>
Vec2i DenseGrid2D<T>::idx2ij(unsigned int idx) const {
    Vec3i ijk = this->idx2ijk(idx);
    return Vec2i{ijk[0], ijk[1]};
}

template <class T>
T& DenseGrid2D<T>::operator()(int x, int y) {
    return DenseGrid3D<T>::operator()(x, y, 0);
}

template <class T>
const T& DenseGrid2D<T>::operator()(int x, int y) const {
    return DenseGrid3D<T>::operator()(x, y, 0);
}

template <class T>
T& DenseGrid2D<T>::operator()(Vec2i ij) {
    return DenseGrid3D<T>::operator()(Vec3i{ij[0], ij[1], 0});
}

template <class T>
const T& DenseGrid2D<T>::operator()(Vec2i ij) const {
    return DenseGrid3D<T>::operator()(Vec3i{ij[0], ij[1], 0});
}

template <class T>
Vec2b DenseGrid2D<T>::boundFlags(int i, int j) const {
    Vec2b res{0, 0};
    res[0] = (i < 0) ? -1 : (i >= this->m_nodeCount[0]) ? 1 : 0;
    res[1] = (j < 0) ? -1 : (j >= this->m_nodeCount[1]) ? 1 : 0;
    return res;
}
template <class T>
Vec2b DenseGrid2D<T>::boundFlags(Vec2i ij) const {
    return boundFlags(ij[0], ij[1]);
}
template <class T>
bool DenseGrid2D<T>::isIdValid(int i, int j) const {
    return DenseGrid3D<T>::isIdValid(i, j, 0);
}

template <class T>
Vec2i DenseGrid2D<T>::pos2ij(const Vec2 pos) {
    Vec3i ijk = this->pos2ijk(Vec3{pos[0], pos[1], 0});
    return Vec2i{ijk[0], ijk[1]};
}

template <class T>
T& DenseGrid2D<T>::refAt(const Vec2 pos) {
    return DenseGrid3D<T>::refAt(Vec3{pos[0], pos[1], 0});
}

template <class T>
const T& DenseGrid2D<T>::refAt(const Vec2 pos) const {
    return this->refAt(Vec3{pos, 0});
}

template <class T>
Vec2 DenseGrid2D<T>::getIJPos(int x, int y) {
    Vec2i realIJ = this->idx2ij(this->ij2idx(x, y));
    return Vec2(
        realIJ[0] * this->m_dx[0] + this->m_startPos[0],
        realIJ[1] * this->m_dx[1] + this->m_startPos[1]
    );
}
template <class T>
Vec2 DenseGrid2D<T>::getIJPos(Vec2i ij) {
    return getIJPos(ij.x(), ij.y());
}

}  // namespace Grid

#endif  // DENSE_GRID_2D_TPP
