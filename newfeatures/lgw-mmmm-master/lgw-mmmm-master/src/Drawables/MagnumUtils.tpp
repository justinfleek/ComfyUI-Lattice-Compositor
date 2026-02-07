#ifndef MAGNUM_UTILS_TPP
#define MAGNUM_UTILS_TPP

#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/GL/Buffer.h>
#include <Magnum/Magnum.h>
#include <Magnum/Math/Color.h>
#include <Magnum/Mesh.h>
#include <Magnum/Shaders/FlatGL.h>
#include <Magnum/Shaders/PhongGL.h>

namespace std {

template <std::size_t size, class T>
std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector<size, T>& vec
) {
    std::stringstream ss;
    ss << "(";
    for (int i = 0; i < size; ++i) {
        ss << vec[i];
        if (i != size - 1) {
            ss << ", ";
        }
    }
    ss << ")";
    os << ss.str();

    return os;
}

}  // namespace std

namespace Magnum {

template <class T>
Magnum::GL::Mesh gridToGLMesh(const Grid::DenseGrid2D<T>& grid) {
    std::vector<Vec2f> gridMesh;
    std::vector<Vec2ui> gridMeshIdx;
    const Vec2f startPos(grid.getStartPos()[0], grid.getStartPos()[1]);
    const Vec2f endPos(grid.getEndPos()[0], grid.getEndPos()[1]);
    const Vec2i res(grid.getCellRes()[0], grid.getCellRes()[1]);
    const Type::NumT dx = grid.getDx();
    for (int i = 0; i <= res.x(); ++i) {
        gridMesh.push_back({startPos.x() + i * dx, startPos.y()});
        gridMesh.push_back({startPos.x() + i * dx, endPos.y()});
        gridMeshIdx.emplace_back(i * 2, i * 2 + 1);
    }
    for (int i = 0; i <= res.y(); ++i) {
        gridMesh.push_back({startPos.x(), startPos.y() + i * dx});
        gridMesh.push_back({endPos.x(), startPos.y() + i * dx});
        gridMeshIdx.emplace_back(
            i * 2 + res.x() * 2 + 2, i * 2 + 3 + res.x() * 2
        );
    }
    Magnum::GL::Buffer vertexBuffer = Magnum::GL::Buffer{
        Corrade::Containers::ArrayView<const Vec2f>(
            gridMesh.data(), gridMesh.size()
        ),
        Magnum::GL::BufferUsage::StaticDraw};
    Magnum::GL::Buffer idxBuffer =
        Magnum::GL::Buffer{Corrade::Containers::ArrayView<const Vec2ui>(
            gridMeshIdx.data(), gridMeshIdx.size()
        )};

    Magnum::GL::Mesh gridMeshGL(Magnum::MeshPrimitive::Lines);
    gridMeshGL.setCount(gridMesh.size())
        .addVertexBuffer(
            std::move(vertexBuffer), 0, Magnum::Shaders::FlatGL2D::Position{}
        )
        .setIndexBuffer(
            std::move(idxBuffer), 0, Magnum::MeshIndexType::UnsignedInt
        );
    return gridMeshGL;
}

template <class T, int POW>
Magnum::GL::Mesh gridToGLMesh(const Grid::BlockGrid3D<T, POW>& grid) {
    std::vector<Vec3f> gridMesh;
    std::vector<Vec2ui> gridMeshIdx;
    const Vec3f startPos(
        grid.getStartPos()[0], grid.getStartPos()[1], grid.getStartPos()[2]
    );
    const Vec3f endPos(
        grid.getEndPos()[0], grid.getEndPos()[1], grid.getEndPos()[2]
    );
    const Vec3i res(
        grid.getCellRes()[0], grid.getCellRes()[1], grid.getCellRes()[2]
    );
    const Type::Vec3 dx = grid.getDx();
    for (int i = 0; i <= res.x(); ++i) {
        for (int j = 0; j <= res.y(); ++j) {
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y() + j * dx.y(),
                 startPos.z()}
            );
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y() + j * dx.y(),
                 endPos.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    for (int i = 0; i <= res.y(); ++i) {
        for (int j = 0; j <= res.z(); ++j) {
            gridMesh.push_back(
                {startPos.x(), startPos.y() + i * dx.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMesh.push_back(
                {endPos.x(), startPos.y() + i * dx.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    for (int i = 0; i <= res.x(); ++i) {
        for (int j = 0; j <= res.z(); ++j) {
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), endPos.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    Magnum::GL::Buffer vertexBuffer = Magnum::GL::Buffer{
        Corrade::Containers::ArrayView<const Vec3f>(
            gridMesh.data(), gridMesh.size()
        ),
        Magnum::GL::BufferUsage::StaticDraw};
    Magnum::GL::Buffer idxBuffer =
        Magnum::GL::Buffer{Corrade::Containers::ArrayView<const Vec2ui>(
            gridMeshIdx.data(), gridMeshIdx.size()
        )};

    Magnum::GL::Mesh gridMeshGL(Magnum::MeshPrimitive::Lines);
    gridMeshGL.setCount(gridMesh.size())
        .addVertexBuffer(
            std::move(vertexBuffer), 0, Magnum::Shaders::PhongGL::Position{}
        )
        .setIndexBuffer(
            std::move(idxBuffer), 0, Magnum::MeshIndexType::UnsignedInt
        );
    return gridMeshGL;
}

template <class T>
Magnum::GL::Mesh gridToGLMesh(const Grid::DenseGrid3D<T>& grid) {
    std::vector<Vec3f> gridMesh;
    std::vector<Vec2ui> gridMeshIdx;
    const Vec3f startPos(
        grid.getStartPos()[0], grid.getStartPos()[1], grid.getStartPos()[2]
    );
    const Vec3f endPos(
        grid.getEndPos()[0], grid.getEndPos()[1], grid.getEndPos()[2]
    );
    const Vec3i res(
        grid.getCellRes()[0], grid.getCellRes()[1], grid.getCellRes()[2]
    );
    const Type::Vec3 dx = grid.getDx();
    for (int i = 0; i <= res.x(); ++i) {
        for (int j = 0; j <= res.y(); ++j) {
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y() + j * dx.y(),
                 startPos.z()}
            );
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y() + j * dx.y(),
                 endPos.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    for (int i = 0; i <= res.y(); ++i) {
        for (int j = 0; j <= res.z(); ++j) {
            gridMesh.push_back(
                {startPos.x(), startPos.y() + i * dx.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMesh.push_back(
                {endPos.x(), startPos.y() + i * dx.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    for (int i = 0; i <= res.x(); ++i) {
        for (int j = 0; j <= res.z(); ++j) {
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), startPos.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMesh.push_back(
                {startPos.x() + i * dx.x(), endPos.y(),
                 startPos.z() + j * dx.z()}
            );
            gridMeshIdx.emplace_back(gridMesh.size() - 2, gridMesh.size() - 1);
        }
    }
    Magnum::GL::Buffer vertexBuffer = Magnum::GL::Buffer{
        Corrade::Containers::ArrayView<const Vec3f>(
            gridMesh.data(), gridMesh.size()
        ),
        Magnum::GL::BufferUsage::StaticDraw};
    Magnum::GL::Buffer idxBuffer =
        Magnum::GL::Buffer{Corrade::Containers::ArrayView<const Vec2ui>(
            gridMeshIdx.data(), gridMeshIdx.size()
        )};

    Magnum::GL::Mesh gridMeshGL(Magnum::MeshPrimitive::Lines);
    gridMeshGL.setCount(gridMesh.size())
        .addVertexBuffer(
            std::move(vertexBuffer), 0, Magnum::Shaders::PhongGL::Position{}
        )
        .setIndexBuffer(
            std::move(idxBuffer), 0, Magnum::MeshIndexType::UnsignedInt
        );
    return gridMeshGL;
}

}  // namespace Magnum

#endif  // MAGNUM_UTILS_TPP
