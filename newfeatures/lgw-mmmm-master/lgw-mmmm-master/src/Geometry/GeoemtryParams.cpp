#include "Geometry/MeshLevelSet3d.hpp"
#include "GeometryParams.hpp"

namespace Params {
VolumeCuboid::VolumeCuboid(
    const Type::Vec3& minCorner, const Type::Vec3& maxCorner,
    const Type::Vec3i& resolution
)
    : Volume::Volume(),
      center(0.5 * (minCorner + maxCorner)),
      diagonal(0.5 * (maxCorner - minCorner)) {
    this->resolution = resolution;
}

void VolumeCuboid::fillGrid(::Grid::DenseGrid3D<NumT>& sdfGrid) const {
    const Vec3i gr = sdfGrid.getNodeRes();

    // https://iquilezles.org/articles/distfunctions/
    ::Grid::forEach(
        std::function([this, &sdfGrid](const Vec3i& ijk, NumT& sdf) {
            const Type::Vec3 nPos = sdfGrid.getIJKPos(ijk);
            const Type::Vec3 p(
                std::fabs(nPos[0] - this->center[0]),
                std::fabs(nPos[1] - this->center[1]),
                std::fabs(nPos[2] - this->center[2])
            );
            const Type::Vec3 q = p - this->diagonal;
            const Type::NumT sd =
                sqrt(
                    std::pow(std::max(0.0, q[0]), 2) +
                    std::pow(std::max(0.0, q[1]), 2) +
                    std::pow(std::max(0.0, q[2]), 2)
                ) +
                std::min(std::max(q[0], std::max(q[1], q[2])), 0.0);
            sdf = std::min(sdf, sd);
        }),
        sdfGrid
    );
}

Params::Grid VolumeCuboid::calculateGridParameters() const {
    Params::Grid ret;
    ret.gridStart = center - diagonal;
    ret.gridEnd = center + diagonal;
    ret.gridResolution = resolution;
    return ret;
}

VolumeMesh::VolumeMesh(
    const std::string& filename, const Type::Vec3i& resolution,
    const Type::Vec3& offset
)
    : Volume::Volume(), filename(filename), offset(offset) {
    this->resolution = resolution;
}

void VolumeMesh::fillGrid(::Grid::DenseGrid3D<NumT>& sdfGrid) const {
    const Vec3i gr = sdfGrid.getNodeRes();
    MeshLevelSet3D initObj(filename, resolution, offset);
    ::Grid::forEach(
        std::function([&sdfGrid, &initObj](const Vec3i& ijk, NumT& sdf) {
            const Type::Vec3 pos = sdfGrid.getIJKPos(ijk);
            const Type::NumT sd = initObj.interpolate(pos);
            sdf = std::min(sdf, sd);
        }),
        sdfGrid
    );
}

Params::Grid VolumeMesh::calculateGridParameters() const {
    Params::Grid ret;
    Eigen::MatrixX3d vertices;
    Eigen::MatrixX3i triangles;
    const bool success = igl::readOBJ(filename, vertices, triangles);

    if (!success) {
        throw std::runtime_error("Error while reading obj: " + filename);
    }

    Vec3 minCorner = vertices.colwise().minCoeff().cast<NumT>();
    Vec3 maxCorner = vertices.colwise().maxCoeff().cast<NumT>();
    ret.gridStart = minCorner + offset;
    ret.gridEnd = maxCorner + offset;
    ret.gridResolution = resolution;
    return ret;
}
ObstacleMesh::ObstacleMesh(
    const std::string& filename,
    // const std::string& PhysicsFile,
    const Type::Vec3i& resolution, const Type::Vec3& offset,
    const Type::Vec3& velocity, const Type::Vec3& angVel,
    const Type::NumT density
)
    : VolumeMesh::VolumeMesh(filename, resolution, offset),
      velocity(velocity),
      angVel(angVel),
      density(density) {}

}  // namespace Params
