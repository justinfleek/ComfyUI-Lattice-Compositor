#include "MeshLevelSet3d.hpp"
#include <iostream>

using namespace Type;

MeshLevelSet3D::MeshLevelSet3D(
    std::string filename, const Vec3i& resolution, const Vec3& translation
) {
    // Load mesh
    if (!std::ifstream(filename).good()) {
        throw std::runtime_error("Cannot find obj file: " + filename);
    }

    const bool success =
        igl::readOBJ(filename, m_meshVerticesEigen, m_meshTrianglesEigen);

    if (!success) {
        throw std::runtime_error("Error while reading obj: " + filename);
    }

    // Bounding grid in local frame
    Vec3 minCorner = m_meshVerticesEigen.colwise().minCoeff().cast<NumT>();
    Vec3 maxCorner = m_meshVerticesEigen.colwise().maxCoeff().cast<NumT>();
    Vec3 diff = maxCorner - minCorner;
    minCorner -= 0.25 * diff;
    maxCorner += 0.25 * diff;

    constexpr bool allowOOB = true;
    m_gSdf = Grid::MovingDenseGrid3D<float>(minCorner, maxCorner, resolution);

    // SDF in local frame
    computeSDF();

    // Translation
    displace(translation);
}

void MeshLevelSet3D::displace(const Vec3& disp) {
    // Update transform
    Eigen::Vector<float, 3> tr(disp[0], disp[1], disp[2]);
    // Transform vertices
    m_meshVerticesEigen.rowwise() += tr.transpose();
    // Update center of mass
    m_com = m_meshVerticesEigen.colwise().mean();

    // Update SDF
    m_gSdf.addTranslation(disp);
}

void MeshLevelSet3D::update(const NumT dt, const NumT t) {
    /////
}

void MeshLevelSet3D::computeSDF() {
    const Vec3i resolution = m_gSdf.getNodeRes();
    m_gSdf.setConst(1e12);

#pragma omp parallel
    {
        // Split indices for igl: good or not
        std::vector<Vec3i> cellIds;
#pragma omp for collapse(3)
        GRID_LOOP3_NP_IJK(i, j, k, resolution) {
            cellIds.emplace_back(Vec3i(i, j, k));
        }  // i, j, k

        // Positions to eval
        Eigen::Matrix<float, Eigen::Dynamic, 3> cellPos(cellIds.size(), 3);
        for (int i = 0; i < cellIds.size(); ++i) {
            cellPos.row(i) = m_gSdf.getIJKPos(cellIds[i]).cast<float>();
        }  // i
        // IGL evalation
        Eigen::Vector<float, Eigen::Dynamic> distances;
        Eigen::VectorXi trianglesId;
        Eigen::Matrix<float, Eigen::Dynamic, 3> closestPoints;
        Eigen::Matrix<float, Eigen::Dynamic, 3> distancesNormals;
        igl::signed_distance(
            cellPos, m_meshVerticesEigen, m_meshTrianglesEigen,
            igl::SignedDistanceType::SIGNED_DISTANCE_TYPE_PSEUDONORMAL,
            // igl::SignedDistanceType::SIGNED_DISTANCE_TYPE_WINDING_NUMBER,
            std::numeric_limits<float>::min(),
            std::numeric_limits<float>::max(), distances, trianglesId,
            closestPoints, distancesNormals
        );
        // Put back
        for (int i = 0; i < cellIds.size(); ++i) {
            m_gSdf(cellIds[i]) = static_cast<float>(distances(i));

        }  // i

    }  // omp parallel
}

const Eigen::Matrix<float, Eigen::Dynamic, 3, Eigen::RowMajor>&
MeshLevelSet3D::vertexData() const {
    return this->m_meshVerticesEigen;
}

const Eigen::Matrix<int, Eigen::Dynamic, 3, Eigen::RowMajor>&
MeshLevelSet3D::faceData() const {
    return m_meshTrianglesEigen;
}

NumT MeshLevelSet3D::interpolate(const Vec3& pos) const {
    NumT val = m_gSdf.interpolateCubic(pos);
    return val;
}

bool MeshLevelSet3D::isInside(const Vec3& pos) const {
    return (interpolate(pos) <= 0);
}
