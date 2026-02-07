#ifndef MESH_LEVEL_SET_3D
#define MESH_LEVEL_SET_3D

#include <memory>
#include <utility>

#include "Common/CustomTypes.hpp"
#include "Common/Utils.hpp"
#include "Grids/Grid.h"

#include <igl/readOBJ.h>
#include <igl/signed_distance.h>
#include <Eigen/Geometry>

using namespace Type;

// #warning SPLIT_IN_MESH_AND_SDF

class MeshLevelSet3D {
public:
    /**
     * @brief Constructor
     * @param filename
     * @param resolution
     */
    MeshLevelSet3D(
        std::string filename, const Vec3i& resolution,
        const Vec3& translation = Vec3(0., 0., 0.)
    );

    /**
     * @brief
     * @return
     */
    virtual void displace(const Vec3& disp);

    /**
     * @brief
     */
    virtual void update(const NumT dt, const NumT t);

    /**
     * @brief
     */
    void computeSDF();

    /// Mesh data

    /**
     * @brief
     * @return
     */
    const Eigen::Matrix<float, Eigen::Dynamic, 3, Eigen::RowMajor>& vertexData(
    ) const;

    /**
     * @brief
     * @return
     */
    const Eigen::Matrix<int, Eigen::Dynamic, 3, Eigen::RowMajor>& faceData(
    ) const;

    /// SDF data

    /**
     * @brief
     * @param pos
     * @return max value if outside of bounding box
     */
    NumT interpolate(const Vec3& pos) const;

    /**
     * @brief
     * @param pos
     * @return
     */
    bool isInside(const Vec3& pos) const;

protected:
    /// @brief Mesh vertices
    Eigen::Matrix<float, Eigen::Dynamic, 3, Eigen::RowMajor>
        m_meshVerticesEigen;
    /// @brief Mesh vertices
    Eigen::Matrix<int, Eigen::Dynamic, 3, Eigen::RowMajor> m_meshTrianglesEigen;

    /// @brief SDF grid
    Grid::MovingDenseGrid3D<float> m_gSdf;

    /// @brief
    Eigen::Vector<float, 3> m_tr;
    /// @brief
    Eigen::Vector<float, 3> m_com;
    /// @brief
    Eigen::Transform<float, 3, Eigen::Affine> m_comRot;
};  // class

#endif  // MESH_LEVEL_SET_3D
