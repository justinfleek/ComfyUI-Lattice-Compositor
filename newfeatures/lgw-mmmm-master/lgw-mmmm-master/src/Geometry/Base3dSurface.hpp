#ifndef _BASE_3D_SURFACE_HPP
#define _BASE_3D_SURFACE_HPP

#include "Common/CustomTypes.hpp"
#include "Common/Utils.hpp"
#include "Geometry/marchingCube.hpp"
#include "Grids/Grid.h"
#include "Physics/MpmParams.hpp"

using namespace Type;

class Base3DSurface {
public:
    /**
     * @brief Constructor
     * @param gridParams
     */
    Base3DSurface(Params::Grid gridParams, Params::Surface surfParams);

    /**
     * @brief
     * @return
     */
    const Params::Grid& getGridParameters() const;
    /**
     * @brief
     * @return
     */
    const Params::Surface& getSurfParameters() const;

    /**
     * @brief  // Volume field must be computed before
     */
    virtual void compute(bool sdfFillAll = false);

    /**
     * @brief Approximate
     * @return
     */
    NumT getVolume() const;

    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<NumT>& getImplGrid() const;
    /**
     * @brief TMP - for external filling of the grid
     * @return
     */
    Grid::DenseGrid3D<NumT>& getImplGridNC();

    /**
     * @brief By triplets if no triangles indices
     * @return
     */
    const VectorVec3& getSurfacePos() const;
    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<VectorVec3>& getSurfacePosOnGrid() const;
    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<VectorI>& getSurfaceIdsOnGrid() const;

    /**
     * @brief
     * @return
     */
    const VectorUi& getTriangles() const;

    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<VectorI>& getTrianglesGrid() const;

    /**
     * @brief By triplets if no triangles indices
     * @return
     */
    void computeSurfaceNormals();

    /**
     * @brief By triplets if no trianglesIndices
     * @return
     */
    const VectorVec3& getSurfaceNormals() const;

    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<std::vector<Edge3D>>& getSurfaceSidesOnGrid() const;

    /**
     * @brief
     * @param
     * @return
     */
    bool isInside(const Vec3& pos) const;

    /**
     * @brief
     */
    void computeDistanceField();
    /**
     * @brief
     * @param
     * @return
     */
    NumT getSDF(const Vec3& xPos) const;
    /**
     * @brief Cubic interpolation
     * @param
     * @return
     */
    NumT getSDFCubic(const Vec3& xPos) const;
    /**
     * @brief
     * @return
     */
    const Grid::DenseGrid3D<NumT>& getSDFGrid() const;
    /**
     * @brief TMP
     */
    void computeImplicitSurfaceNoSoup();

protected:
    /**
     * @brief
     */
    void computeImplicitSurface();

    /// @brief Sim space
    const Params::Grid m_gridParams;
    /// @brief Surface tracking parameters
    const Params::Surface m_surfParams;

    /// @brief Grid for the implicit surface
    Grid::DenseGrid3D<NumT> m_gImpSurf;

    /// @brief Vertices of the implicit surface (read by triplet if no indices)
    VectorVec3 m_surfPos;
    /// @brief Grid also storing the vertices
    Grid::DenseGrid3D<VectorVec3> m_gSurfPos;
    /// @brief Remember where each vertex belonged
    Grid::DenseGrid3D<std::vector<Edge3D>> m_gSurfPosEdge;
    /// @brief Remember where each vertex belonged
    Grid::DenseGrid3D<VectorI> m_gSurfIndex;

    /// @brief Normals of the implicit surface (read by triplet if no indices)
    VectorVec3 m_surfNormals;

    /// @brief Triangles indices
    VectorUi m_triangles;
    /// @brief Triangles indices on grid
    Grid::DenseGrid3D<VectorI> m_gTriangles;

    /// @brief Upper bound
    const NumT m_distUp;
};  // class Base2DSurface

#endif  //_BASE_2D_SURFACE_HPP
