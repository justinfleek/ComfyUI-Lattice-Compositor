#include "Mesh.h"

#include <Eigen/src/Core/Matrix.h>
#include <Eigen/src/Geometry/AlignedBox.h>

#include "Common/DisableStupidWarnings.h"

#include <igl/barycentric_coordinates.h>
#include <igl/per_edge_normals.h>
#include <igl/per_face_normals.h>
#include <igl/per_vertex_normals.h>
#include <igl/project_to_line_segment.h>
#include <igl/signed_distance.h>

#include "Common/ReenableStupidWarnings.h"

#include <limits>
#include <memory>
#include <vector>
#include "CollisionObject/RigidObjectBase.h"
#include "Common/MatrixTypes.h"
#include "Discregrid/cubic_lagrange_discrete_grid.hpp"
#include "Discregrid/discrete_grid.hpp"

namespace FrictionFrenzy {
namespace CollisionObject {
void Mesh::initializeFCLObject() {
    // Extract all transformations and transformed vertices.
    Affine               scaled;
    Isometry             rigid;
    Scalar               vol;
    std::vector<Vector3> transVertices;
    preprocessMesh(rigid, scaled, transVertices, vol);

    // Construct triangles for the FCL structure.
    std::vector<fcl::Triangle> indices;
    const MatrixX3i&           indicesEigen = *(mp_mesh->indices_Eigen);
    for (int i = 0; i < indicesEigen.rows(); ++i) {
        Vector3i tri = indicesEigen.row(i).transpose();
        indices.emplace_back(tri[0], tri[1], tri[2]);
    }

    // Construct the FCL BVH model.
    mp_geo    = std::make_shared<BVH>();
    auto* bvh = dynamic_cast<BVH*>(mp_geo.get());
    bvh->beginModel();
    bvh->addSubModel(transVertices, indices);
    bvh->endModel();

    // Calculate the face areas;
    std::vector<Scalar> faceAreas;
    faceAreas.reserve(indicesEigen.rows());
    for (int i = 0; i < indicesEigen.rows(); ++i) {
        Vector3 v1 =
            (transVertices[indicesEigen(i, 1)] -
             transVertices[indicesEigen(i, 0)]);
        Vector3 v2 =
            (transVertices[indicesEigen(i, 2)] -
             transVertices[indicesEigen(i, 0)]);
        faceAreas.push_back(0.5 * v1.cross(v2).norm());
    }

    // Construct SDF query structure
    mp_sdfQuery = std::make_shared<SDFQueryStruct>();
    mp_sdfQuery->transformedPositions.resize(transVertices.size(), 3);
    for (size_t i = 0; i < transVertices.size(); ++i) {
        mp_sdfQuery->transformedPositions.row(i) << transVertices[i].transpose();
    }
    mp_sdfQuery->p_indices = mp_mesh->indices_Eigen;
    const MatrixX3&  V    = mp_sdfQuery->transformedPositions;
    const MatrixX3i& F    = *(mp_sdfQuery->p_indices.lock());
    Eigen::MatrixX2i E;
    mp_sdfQuery->aabbTree.init(V, F);
    igl::per_face_normals(V, F, mp_sdfQuery->faceNormals);
    igl::per_vertex_normals(
        V, F, igl::PER_VERTEX_NORMALS_WEIGHTING_TYPE_ANGLE,
        mp_sdfQuery->faceNormals, mp_sdfQuery->vertNormals
    );
    igl::per_edge_normals(
        V, F, igl::PER_EDGE_NORMALS_WEIGHTING_TYPE_UNIFORM,
        mp_sdfQuery->faceNormals, mp_sdfQuery->edgeNormals, E, mp_sdfQuery->edgeMap
    );

    // Construct vertex adjacency map
    std::vector<std::vector<int>> adjMap_Inner(V.rows());
    for (int i = 0; i < F.rows(); ++i) {
        for (int v0 = 0; v0 < 3; ++v0) {
            for (int v1 = v0 + 1; v1 < 3; ++v1) {
                adjMap_Inner[v0].push_back(v1);
                adjMap_Inner[v1].push_back(v0);
            }
        }
    }

    auto&  adjMap  = mp_sdfQuery->vertAdjMap;
    size_t mapSize = V.rows();
    for (size_t i = 0; i < adjMap_Inner.size(); ++i) {
        mapSize += adjMap_Inner[i].size();
    }
    adjMap.reserve(V.rows() + 1 + mapSize);
    adjMap.resize(V.rows() + 1);
    for (int i = 0; i < V.rows(); ++i) {
        size_t dataOffset = adjMap.size();
        adjMap[i]         = dataOffset;
        adjMap.insert(
            adjMap.end(), adjMap_Inner[i].begin(), adjMap_Inner[i].end()
        );
    }
    adjMap[V.rows()] = adjMap.size();

    // Calculate vertex areas
    mp_sdfQuery->vertArea.resize(V.rows());
    mp_sdfQuery->vertArea.setZero();
    for (int i = 0; i < F.rows(); ++i) {
        for (int j = 0; j < 3; ++j) {
            mp_sdfQuery->vertArea(F(i, j)) += faceAreas[i];
        }
    }
    mp_sdfQuery->vertArea /= 3;

    m_dist2 = 0;
    for (int i = 0; i < F.rows(); ++i) {
        Vector3 v0   = transVertices[F(i, 0)];
        Vector3 v1   = transVertices[F(i, 1)];
        Vector3 v2   = transVertices[F(i, 2)];
        Scalar  V    = v0.dot(v1.cross(v2));
        Scalar  dots = v0.dot(v0) + v0.dot(v1) + v0.dot(v2) + v1.dot(v1) +
                      v1.dot(v2) + v2.dot(v2);
        m_dist2 += dots * V;
    }
    m_dist2 /= 60;

    // Construct Discregrid domain
    if (m_sdfDims > 0) {
        Eigen::AlignedBox3d sdfDomain;
        for (auto v : transVertices) {
            sdfDomain.extend(v);
        }
        sdfDomain.max().array() += 1e-3 * sdfDomain.diagonal().norm();
        sdfDomain.min().array() -= 1e-3 * sdfDomain.diagonal().norm();
        std::array<unsigned int, 3> sdfDims;
        Scalar                      maxSide = sdfDomain.sizes().maxCoeff();
#pragma omp unroll
        for (int i = 0; i < 3; ++i) {
            sdfDims[i] = std::ceil(sdfDomain.sizes()[i] / maxSide * m_sdfDims);
        }
        mp_discregrid = std::make_shared<Discregrid::CubicLagrangeDiscreteGrid>(
            sdfDomain, sdfDims
        );
        Discregrid::DiscreteGrid::ContinuousFunction func = [&](Vector3 const& x
                                                            ) {
            Scalar                    distSign, dist2;
            Vector3                   n;
            Eigen::RowVector3<Scalar> cT;
            int                       idx;
            igl::signed_distance_pseudonormal(
                mp_sdfQuery->aabbTree, mp_sdfQuery->transformedPositions,
                *(mp_sdfQuery->p_indices.lock()), mp_sdfQuery->faceNormals,
                mp_sdfQuery->vertNormals, mp_sdfQuery->edgeNormals,
                mp_sdfQuery->edgeMap, x.transpose(), distSign, dist2, idx, cT, n
            );
            return distSign * std::sqrt(dist2);
        };
        m_discSDFId = mp_discregrid->addFunction(func);

        // Delete unused structures to save space
        mp_sdfQuery->aabbTree.clear();
        mp_sdfQuery->edgeMap.resize(0);
        mp_sdfQuery->edgeNormals.resize(0, 3);
        mp_sdfQuery->faceNormals.resize(0, 3);
    }

    initializeConfig(rigid, scaled, scaled);
}

Scalar Mesh::obbMinLength() const {
    // Construct OBB around mesh with SVD and return the shortest length.
    auto*    bvh   = dynamic_cast<BVH*>(mp_geo.get());
    Vector3* verts = bvh->vertices;
    Vector3  com   = bvh->computeCOM();
    Matrix3X vToCOM(3, bvh->num_vertices);
    for (int i = 0; i < bvh->num_vertices; ++i) {
        vToCOM.col(i) << verts[i] - com;
    }
    Matrix3 pcaMat = vToCOM * vToCOM.transpose() / bvh->num_vertices;
    Eigen::JacobiSVD<Matrix3, Eigen::ComputeFullU> svd(
        pcaMat, Eigen::ComputeFullU
    );
    Matrix3  uT         = svd.matrixU().transpose();
    Matrix3X localVerts = uT * vToCOM;
    Vector3  boxSize =
        localVerts.rowwise().maxCoeff() - localVerts.rowwise().minCoeff();
    return boxSize.minCoeff();
}
std::pair<Scalar, Vector3> Mesh::signedDistance(Eigen::Ref<const Vector3> q
) const {
    // Convert q to local coordinates.
    Isometry trans    = this->getRigidTransMatrix();
    Isometry invTrans = trans.inverse();
    Vector3  localQ   = (invTrans * q.homogeneous()).head(3);

    if (mp_discregrid) {
        Vector3 nDisc;
        Scalar  value = mp_discregrid->interpolate(m_discSDFId, localQ, &nDisc);
        return {value, trans.linear() * nDisc};
    } else {
        // Calculate the signed distance.
        Scalar                    distSign, dist2;
        Vector3                   n;
        Eigen::RowVector3<Scalar> cT;
        int                       idx;
        igl::signed_distance_pseudonormal(
            mp_sdfQuery->aabbTree, mp_sdfQuery->transformedPositions,
            *(mp_sdfQuery->p_indices.lock()), mp_sdfQuery->faceNormals,
            mp_sdfQuery->vertNormals, mp_sdfQuery->edgeNormals,
            mp_sdfQuery->edgeMap, localQ.transpose(), distSign, dist2, idx, cT, n
        );
        Scalar signedDist = distSign * std::sqrt(dist2);

        // Find barycentric coordinates of the closest point to q on the mesh.
        const MatrixX3&        V    = mp_sdfQuery->transformedPositions;
        const MatrixX3i&       F    = *(mp_sdfQuery->p_indices.lock());
        std::array<int, 3>     vidx = {F(idx, 0), F(idx, 1), F(idx, 2)};
        std::array<Vector3, 3> v    = {
               V.row(vidx[0]).transpose(), V.row(vidx[1]).transpose(),
               V.row(vidx[2]).transpose()};
        Eigen::RowVector3<Scalar> barCoor;
        igl::barycentric_coordinates(
            cT, v[0].transpose(), v[1].transpose(), v[2].transpose(), barCoor
        );

        // Recalculate signed-distance gradient n by interpolating from the
        // vertex normals on the closest surface.
        Matrix3 vNormals;
        vNormals << mp_sdfQuery->vertNormals.row(vidx[0]).transpose(),
            mp_sdfQuery->vertNormals.row(vidx[1]).transpose(),
            mp_sdfQuery->vertNormals.row(vidx[2]).transpose();
        n = vNormals * barCoor.transpose();
        n.normalize();

        // Convert n to global space.
        n = trans.linear() * n;
        return {signedDist, n};
    }
}
igl::Hit Mesh::rayIntersection(
    Eigen::Ref<const Vector3> o,
    Eigen::Ref<const Vector3> ray
) const {
    // Convert o and ray to local coordinates.
    Isometry invTrans = getRigidTransMatrix().inverse();
    Vector3  localO   = (invTrans * o.homogeneous()).head(3);
    Vector3  localRay = invTrans.linear() * ray;

    // Call libIGL ray intersection routine.
    igl::Hit         hit;
    const MatrixX3&  V      = mp_sdfQuery->transformedPositions;
    const MatrixX3i& F      = *(mp_sdfQuery->p_indices.lock());
    bool             didHit = mp_sdfQuery->aabbTree.intersect_ray(
                    V, F, localO.transpose(), localRay.transpose(), hit
                );
    if (!didHit) {
        hit.t = std::numeric_limits<Scalar>::infinity();
    }
    return hit;
}

std::string Mesh::toString() const {
    std::stringstream ss;
    ss << "Type: mesh\n"
       << getVertCount() << " vertices\n"
       << getIndexCount() << " triangles\n"
       << RigidObjectBase::toString();
    return ss.str();
}
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
