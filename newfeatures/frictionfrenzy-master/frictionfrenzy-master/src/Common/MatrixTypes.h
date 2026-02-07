#ifndef __MATRIXTYPES_H__
#define __MATRIXTYPES_H__

#include <Eigen/Dense>
#include <Eigen/Geometry>
#include <Eigen/Sparse>

#include "Scalar.h"

namespace FrictionFrenzy {

typedef Eigen::SparseMatrix<Scalar, Eigen::RowMajor, int64_t> SparseMat;
typedef Eigen::Matrix<Scalar, -1, 1> VectorX;
typedef Eigen::Matrix<Scalar, 2, 1> Vector2;
typedef Eigen::Matrix<Scalar, 3, 1> Vector3;
typedef Eigen::Matrix<Scalar, 4, 1> Vector4;
typedef Eigen::Matrix<Scalar, 6, 1> Vector6;
typedef Eigen::Matrix<Scalar, 2, 2> Matrix2;
typedef Eigen::Matrix<Scalar, 3, 3> Matrix3;
typedef Eigen::Matrix<Scalar, 4, 4> Matrix4;
typedef Eigen::Matrix<Scalar, 6, 6> Matrix6;
typedef Eigen::Matrix<Scalar, -1, 3> MatrixX3;
typedef Eigen::Matrix<Scalar, -1, 2> MatrixX2;
typedef Eigen::Matrix<Scalar, 3, -1> Matrix3X;
typedef Eigen::Matrix<Scalar, -1, -1> MatrixX;
typedef Eigen::Matrix<int, -1, 1> VectorXi;
typedef Eigen::Matrix<int, 3, 1> Vector3i;
typedef Eigen::Matrix<int, -1, 3> MatrixX3i;
typedef Eigen::Matrix<int, -1, 3> MeshIndexMatrix;
typedef Eigen::Matrix<Scalar, -1, 3> MeshVertexMatrix;
typedef Eigen::Matrix<int, -1, -1> MatrixXi;
typedef Eigen::Transform<Scalar, 3, Eigen::Affine> Affine;
typedef Eigen::Transform<Scalar, 3, Eigen::Isometry> Isometry;
typedef Eigen::Quaternion<Scalar> Quaternion;
typedef Eigen::AngleAxis<Scalar> AngleAxis;

}  // namespace FrictionFrenzy

#endif
