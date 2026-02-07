#ifndef CUSTOM_TYPES_HPP
#define CUSTOM_TYPES_HPP

#include <Eigen/Dense>
// #include <Eigen/LU>
// #include <Eigen/Geometry>

#include <array>
#include <vector>

#include <memory>  // shared_ptr

// Simulation types
namespace Type {

// Typedefs with varying num type
typedef double NumT;

// Vectors and matrices types
using Vec2 = Eigen::Matrix<NumT, 2, 1>;
using Mat2 = Eigen::Matrix<NumT, 2, 2>;
using Vec2i = Eigen::Matrix<int, 2, 1>;
using Vec2ui = Eigen::Matrix<unsigned, 2, 1>;
using Vec2f = Eigen::Matrix<float, 2, 1>;
using Vec2b = std::array<bool, 2>;

using Vec3 = Eigen::Matrix<NumT, 3, 1>;
using Mat3 = Eigen::Matrix<NumT, 3, 3>;
using Vec3i = Eigen::Matrix<int, 3, 1>;
using Vec3ui = Eigen::Matrix<unsigned, 3, 1>;
using Vec3f = Eigen::Matrix<float, 3, 1>;
using Vec3b = std::array<bool, 3>;

using Vec4 = Eigen::Matrix<NumT, 4, 1>;
using Mat4 = Eigen::Matrix<NumT, 4, 4>;
using Vec4i = Eigen::Matrix<int, 4, 1>;
using Vec4ui = Eigen::Matrix<unsigned, 4, 1>;
using Vec4f = Eigen::Matrix<float, 4, 1>;

// Constants
inline Vec2 const Zero2 = Vec2::Zero();
inline Mat2 const Zero2x2 = Mat2::Zero();
inline Mat2 const Id2x2 = Mat2::Identity();
inline Vec2f const Zero2f = Vec2f::Zero();
inline Vec2i const Zero2i = Vec2i::Zero();

inline Vec3 const Zero3 = Vec3::Zero();
inline Mat3 const Zero3x3 = Mat3::Zero();
inline Mat3 const Id3x3 = Mat3::Identity();
inline Vec3f const Zero3f = Vec3f::Zero();
inline Vec3i const Zero3i = Vec3i::Zero();

inline Vec4 const Zero4 = Vec4::Zero();
inline Mat4 const Zero4x4 = Mat4::Zero();
inline Mat4 const Id4x4 = Mat4::Identity();
inline Vec4f const Zero4f = Vec4f::Zero();
inline Vec4i const Zero4i = Vec4i::Zero();

// Vectors
using VectorUi = std::vector<unsigned int>;
using VectorI = std::vector<int>;
using VectorD = std::vector<double>;
using VectorNumT = std::vector<NumT>;
using VectorVec2 = std::vector<Vec2>;
using VectorMat2 = std::vector<Mat2>;
using VectorVec2i = std::vector<Vec2i>;
using VectorVec2f = std::vector<Vec2f>;
using VectorVec3 = std::vector<Vec3>;
using VectorVec3f = std::vector<Vec3f>;
using VectorVec3i = std::vector<Vec3i>;
using VectorVec3ui = std::vector<Vec3ui>;
using VectorMat3 = std::vector<Mat3>;
using VectorVec4 = std::vector<Vec4>;

// "Matrices"
using Vector2NumT = std::vector<std::vector<NumT>>;
using Vector2Vec2 = std::vector<std::vector<Vec2>>;
using Vector2Mat2 = std::vector<std::vector<Mat2>>;
using Vector2Vec2i = std::vector<std::vector<Vec2i>>;
using Vector2Vec3 = std::vector<std::vector<Vec3>>;

// Matrices

// Shared ptrs
using VectorNumTPtr = std::shared_ptr<std::vector<NumT>>;
using VectorVec2Ptr = std::shared_ptr<std::vector<Vec2>>;
using VectorMat2Ptr = std::shared_ptr<std::vector<Mat2>>;
using VectorVec2iPtr = std::shared_ptr<std::vector<Vec2i>>;
using VectorVec3Ptr = std::shared_ptr<std::vector<Vec3>>;
using VectorVec3iPtr = std::shared_ptr<std::vector<Vec3i>>;
using VectorMat3Ptr = std::shared_ptr<std::vector<Mat3>>;

}  // namespace Type

#endif  // CUSTOM_TYPES_HPP
