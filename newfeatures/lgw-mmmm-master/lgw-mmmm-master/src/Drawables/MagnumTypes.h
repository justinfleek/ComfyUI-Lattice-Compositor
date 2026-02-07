#ifndef __MAGNUMTYPES_H__
#define __MAGNUMTYPES_H__

#include "Common/CustomTypes.hpp"

#include <Magnum/Magnum.h>
#include <Magnum/Math/Matrix.h>
#include <Magnum/Math/Tags.h>  // ZeroInit
#include <Magnum/Math/Vector.h>
#include <Magnum/Math/Vector2.h>
#include <Magnum/Math/Vector3.h>

#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/MatrixTransformation3D.h>
#include <Magnum/SceneGraph/Scene.h>

#include <Corrade/Containers/ArrayView.h>

#include <Magnum/Math/Color.h>

namespace Magnum {

// For rendering only
// Vectors and matrices types
using Vec2 = Magnum::Math::Vector2<Magnum::Float>;
using Mat2 = Magnum::Math::Matrix2x2<Magnum::Float>;
using Vec2i = Magnum::Vector2i;
using Vec2ui = Magnum::Vector2ui;
using Vec2f = Magnum::Math::Vector2<float>;

using Vec3 = Magnum::Math::Vector3<Magnum::Float>;
using Mat3 = Magnum::Math::Matrix3x3<Magnum::Float>;
using Vec3i = Magnum::Vector3i;
using Vec3ui = Magnum::Vector3ui;
using Vec3f = Magnum::Math::Vector3<float>;

using Vec4 = Magnum::Math::Vector4<Magnum::Float>;
using Mat4 = Magnum::Math::Matrix4x4<Magnum::Float>;
using Vec4i = Magnum::Vector4i;
using Vec4ui = Magnum::Vector4ui;
using Vec4f = Magnum::Math::Vector4<float>;

// Constants
inline Vec2 const Zero2 = Vec2(Magnum::Math::ZeroInit);
inline Mat2 const Zero2x2 = Mat2(Magnum::Math::ZeroInit);
inline Mat2 const Id2x2 = Mat2(Magnum::Math::IdentityInit);

inline Vec3 const Zero3 = Vec3(Magnum::Math::ZeroInit);
inline Mat3 const Zero3x3 = Mat3(Magnum::Math::ZeroInit);
inline Mat3 const Id3x3 = Mat3(Magnum::Math::IdentityInit);

inline Mat4 const Id4x4 = Mat4(Magnum::Math::IdentityInit);

// Vectors
using VectorUi = std::vector<unsigned int>;
using VectorI = std::vector<int>;
using VectorVec2 = std::vector<Vec2>;
using VectorMat2 = std::vector<Mat2>;
using VectorVec2i = std::vector<Vec2i>;
using VectorVec3 = std::vector<Vec3>;
using VectorVec3i = std::vector<Vec3i>;
using VectorVec3ui = std::vector<Vec3ui>;
using VectorMat3 = std::vector<Mat3>;
using VectorVec4 = std::vector<Vec4>;

// "Matrices"
using Vector2Vec2 = std::vector<std::vector<Vec2>>;
using Vector2Mat2 = std::vector<std::vector<Mat2>>;
using Vector2Vec2i = std::vector<std::vector<Vec2i>>;
using Vector2Vec3 = std::vector<std::vector<Vec3>>;

// Matrices

// Shared ptrs
using VectorVec2Ptr = std::shared_ptr<std::vector<Vec2>>;
using VectorMat2Ptr = std::shared_ptr<std::vector<Mat2>>;
using VectorVec2iPtr = std::shared_ptr<std::vector<Vec2i>>;
using VectorVec3Ptr = std::shared_ptr<std::vector<Vec3>>;
using VectorVec3iPtr = std::shared_ptr<std::vector<Vec3i>>;
using VectorMat3Ptr = std::shared_ptr<std::vector<Mat3>>;

using namespace Math::Literals;
typedef SceneGraph::Object<SceneGraph::MatrixTransformation3D> Object3D;
typedef SceneGraph::Scene<SceneGraph::MatrixTransformation3D> Scene3D;

typedef SceneGraph::Object<SceneGraph::MatrixTransformation2D> Object2D;
typedef SceneGraph::Scene<SceneGraph::MatrixTransformation2D> Scene2D;

}  // namespace Magnum

#endif
