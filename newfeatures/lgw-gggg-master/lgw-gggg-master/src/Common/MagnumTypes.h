#ifndef __MAGNUMTYPES_H__
#define __MAGNUMTYPES_H__

#include <frictionfrenzy/FrictionFrenzy.h>
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/MatrixTransformation3D.h>
#include <Magnum/SceneGraph/Scene.h>

namespace Magnum {
using namespace Math::Literals;
typedef SceneGraph::Object<SceneGraph::MatrixTransformation3D> Object3D;
typedef SceneGraph::Scene<SceneGraph::MatrixTransformation3D> Scene3D;

typedef SceneGraph::Object<SceneGraph::MatrixTransformation2D> Object2D;
typedef SceneGraph::Scene<SceneGraph::MatrixTransformation2D> Scene2D;
}  // namespace Magnum
namespace Homogenization {
using FrictionFrenzy::Scalar;
typedef Magnum::UnsignedInt UnsignedInt;
typedef Magnum::Byte Byte;

typedef Magnum::Math::Vector3<Scalar> MagnumVector3;
typedef Magnum::Math::Vector2<int> MagnumVector2i;
typedef Magnum::Math::Matrix3<Scalar> MagnumMatrix3;
typedef Magnum::Math::Matrix4<Scalar> MagnumMatrix4;
typedef Magnum::Math::Quaternion<Scalar> MagnumQuaternion;
typedef Magnum::Math::DualQuaternion<Scalar> DualQuaternion;
typedef Magnum::Math::Rad<Scalar> Rad;
typedef Magnum::Math::Deg<Scalar> Deg;
}  // namespace ContactSimulation

#endif
