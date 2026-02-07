
#include "Mpm3dDrawable.hpp"
#include <Magnum/EigenIntegration/Integration.h>
#include <Magnum/GL/Attribute.h>
#include <Magnum/GL/Buffer.h>
#include <Magnum/GL/Renderer.h>
#include <Magnum/Mesh.h>
#include <Magnum/MeshTools/Duplicate.h>
#include "Common/CustomTypes.hpp"
#include "Drawables/MagnumUtils.hpp"
#include "Shaders/ParticleShaderProgram.h"

namespace MPM {

MPM3DDrawable::MPM3DDrawable(
    const std::shared_ptr<MPM::MPM3D> mpmSimPtr,
    const Params::Rendering drawParams, Magnum::Object3D& obj,
    Magnum::SceneGraph::DrawableGroup3D& drawableGroup,
    const std::vector<Magnum::Vec4f>& lightPositions,
    const std::vector<Magnum::Color3>& lightColours
    // const bool                           displaySurface
)
    : Magnum::SceneGraph::Drawable3D(obj, &drawableGroup),
      m_mpmSimPtr(mpmSimPtr),
      m_drawParams(drawParams),
      m_lightPositions(lightPositions),
      m_lightColours(lightColours) {
    init(obj, drawableGroup);
}

void MPM3DDrawable::update() {
    updateData();
    updateBuffers();
}

void MPM3DDrawable::draw(
    const Magnum::Matrix4& transformationMatrix,
    Magnum::SceneGraph::Camera3D& camera
) {
    // Particles
    (*m_glParticleShader)
        .setProjectionMatrix(camera.projectionMatrix())
        .setParticleRadius(m_drawParams.pRadius * m_drawParams.particleScale)
        .setViewMatrix(transformationMatrix)
        .setPointSizeScale(
            camera.viewport().x() * camera.projectionMatrix()[0][0]
        )
        .setValueRange(m_valueMin, m_valueMax)
        .setVisualize(m_displayDebug)
        .setSelection(m_selectedParticle)
        .draw(*m_glPartPointMesh);
}

void MPM3DDrawable::init(
    Magnum::Object3D& obj, Magnum::SceneGraph::DrawableGroup3D& drawableGroup
) {
    // Data
    const VectorVec3& posPtr = m_mpmSimPtr->getPartPosPtr();
    const VectorNumT& debugVals = m_mpmSimPtr->getPartDebugData().data;
    const VectorI& partId = m_mpmSimPtr->getParticleIDArray();
    const size_t nbPart = posPtr.size();

    // Fill the data
    updateData();

    // Allocate GPU buffers
    /// Pos
    m_glPartPosBuffer = Magnum::GL::Buffer(
        Corrade::Containers::ArrayView<const Magnum::Vector3d>(
            reinterpret_cast<const Magnum::Vector3d*>(posPtr.data()),
            posPtr.size()
        ),
        Magnum::GL::BufferUsage::DynamicDraw
    );
    m_glPartDebugBuffer =
        Magnum::GL::Buffer(Corrade::Containers::ArrayView<const NumT>(
            debugVals.data(), debugVals.size()
        ));
    m_glPartDebugBuffer =
        Magnum::GL::Buffer(Corrade::Containers::ArrayView<const NumT>(
            debugVals.data(), debugVals.size()
        ));
    m_glPartIdBuffer = Magnum::GL::Buffer(
        Corrade::Containers::ArrayView<const int>(partId.data(), partId.size())
    );

    // Create GL mesh and give them the buffers
    m_glPartPointMesh =
        std::make_shared<Magnum::GL::Mesh>(Magnum::GL::MeshPrimitive::Points);
    (*m_glPartPointMesh)
        .setCount(posPtr.size())
        .addVertexBuffer(
            m_glPartPosBuffer, 0, Magnum::GL::Attribute<0, Magnum::Vector3d>{}
        )
        .addVertexBuffer(
            m_glPartDebugBuffer, 0, Magnum::GL::Attribute<1, NumT>{}
        )
        .addVertexBuffer(m_glPartIdBuffer, 0, Magnum::GL::Attribute<2, int>{});

    // Create shaders
    m_glFlatShader = std::make_shared<Magnum::Shaders::FlatGL3D>();

    m_glPhongShader = std::make_shared<Magnum::Shaders::PhongGL>(
        Magnum::Shaders::PhongGL::Flag::VertexColor |
            Magnum::Shaders::PhongGL::Flag::AlphaMask,
        m_lightPositions.size()
    );
    (*m_glPhongShader)
        .setAmbientColor(Magnum::hexToRgbaf(0x33333300))
        .setSpecularColor(Magnum::hexToRgbaf(0xffffff00))
        .setShininess(150.f)  // 80.f)
        .setAlphaMask(0.1f)
        .setLightPositions(Magnum::Containers::ArrayView<const Magnum::Vec4f>(
            m_lightPositions.data(), m_lightPositions.size()
        ))
        .setLightColors(Magnum::Containers::ArrayView<const Magnum::Color3>(
            m_lightColours.data(), m_lightColours.size()
        ));

    m_glParticleShader =
        std::make_shared<Magnum::ParticleShader>(m_lightPositions.size());
    (*m_glParticleShader)
        .setLightPositions(m_lightPositions)
        .setLightColors(m_lightColours);

    m_glMeshShader = std::make_shared<Magnum::Shaders::MeshVisualizerGL3D>(
        Magnum::Shaders::MeshVisualizerGL3D::Flag::Wireframe |
        Magnum::Shaders::MeshVisualizerGL3D::Flag::NoGeometryShader
    );
    (*m_glMeshShader)
        .setColor(Magnum::hexToRgbf(0xdcdcdc))
        .setWireframeColor(Magnum::hexToRgbf(0x2f83cc));
}

void MPM3DDrawable::updateData() {
    // Data
    m_displayDebug =
        m_mpmSimPtr->getDebugParameters() != Params::DisplayValue::None;

    const VectorVec3& posPtr = m_mpmSimPtr->getPartPosPtr();
    m_valueMin = m_mpmSimPtr->getPartDebugData().min;
    m_valueMax = m_mpmSimPtr->getPartDebugData().max;
    if (m_valueMax - m_valueMin <= 1e-3) {
        Magnum::Double avg = 0.5 * (m_valueMin + m_valueMax);
        m_valueMin = avg - 5e-4;
        m_valueMax = avg + 5e-4;
    }
}

void MPM3DDrawable::updateBuffers() {
    const VectorVec3& posPtr = m_mpmSimPtr->getPartPosPtr();
    const VectorNumT& debugVals = m_mpmSimPtr->getPartDebugData().data;
    const VectorI& partId = m_mpmSimPtr->getParticleIDArray();

    m_glPartPosBuffer.setSubData(
        0, Corrade::Containers::ArrayView<const Magnum::Vector3d>(
               reinterpret_cast<const Magnum::Vector3d*>(posPtr.data()),
               posPtr.size()
           )
    );
    m_glPartDebugBuffer.setSubData(
        0, Corrade::Containers::ArrayView<const NumT>(
               debugVals.data(), debugVals.size()
           )
    );
    m_glPartIdBuffer.setSubData(
        0,
        Corrade::Containers::ArrayView<const int>(partId.data(), partId.size())
    );
}

void MPM3DDrawable::setDebugData(const Params::DisplayValue& disp) {
    m_mpmSimPtr->getDebugParameters() = disp;
    m_mpmSimPtr->updateDebugData();
    update();
}

}  // namespace MPM
