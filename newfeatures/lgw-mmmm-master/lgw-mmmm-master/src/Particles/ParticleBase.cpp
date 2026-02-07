#include "ParticleBase.h"

#include <iostream>

namespace Particles {

ParticleGroup2D::ParticleGroup2D() {}

void ParticleGroup2D::initializeMeshes(Magnum::Object2D& obj) {
    // Clear data
    size_t pointCount = 0, idxCount = 0;
    m_particleMeshPointOffset.clear();
    m_particleMeshIndexOffset.clear();
    m_particleMeshPointOffset.reserve(m_particles.size());
    m_particleMeshIndexOffset.reserve(m_particles.size());

    // ?
    for (size_t i = 0; i < m_particles.size(); ++i) {
        m_particleMeshPointOffset.push_back(pointCount);
        m_particleMeshIndexOffset.push_back(idxCount);
        pointCount += m_particles[i]->meshPointCount();
        idxCount += m_particles[i]->meshIndexCount();
    }

    m_particleMeshPoints.resize(pointCount);
    m_particleMeshIndices.resize(idxCount);

    // Compute meshes
    recomputeMeshes();

    // Create GPU Buffers
    m_particleMeshPointBuffer = Magnum::GL::Buffer(
        Corrade::Containers::ArrayView<const Magnum::Vector2>(
            m_particleMeshPoints.data(), m_particleMeshPoints.size()
        ),
        Magnum::GL::BufferUsage::DynamicDraw
    );
    m_particleMeshIndexBuffer = Magnum::GL::Buffer(
        Corrade::Containers::ArrayView<const Magnum::Vector3ui>(
            m_particleMeshIndices.data(), m_particleMeshIndices.size()
        )
    );

    // Create mesh
    mp_mesh =
        std::make_shared<Magnum::GL::Mesh>(Magnum::MeshPrimitive::Triangles);
    (*mp_mesh)
        .setCount(m_particleMeshIndices.size() * 3)
        .addVertexBuffer(
            m_particleMeshPointBuffer, 0, Magnum::Shaders::FlatGL2D::Position{}
        )
        .setIndexBuffer(
            m_particleMeshIndexBuffer, 0, Magnum::MeshIndexType::UnsignedInt
        );
    // Create shader
    mp_coloredShader = std::make_shared<Magnum::Shaders::FlatGL2D>();
    mp_coloredShader->setColor(Magnum::operator""_rgbf(0xffffff));
    // Create drawable and give it to drawable group
    new Magnum::ColoredDrawable2D(
        obj, mp_coloredShader, mp_mesh, Magnum::operator""_rgbf(0xffffff),
        m_drawableGroup
    );
}
void ParticleGroup2D::updateMeshes() {
    recomputeMeshes();
    updateMeshesBuffers();
}

// Could be factorised with the update
void ParticleGroup2D::scaleUniform(Magnum::Vector2 scale) {
    m_currentScale = scale;
    const Magnum::Vector2 s = scale / m_currentScale;
    for (size_t i = 0; i < m_particles.size(); ++i) {
        m_particles[i]->m_state.m_translation *= s;
        m_particles[i]->writeMeshData(
            m_particleMeshPoints, m_particleMeshIndices,
            m_particleMeshPointOffset[i], m_particleMeshIndexOffset[i]
        );
    }
}

void ParticleGroup2D::shearUniform(Magnum::Vector2 shear) {}

void ParticleGroup2D::recomputeMeshes() {
#pragma omp parallel for
    for (size_t i = 0; i < m_particles.size(); ++i) {
        m_particles[i]->writeMeshData(
            m_particleMeshPoints, m_particleMeshIndices,
            m_particleMeshPointOffset[i], m_particleMeshIndexOffset[i]
        );
    }
}

void ParticleGroup2D::updateMeshesBuffers() {
    m_particleMeshPointBuffer.setSubData(
        0, Corrade::Containers::ArrayView<const Magnum::Vector2>(
               m_particleMeshPoints.data(), m_particleMeshPoints.size()
           )
    );
}

}  // namespace Particles
