#ifndef __PARTICLE_BASE_H__
#define __PARTICLE_BASE_H__

#include <Drawables/ColoredDrawable.h>
#include <Drawables/MagnumTypes.h>
#include <Magnum/GL/Buffer.h>
#include <Magnum/GL/Mesh.h>
#include <Magnum/Magnum.h>
#include <Magnum/Trade/MeshData.h>

namespace Particles {

struct ParticleState2D {
    void ApplySimplecticEuler(
        ParticleState2D& out, Magnum::Vector2 force, Magnum::Float torque,
        Magnum::Float mass, Magnum::Float inertia, Magnum::Float dt
    ) {
        out.m_velocity = m_velocity + force / mass * dt;
        out.m_angularVel = m_angularVel + torque / inertia * dt;
        out.m_translation = m_translation + out.m_velocity * dt;
        out.m_orientation = m_orientation + out.m_angularVel * dt;
    }
    Magnum::Vector2 m_translation;
    Magnum::Vector2 m_velocity;
    Magnum::Float m_orientation;
    Magnum::Float m_angularVel;
};
class ParticleBase2D {
public:
    ParticleBase2D() {}
    virtual ~ParticleBase2D() {}
    ParticleBase2D(
        Magnum::Vector2 translation, Magnum::Float orientation,
        Magnum::Float mass = 1
    )
        : m_state{translation, Magnum::Vector2{0, 0}, orientation, Magnum::Float(0)},
          m_mass(mass),
          m_inertia(1){};
    virtual size_t meshPointCount() const = 0;
    virtual size_t meshIndexCount() const = 0;
    virtual void writeMeshData(
        std::vector<Magnum::Vector2>& points,
        std::vector<Magnum::Vector3ui>& indices, const size_t pOffset,
        const size_t iOffset
    ) const = 0;
    virtual Magnum::Float signedDistance(Magnum::Vector2 query) const = 0;

    ParticleState2D m_state;
    Magnum::Float m_mass;
    Magnum::Float m_inertia;

protected:
};

/// @brief Renderable for a set of particles
class ParticleGroup2D {
public:
    /// @brief Constructor
    ParticleGroup2D();

    /**
     * @brief Allocate the buffers and init them
     * @param obj Scene object
     */
    void initializeMeshes(Magnum::Object2D& obj);

    ///

    /// @brief Recompute the meshes from the particles and update the buffers
    void updateMeshes();

    /**
     * @brief Update the rendering with a scaling
     * @param scale 2D scaling factor
     */
    void scaleUniform(Magnum::Vector2 scale);

    /**
     * @brief Update the rendering with a shearing
     * @param scale 2D shearing factor
     */
    void shearUniform(Magnum::Vector2 shear);

public:  // BAD
    std::vector<std::unique_ptr<ParticleBase2D>> m_particles;
    Magnum::SceneGraph::DrawableGroup2D m_drawableGroup;

private:
    std::vector<Magnum::Vector2> m_particleMeshPoints;
    std::vector<Magnum::Vector3ui> m_particleMeshIndices;
    std::vector<size_t> m_particleMeshPointOffset;
    std::vector<size_t> m_particleMeshIndexOffset;
    Magnum::GL::Buffer m_particleMeshPointBuffer{Magnum::NoCreate};
    Magnum::GL::Buffer m_particleMeshIndexBuffer{Magnum::NoCreate};
    std::shared_ptr<Magnum::Shaders::FlatGL2D> mp_coloredShader;
    std::shared_ptr<Magnum::GL::Mesh> mp_mesh;
    Magnum::Vector2 m_currentScale = {1.0, 1.0};

    /// @brief Recompute the meshes from the particles
    void recomputeMeshes();

    /// @brief Update the GPU buffers
    void updateMeshesBuffers();
};

class CircularParticle2D : public ParticleBase2D {
public:
    CircularParticle2D(
        Magnum::Vector2 position, Magnum::Float radius, Magnum::Float density
    )
        : m_radius(radius) {
        this->m_mass =
            density * radius * radius * static_cast<Magnum::Float>(M_PI);
        this->m_state = {position, {0, 0}, 0, 0};
        this->m_inertia =
            static_cast<Magnum::Float>(0.5) * this->m_mass * radius * radius;
    }
    Magnum::Float signedDistance(Magnum::Vector2 query) const override {
        Magnum::Vector2 diff = query - this->m_state.m_translation;
        return diff.length() - m_radius;
    }
    size_t meshPointCount() const override { return m_segments + 1; };
    size_t meshIndexCount() const override { return m_segments; };
    int segments() const { return m_segments; }
    int nPoints() const { return m_segments + 1; }
    void writeMeshData(
        std::vector<Magnum::Vector2>& points,
        std::vector<Magnum::Vector3ui>& indices, const size_t pOffset,
        const size_t iOffset
    ) const override {
        const Magnum::Float o = this->m_state.m_orientation;
        const Magnum::Vector2 t = this->m_state.m_translation;
        points[pOffset] = t;
        points[pOffset + 1] =
            t + m_radius * Magnum::Vector2{std::cos(o), std::sin(o)};
        for (int i = 1; i < m_segments; ++i) {
            Magnum::Float angle = o + 2 * static_cast<Magnum::Float>(M_PI) *
                                          Magnum::Float(i) / m_segments;
            points[pOffset + i + 1] =
                t +
                m_radius * Magnum::Vector2{std::cos(angle), std::sin(angle)};
            // std::cout << t[0] << " " << t[1] << std::endl;
            indices[iOffset + i - 1] =
                Magnum::Vector3ui(pOffset, pOffset + i, pOffset + i + 1);
        }
        indices[iOffset + m_segments - 1] =
            Magnum::Vector3ui(pOffset, pOffset + m_segments, pOffset + 1);
        return;
    }

    Magnum::Float m_radius;
    const int m_segments = 16;

protected:
};
}  // namespace Particles

#endif
