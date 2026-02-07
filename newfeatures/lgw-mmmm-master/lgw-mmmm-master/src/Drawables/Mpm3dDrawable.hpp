#ifndef MPM_3D_DRAWABLE_HPP
#define MPM_3D_DRAWABLE_HPP

#include <Magnum/GL/Buffer.h>
#include <Magnum/GL/Mesh.h>
#include <Magnum/Magnum.h>

#include <Magnum/SceneGraph/Drawable.h>
#include <Magnum/SceneGraph/MatrixTransformation2D.h>
#include <Magnum/SceneGraph/MatrixTransformation3D.h>
#include <Magnum/SceneGraph/Scene.h>
#include <Magnum/SceneGraph/SceneGraph.h>

#include <Magnum/Shaders/FlatGL.h>
#include <Magnum/Shaders/LineGL.h>
#include <Magnum/Shaders/MeshVisualizerGL.h>
#include <Magnum/Shaders/PhongGL.h>
#include <Magnum/Shaders/VertexColorGL.h>

#include "Drawables/MagnumTypes.h"
#include "Physics/Mpm3d.hpp"
#include "Shaders/ParticleShaderProgram.h"

namespace MPM {

class MPM3DDrawable : public Magnum::SceneGraph::Drawable3D {
public:
    /**
     * @brief Constructor
     * @param mpmSimPtr  MPM simulation
     * @param drawParams
     * @param obj  Obj node graph
     * @param drawableGroup  Drawable manager
     */
    MPM3DDrawable(
        const std::shared_ptr<MPM::MPM3D> mpmSimPtr,
        const Params::Rendering drawParams, Magnum::Object3D& obj,
        Magnum::SceneGraph::DrawableGroup3D& drawableGroup,
        const std::vector<Magnum::Vec4f>& lightPositions,
        const std::vector<Magnum::Color3>& lightColours
        // const bool                           displaySurface
    );

    /// @brief Update data to draw
    void update();

    void setSelectedParticle(Magnum::Int selected) {
        m_selectedParticle = selected;
    }

    Magnum::ParticleShader* getParticleShader() {
        return m_glParticleShader.get();
    }

    void setDebugData(const Params::DisplayValue& disp);

private:
    /**
     * @brief Draw procedure
     * @param transformationMatrix MVP
     * @param camera
     */
    void draw(
        const Magnum::Matrix4& transformationMatrix,
        Magnum::SceneGraph::Camera3D& camera
    ) override;

private:
    /// @brief Init all the buffers
    void init(
        Magnum::Object3D& obj,
        Magnum::SceneGraph::DrawableGroup3D& drawableGroup
    );

    /// @brief Update geometry
    void updateData();
    /// @brief Update GPU buffers
    void updateBuffers();

    /// @brief Sim data
    const std::shared_ptr<MPM::MPM3D> m_mpmSimPtr;

    /// @brief Rendering parameters
    const Params::Rendering m_drawParams;

    /// @brief Display implicit surface
    // bool m_displaySurface;

    ///// Visualizations
    bool m_displayDebug;
    Magnum::Double m_valueMin, m_valueMax;

    ///// GPU buffers

    /// @brief GL Particles positions buffer
    Magnum::GL::Buffer m_glPartPosBuffer{Magnum::NoCreate};
    Magnum::GL::Buffer m_glPartIdBuffer{Magnum::NoCreate};
    Magnum::GL::Buffer m_glPartDebugBuffer{Magnum::NoCreate};

    ///// GL Meshes

    /// @brief GL Particles mesh
    std::shared_ptr<Magnum::GL::Mesh> m_glPartPointMesh;

    ///// Shaders

    /// @brief Color vertex shader
    std::shared_ptr<Magnum::Shaders::PhongGL> m_glPhongShader;
    /// @brief Flat shader
    std::shared_ptr<Magnum::Shaders::FlatGL3D> m_glFlatShader;
    /// @brief Vertex shader
    std::shared_ptr<Magnum::Shaders::VertexColorGL3D> m_glVertexShader;
    /// @brief Mesh shader
    std::shared_ptr<Magnum::Shaders::MeshVisualizerGL3D> m_glMeshShader;

    std::shared_ptr<Magnum::ParticleShader> m_glParticleShader;

    /// @brief Light positions
    const std::vector<Magnum::Vec4f>& m_lightPositions;
    /// @brief Light colours
    const std::vector<Magnum::Color3>& m_lightColours;

    /// @brief Selected particle
    Magnum::Int m_selectedParticle;

};  // class MPM3DDrawable

}  // namespace MPM

#endif  // MPM_3D_DRAWABLE_HPP
