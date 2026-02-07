#ifndef __ORTHO_CAMERA2D_H__
#define __ORTHO_CAMERA2D_H__
#include <Magnum/Magnum.h>
#include <Magnum/Math/Vector2.h>
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/Object.h>
#include <Magnum/SceneGraph/Scene.h>

#include "Drawables/MagnumTypes.h"

//#define DEBUG_CAMERA

namespace Magnum {
namespace Camera {

class OrthoCamera2D {
public:
    OrthoCamera2D(
        Scene2D& scene, Vector2i frameBufferSize, Float zoom = 1,
        Vector2 pos = {0.f, 0.f}
    )
        : m_zoom(zoom),
          m_pos(pos),
          m_camera_obj(&scene),
          m_camera(m_camera_obj),
          m_frameBufferSize(frameBufferSize) {
        m_camera.setAspectRatioPolicy(SceneGraph::AspectRatioPolicy::Extend)
            .setProjectionMatrix(Matrix3::projection({zoom, zoom}))
            .setViewport(frameBufferSize);
        m_camera_obj.setTransformation(Matrix3::translation(pos));
    }

    void draw(SceneGraph::DrawableGroup2D& group) { m_camera.draw(group); }

    void reshape(const Vector2i& frameBufferSize) {
        m_frameBufferSize = frameBufferSize;
        m_camera.setViewport(frameBufferSize);
    }

    void update() {
        m_camera.setProjectionMatrix(Matrix3::projection({m_zoom, m_zoom}));
        m_camera_obj.setTransformation(Matrix3::translation(m_pos));
    }

    void zoom(Float delta) {
        // m_zoom *= static_cast<Float>(std::pow(2, 0.5 *
        // static_cast<double>(delta)));
        m_zoom *=
            static_cast<Float>(std::pow(2, 0.25 * static_cast<double>(-delta)));
#ifdef DEBUG_CAMERA
        std::cout << "Zoom: " << m_zoom << std::endl;
#endif
    }

    Vector2 imgToWorldCoordinate(Vector2i imgPos) {
        const Vector2 locPos(
            -0.5f + static_cast<float>(imgPos[0]) / m_frameBufferSize[0],
            0.5f - static_cast<float>(imgPos[1]) / m_frameBufferSize[1]
        );
        return m_pos + m_zoom * locPos;
    }

    void initTransformation(Vector2i pos) {
        m_clickInitPos = pos;
        m_pos_old = m_pos;
    }

    void move(const Vector2i pos) {
        const Vector2i diff = m_clickInitPos - pos;
        moveDiff(diff);
#ifdef DEBUG_CAMERA
        std::cout << "Pos: " << m_pos[0] << ", " << m_pos[1] << std::endl;
#endif
    }

    void moveDiff(const Vector2i diff) {
        const int frameMax =
            std::min(m_frameBufferSize.x(), m_frameBufferSize.y());
        Vector2 inc(diff);
        inc *= m_zoom / frameMax;
        inc.y() *= -1;
        m_pos = m_pos_old + inc;
    }

    Float m_zoom;
    Vector2 m_pos, m_pos_old;
    Object2D m_camera_obj;
    SceneGraph::Camera2D m_camera;
    Vector2i m_frameBufferSize;
    Vector2i m_clickInitPos;
};

}  // namespace Camera
}  // namespace Magnum

#endif
