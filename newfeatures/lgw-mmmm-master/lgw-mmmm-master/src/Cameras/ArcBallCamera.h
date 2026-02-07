#ifndef Magnum_Examples_ArcBallCamera_h
#define Magnum_Examples_ArcBallCamera_h
/*
    This file is part of Magnum.

    Original authors — credit is appreciated but not required:

        2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019,
        2020, 2021, 2022 — Vladimír Vondruš <mosra@centrum.cz>
        2020 — Nghia Truong <nghiatruong.vn@gmail.com>

    This is free and unencumbered software released into the public domain.

    Anyone is free to copy, modify, publish, use, compile, sell, or distribute
    this software, either in source code form or as a compiled binary, for any
    purpose, commercial or non-commercial, and by any means.

    In jurisdictions that recognize copyright laws, the author or authors of
    this software dedicate any and all copyright interest in the software to
    the public domain. We make this dedication for the benefit of the public
    at large and to the detriment of our heirs and successors. We intend this
    dedication to be an overt act of relinquishment in perpetuity of all
    present and future rights to this software under copyright law.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
    THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
    IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
    CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include <Magnum/SceneGraph/AbstractTranslationRotation3D.h>
#include <Magnum/SceneGraph/Camera.h>
#include <Magnum/SceneGraph/Object.h>
#include <Magnum/SceneGraph/Scene.h>
#include <iostream>
#include "ArcBall.h"

namespace Magnum {
namespace Camera {

/* Arcball camera implementation integrated into the SceneGraph */
class ArcBallCamera : public ArcBall {
public:
    template <class Transformation>
    ArcBallCamera(
        SceneGraph::Scene<Transformation>& scene, const Vector3& cameraPosition,
        const Vector3& viewCenter, const Vector3& upDir, Deg fov,
        const Vector2i& windowSize, const Vector2i& viewportSize
    )
        : ArcBall{cameraPosition, viewCenter, upDir, fov, windowSize},
          _cameraPos(cameraPosition) {
        /* Create a camera object of a concrete type */
        auto* cameraObject = new SceneGraph::Object<Transformation>{&scene};
        (*(_camera = new SceneGraph::Camera3D{*cameraObject}))
            .setAspectRatioPolicy(SceneGraph::AspectRatioPolicy::Extend)
            .setProjectionMatrix(Matrix4::perspectiveProjection(
                fov, Vector2{windowSize}.aspectRatio(), 0.01f, 1000.0f
            ))
            .setViewport(viewportSize);

        /* Save the abstract transformation interface and initialize the
           camera position through that */
        (*(_cameraObject = cameraObject))
            .rotate(transformation().rotation())
            .translate(transformation().translation());

        update(true);
    }

    /* Update screen and viewport size after the window has been resized */
    void reshape(const Vector2i& windowSize, const Vector2i& viewportSize) {
        _windowSize = windowSize;
        _camera->setViewport(viewportSize);
    }

    void setViewParameters(
        const Vector3& eye, const Vector3& viewCenter, const Vector3& upDir
    ) {
        ArcBall::setViewParameters(eye, viewCenter, upDir);
        update(true);
    }

    /* Update the SceneGraph camera if arcball has been changed */
    bool update(bool force = false) {
        /* call the internal update */
        if (!force && !updateTransformation())
            return false;

        (*_cameraObject)
            .resetTransformation()
            .rotate(transformation().rotation())
            .translate(transformation().translation());

        const auto& vMat = _camera->cameraMatrix();
        const Vector4 tmp =
            -vMat.transposed() * Vector4(vMat[3][0], vMat[3][1], vMat[3][2], 0);
        _cameraPos = Vector3(tmp[0], tmp[1], tmp[2]);

        return true;
    }

    /* Draw objects using the internal scenegraph camera */
    void draw(SceneGraph::DrawableGroup3D& drawables) {
        _camera->draw(drawables);
    }

    /* Accessor to the raw camera object */
    SceneGraph::Camera3D& camera() const { return *_camera; }

    static constexpr Float screenLimit = 1.1;
    static constexpr Float normalLimit = 0.0;

    /* Rendering helper */
    bool isPosIn(const Vector3& pos, const Vector3& normal) const {
        const auto& vMat = _camera->cameraMatrix();
        const auto& pMat = _camera->projectionMatrix();

        const Vector3 dir = (_cameraPos - pos).normalized();
        const bool faceScreen = (Magnum::Math::dot(normal, dir) >= normalLimit);

        if (!faceScreen) {
            return false;
        }

        if (faceScreen) {
            Vector4 proj = pMat * vMat * Vector4(pos, 1);
            proj /= proj[3];
            const bool inScreen =
                (proj[2] > -0.5) && (-screenLimit <= proj[0]) &&
                (proj[0] <= screenLimit) && (-screenLimit <= proj[1]) &&
                (proj[1] <= screenLimit);

            return inScreen;
        }  // faceScreen

        return false;
    }

    bool isTriangleOnScreen(
        const Vector3& pos0, const Vector3& pos1, const Vector3& pos2
    ) const {
        const auto& vMat = _camera->cameraMatrix();
        const auto& pMat = _camera->projectionMatrix();
        const Vector3 pos[3] = {pos0, pos1, pos2};

        // Is the triangle facing the screen?
        const Vector3 normal =
            Math::cross(pos1 - pos0, pos2 - pos0).normalized();
        bool faceScreen = false;
        for (int i = 0; (i < 3) && (!faceScreen); ++i) {
            faceScreen |=
                (Magnum::Math::dot(
                     normal, (_cameraPos - pos[i]).normalized()
                 ) >= normalLimit);
        }  // i
        if (!faceScreen) {
            return false;
        }

        // Is one of the vertex inside the screen?
        bool posIn = false;
        Vector2 projPos[3];
        for (int i = 0; (i < 3) && (!posIn); ++i) {
            Vector4 proj = pMat * vMat * Vector4(pos[i], 1);
            proj /= proj[3];
            const bool inScreen =
                (proj[2] > -0.5) && (-screenLimit <= proj[0]) &&
                (proj[0] <= screenLimit) && (-screenLimit <= proj[1]) &&
                (proj[1] <= screenLimit);
            posIn |= inScreen;
            projPos[i] = Vector2(proj[0], proj[1]);
        }  // posIn
        if (posIn) {
            return true;
        }

        // Is an edge crossing the screen?
        bool edgeScreen = false;
        auto ccw = [](const Vector2& A, const Vector2& B,
                      const Vector2& C) -> bool {
            return (C[1] - A[1]) * (B[0] - A[0]) >
                   (B[1] - A[1]) * (C[0] - A[0]);
        };
        auto intersect = [&ccw](
                             const Vector2& A, const Vector2& B,
                             const Vector2& C, const Vector2& D
                         ) -> bool {
            return (
                (ccw(A, C, D) != ccw(B, C, D)) && (ccw(A, B, C) != ccw(A, B, D))
            );
        };
        const Vector2 screen[4] = {
            Vector2(-screenLimit, -screenLimit),
            Vector2(screenLimit, -screenLimit),
            Vector2(screenLimit, screenLimit),
            Vector2(-screenLimit, screenLimit)};
        for (int i = 0; (i < 3) && (!edgeScreen); ++i) {
            for (int j = 0; (j < 4) && (!edgeScreen); ++j) {
                edgeScreen != intersect(
                                  projPos[i], projPos[(i + 1) % 3], screen[j],
                                  screen[(j + 1) % 4]
                              );
            }  // j
        }      // i

        if (edgeScreen) {
            return true;
        }

        // Is the screen inside the triangle?
        /*
        bool screenIn = false;
        for (int j = 0; (j < 4) && (!screenIn); ++j) {
            const bool ori[3] =
                { ccw(projPos[0], projPos[1], screen[j]),
                  ccw(projPos[1], projPos[2], screen[j]),
                  ccw(projPos[2], projPos[0], screen[j]) };
            screenIn |= (ori[0] == ori[1]) && (ori[1] == ori[2]);
        }
        if (screenIn) {
            return true;
        }
        */

        return false;
    }

    /* Rendering helper */
    Float getFeatureSize(const Vector3& pos) const {
        const Float dist = (pos - _cameraPos).length();
        const Float hh = dist * Math::tan(_fov / _windowSize[0]);
        const Float hw = dist * Math::tan(
                                    _fov / _windowSize[1]
                                );  // hh*Vector2{_windowSize}.aspectRatio();
        return 2 * std::min(hh, hw);
    }

private:
    SceneGraph::AbstractTranslationRotation3D* _cameraObject{};
    SceneGraph::Camera3D* _camera{};
    Vector3 _cameraPos;
};

}  // namespace Camera
}  // namespace Magnum

#endif
