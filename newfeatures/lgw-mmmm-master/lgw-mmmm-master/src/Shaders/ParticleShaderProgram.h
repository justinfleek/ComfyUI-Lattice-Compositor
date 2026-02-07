#pragma once

#include <Magnum/Shaders/Shaders.h>
#include <vector>
#include "Magnum/GL/AbstractShaderProgram.h"

namespace Magnum {
class ParticleShader : public GL::AbstractShaderProgram {
public:
    explicit ParticleShader(Int n_lights);

    ParticleShader& setParticleRadius(Float radius);
    ParticleShader& setPointSizeScale(Float scale);

    // ParticleShader& setViewport(const Vector2i& viewport);
    ParticleShader& setViewMatrix(const Matrix4& matrix);
    ParticleShader& setProjectionMatrix(const Matrix4& matrix);
    ParticleShader& setCuttingPlanes(const Vector3& planes);
    ParticleShader& setValueRange(Double min, Double max);
    ParticleShader& setVisualize(bool vis);
    ParticleShader& setSelection(Int selection);
    ParticleShader& setLightPositions(
        const std::vector<Magnum::Vector4>& lightPos
    );
    ParticleShader& setLightColors(const std::vector<Magnum::Color3>& lightColor
    );
    ParticleShader& setGamma(Float gamma);
    ParticleShader& setInvertPlanes(bool iX, bool iY, bool iZ);

private:
    Int m_uParticleRadius;
    Int m_uPointSizeScale;
    Int m_uViewMatrix;
    Int m_uProjectionMatrix;
    Int m_uValueMin;
    Int m_uValueMax;
    Int m_uSelection;
    Int m_uVisualizeValue;
    Int m_uGamma;
    Int m_uCuttingPlanes;
    Int m_uInvertPlanes;
    struct lightParam {
        Int dir;
        Int color;
    };
    std::vector<lightParam> pointLightParams;
};
}  // namespace Magnum
