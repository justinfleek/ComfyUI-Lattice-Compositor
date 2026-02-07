#include "ParticleShaderProgram.h"

#include <Corrade/Containers/Iterable.h>
#include <Corrade/Containers/StringStl.h>
#include <Corrade/Utility/Resource.h>
#include <Magnum/GL/Shader.h>
#include <Magnum/GL/Version.h>
#include <Magnum/Magnum.h>
#include <Magnum/Math/Color.h>
#include <Magnum/Math/Matrix4.h>
// #include <format>
#include <iostream>
#include <sstream>
#include <string>
#include "Corrade/Containers/String.h"
#include "Corrade/Containers/StringView.h"
#include "Corrade/Utility/Assert.h"

namespace Magnum {
ParticleShader::ParticleShader(Int n_lights) {
    Utility::Resource rs("particleShaders");

    GL::Shader vertShader(GL::Version::GL430, GL::Shader::Type::Vertex);
    GL::Shader fragShader(GL::Version::GL430, GL::Shader::Type::Fragment);
    vertShader.addSource(rs.getString("ParticleShader.vert"));

    std::stringstream ss;
    ss << "#define N_LIGHTS " << n_lights << "\n";
    std::string header = ss.str();
    // std::string       header = std::format("#define N_LIGHTS {}\n",
    // n_lights);
    Corrade::Containers::String fragString =
        header + rs.getString("ParticleShader.frag");
    fragShader.addSource(fragString);

    CORRADE_INTERNAL_ASSERT_OUTPUT(
        vertShader.compile() && fragShader.compile()
    );
    attachShaders({vertShader, fragShader});
    CORRADE_INTERNAL_ASSERT(link());

    // GLint  count;
    // GLint  size;  // size of the variable
    // GLenum type;  // type of the variable (float, vec3 or mat4, etc)
    //
    // const GLsizei bufSize = 20;   // maximum name length
    // GLchar        name[bufSize];  // variable name in GLSL
    // GLsizei       length;         // name length
    // glGetProgramiv(this->id(), GL_ACTIVE_UNIFORMS, &count);
    // std::cout << count << " uniforms.\n";
    // for (GLuint i = 0; i < count; i++) {
    //     glGetActiveUniform(this->id(), i, bufSize, &length, &size, &type,
    //     name);
    //
    //     printf("Uniform #%d Type: %u Name: %s\n", i, type, name);
    // }

    m_uViewMatrix = uniformLocation("viewMatrix");
    m_uProjectionMatrix = uniformLocation("projectionMatrix");
    m_uParticleRadius = uniformLocation("particleRadius");
    m_uPointSizeScale = uniformLocation("pointSizeScale");
    m_uGamma = uniformLocation("gamma");
    m_uValueMin = uniformLocation("valueMin");
    m_uValueMax = uniformLocation("valueMax");
    m_uSelection = uniformLocation("selection");
    m_uVisualizeValue = uniformLocation("visualizeValue");
    m_uCuttingPlanes = uniformLocation("cuttingPlanes");
    m_uInvertPlanes = uniformLocation("planeDir");

    pointLightParams.reserve(n_lights);
    for (int i = 0; i < n_lights; ++i) {
        pointLightParams.emplace_back();
        ss.str("");
        ss << "lights[" << i << "].dir";
        std::string name = ss.str();  // std::format("lights[{}].dir", i);
        pointLightParams.back().dir = uniformLocation(name);
        ss.str("");
        ss << "lights[" << i << "].color";
        name = ss.str();  // std::format("lights[{}].color", i);
        pointLightParams.back().color = uniformLocation(name);
    }
}

ParticleShader& ParticleShader::setParticleRadius(Float radius) {
    setUniform(m_uParticleRadius, radius);
    return *this;
}

ParticleShader& ParticleShader::setPointSizeScale(Float scale) {
    setUniform(m_uPointSizeScale, scale);
    return *this;
}

ParticleShader& ParticleShader::setGamma(Float gamma) {
    setUniform(m_uGamma, gamma);
    return *this;
}

// ParticleShader &ParticleShader::setViewport()
ParticleShader& ParticleShader::setViewMatrix(const Matrix4& matrix) {
    setUniform(m_uViewMatrix, matrix);
    return *this;
}

ParticleShader& ParticleShader::setProjectionMatrix(const Matrix4& matrix) {
    setUniform(m_uProjectionMatrix, matrix);
    return *this;
}

ParticleShader& ParticleShader::setVisualize(bool vis) {
    setUniform(m_uVisualizeValue, vis);
    return *this;
}

ParticleShader& ParticleShader::setValueRange(Double min, Double max) {
    setUniform(m_uValueMin, min);
    setUniform(m_uValueMax, max);
    return *this;
}
ParticleShader& ParticleShader::setSelection(Int selection) {
    setUniform(m_uSelection, selection);
    return *this;
}
ParticleShader& ParticleShader::setCuttingPlanes(const Vector3& planes) {
    setUniform(m_uCuttingPlanes, planes);
    return *this;
}
ParticleShader& ParticleShader::setInvertPlanes(bool iX, bool iY, bool iZ) {
    Vector3 invVec = {iX, iY, iZ};
    invVec = -invVec * 2 + Vector3{1.f, 1.f, 1.f};
    setUniform(m_uInvertPlanes, invVec);
    return *this;
}

ParticleShader& ParticleShader::setLightPositions(
    const std::vector<Magnum::Vector4>& lightPos
) {
    CORRADE_INTERNAL_ASSERT(lightPos.size() == pointLightParams.size());

    for (int i = 0; i < lightPos.size(); ++i) {
        setUniform(pointLightParams[i].dir, lightPos[i]);
    }
    return *this;
}
ParticleShader& ParticleShader::setLightColors(
    const std::vector<Magnum::Color3>& lightColor
) {
    CORRADE_INTERNAL_ASSERT(lightColor.size() == pointLightParams.size());

    for (int i = 0; i < lightColor.size(); ++i) {
        setUniform(pointLightParams[i].color, lightColor[i]);
    }
    return *this;
}
}  // namespace Magnum
