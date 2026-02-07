#pragma once

#include "../MpmParams.hpp"
#include "Common/CustomTypes.hpp"
namespace MPM {
namespace Plastic {
using namespace Type;

enum class ReturnMapType : uint8_t {
    None = 0,
    PreserveVolume = 1,
    ResistExpand = 1 << 1,
    ResistShrink = 1 << 2,
    SandLike = 1 << 3
};
constexpr ReturnMapType operator|(
    const ReturnMapType& a, const ReturnMapType& b
) {
    return static_cast<ReturnMapType>(
        static_cast<uint8_t>(a) | static_cast<uint8_t>(b)
    );
}
constexpr ReturnMapType operator&(
    const ReturnMapType& a, const ReturnMapType& b
) {
    return static_cast<ReturnMapType>(
        static_cast<uint8_t>(a) & static_cast<uint8_t>(b)
    );
}
/**
 * @brief Base class of a yield surface. We assume that the yield surface is
 * isotropic, in the sense that its values solely depend on the singular values
 * of the Kirchhoff stress tensor. Yield surfaces are further devided into two
 * types:
 *
 * 1. Deformation constraints directly constrain the deformation, such as the
 * case with Eulerean fluids or snow.
 * 2. Stress constraints modify the stress to conform to a certain yield surface
 * instead.
 */
class YieldSurfaceBase {
public:
    YieldSurfaceBase() {}

    /// @brief Get the volume of the
    virtual Params::PlasticityType type() const {
        return Params::PlasticityType::None;
    }
    virtual ReturnMapType returnMapType() const { return ReturnMapType::None; }
    virtual bool deformationConstraint() const { return false; }
    virtual Vec3 projectDeformation(const Vec3& sig) const { return sig; }
    virtual Vec3 projectStress(const Vec3& sig) const { return sig; }
    virtual NumT value(const Vec3& T) const { return -1; }
    virtual Vec3 gradient(const Vec3& T) const { return Zero3; }
};
}  // namespace Plastic
}  // namespace MPM
