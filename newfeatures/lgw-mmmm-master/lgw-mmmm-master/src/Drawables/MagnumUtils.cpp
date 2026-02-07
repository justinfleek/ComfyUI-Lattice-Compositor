#include "Drawables/MagnumUtils.hpp"

namespace std {

std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector2<Type::NumT>& vec
) {
    os << "(" << vec[0] << ", " << vec[1] << ")";
    return os;
}

std::ostream& operator<<(
    std::ostream& os, const Magnum::Math::Vector3<float>& vec
) {
    os << "(" << vec[0] << ", " << vec[1] << ", " << vec[2] << ")";
    return os;
}

}  // namespace std

namespace Magnum {

Color3 hexToRgbf(unsigned long long hexColor) {
    return Math::Literals::operator""_rgbf(hexColor);
}

Color4 hexToRgbaf(unsigned long long hexColor) {
    return Math::Literals::operator""_rgbaf(hexColor);
}

}  // namespace Magnum
