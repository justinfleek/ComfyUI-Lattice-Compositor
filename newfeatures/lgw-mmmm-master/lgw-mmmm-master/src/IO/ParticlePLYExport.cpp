#include "ParticlePLYExport.hpp"

void exportDataToPLY(
    const std::string& filename, bool doublePrecision, bool rotationOnly,
    const std::vector<Type::NumT>& data
) {
    const char* header =
        "ply\n"
        "format binary_little_endian 1.0\n";
    const char* dataType = (doublePrecision) ? "double" : "float";
    std::stringstream ss;
    ss << "ply\nformat binary_little_endian 1.0\n";
    ss << "element vertex "
       << (rotationOnly ? data.size() / 7 : data.size() / 12) << "\n";
    for (int i = 0; i < 3; ++i) {
        ss << "property " << dataType << " " << char('x' + i) << "\n";
    }
    if (rotationOnly) {
        for (int i = 0; i < 4; ++i) {
            ss << "property " << dataType << " q" << char('w' + i) << "\n";
        }
    } else {
        for (int i = 0; i < 4; ++i) {
            ss << "property " << dataType << " F" << char('a' + i) << "\n";
        }
    }
    ss << "end_header\n";
    std::string headerVert = ss.str();

    std::ofstream file(filename, std::ios::binary | std::ios::trunc);
    file.write(headerVert.data(), headerVert.size());
    if (doublePrecision) {
        file.write(
            reinterpret_cast<const char*>(data.data()),
            data.size() * sizeof(Type::NumT)
        );
    } else {
        Eigen::VectorXf dataSingle =
            Eigen::Map<const Eigen::VectorXd>(data.data(), data.size())
                .cast<float>();
        file.write(
            reinterpret_cast<const char*>(dataSingle.data()),
            dataSingle.size() * sizeof(float)
        );
    }
}
