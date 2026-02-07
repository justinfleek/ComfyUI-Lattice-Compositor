#ifndef PLY_EXPORTER_HPP
#define PLY_EXPORTER_HPP

#include <Eigen/Dense>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include "Common/CustomTypes.hpp"
void exportDataToPLY(
    const std::string& filename, bool doublePrecision, bool rotationOnly,
    const std::vector<Type::NumT>& data
);

#endif
