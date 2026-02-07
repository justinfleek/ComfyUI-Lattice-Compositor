#ifndef GRID_PARAMETERS_HPP
#define GRID_PARAMETERS_HPP
#include "Common/CustomTypes.hpp"

namespace Params {

// using namespace Type;
struct Grid {
    /// @brief MPM grid resolution
    Type::Vec3i gridResolution = {30, 30, 30};
    /// @brief Lower-left corner of the grid, default to origin
    Type::Vec3 gridStart = {0., 0., 0.};
    /// @brief Size of the domain, default 1mx1m
    Type::Vec3 gridEnd = {1., 1., 1.};
    Type::Vec3 gridSize() const { return gridEnd - gridStart; }
};

/// @brief MPM geometric parameters
}  // namespace Params
#endif
