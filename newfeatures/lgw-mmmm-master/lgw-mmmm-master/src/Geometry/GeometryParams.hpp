#include "Common/CustomTypes.hpp"
#include "Grids/DenseGrid3d.hpp"

namespace Params {
struct Volume {
    virtual void         fillGrid(::Grid::DenseGrid3D<NumT>& sdfGrid) const = 0;
    virtual Params::Grid calculateGridParameters() const                    = 0;

    Type::Vec3  velocity = Type::Zero3;
    Type::Vec3i resolution =
        Type::Zero3i;  // Internal discretization of the SDF
};                     // Volume
struct VolumeCuboid : public Volume {
    VolumeCuboid() = default;
    VolumeCuboid(
        const Type::Vec3&  minCorner,
        const Type::Vec3&  maxCorner,
        const Type::Vec3i& resolution
    );
    virtual void fillGrid(::Grid::DenseGrid3D<NumT>& sdfGrid) const;
    // virtual GridParameters calculateGridParameters() const;
    virtual Params::Grid calculateGridParameters() const;

    Type::Vec3 center = Type::Zero3, diagonal = Type::Zero3;
};  // VolumeCuboid
struct VolumeMesh : public Volume {
    VolumeMesh() = default;
    VolumeMesh(
        const std::string& filename,
        const Type::Vec3i& resolution,
        const Type::Vec3&  offset = Type::Zero3
    );
    virtual void         fillGrid(::Grid::DenseGrid3D<NumT>& sdfGrid) const;
    virtual Params::Grid calculateGridParameters() const;

    std::string filename = "";
    Type::Vec3  offset   = Type::Zero3;
};  // VolumeCuboid
struct ObstacleMesh : public Params::VolumeMesh {
    ObstacleMesh() = default;
    ObstacleMesh(
        const std::string& filename,
        // const std::string& physicsFile,
        const Type::Vec3i& resolution,
        const Type::Vec3&  offset   = Type::Zero3,
        const Type::Vec3&  velocity = Type::Zero3,
        const Type::Vec3&  angVel   = Type::Zero3,
        const Type::NumT   density  = 1000
    );
    Type::Vec3 velocity, angVel;
    Type::NumT density;
    bool       active = false;
};  // ObstacleMesh
}  // namespace Params
