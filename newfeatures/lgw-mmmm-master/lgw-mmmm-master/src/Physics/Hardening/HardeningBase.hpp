#pragma once
#include "Common/CustomTypes.hpp"
namespace MPM {
namespace Hardening {
using Type::Vec3, Type::NumT;
class HardeningBase {
public:
    HardeningBase() {}
    virtual ~HardeningBase() {}
    virtual NumT operator()(NumT Jp) const = 0;
    virtual NumT hardeningParam(
        Eigen::Ref<const Vec3> sigOld, Eigen::Ref<const Vec3> sigNew, NumT pOld
    ) const = 0;
    virtual NumT initialParam() const = 0;
};

class NoHardening : public HardeningBase {
public:
    NoHardening() {}
    Type::NumT operator()(Type::NumT Jp) const override { return 1; }
    NumT hardeningParam(
        Eigen::Ref<const Vec3> sigOld, Eigen::Ref<const Vec3> sigNew, NumT pOld
    ) const override {
        return 1;
    }
    NumT initialParam() const override { return 1; }
};

class ExpHardening : public HardeningBase {
public:
    ExpHardening() {}
    Type::NumT operator()(Type::NumT Jp) const override {
        // return exp(10 * (1. - Jp));
        return std::min((Type::NumT)5, (Type::NumT)exp(10 * (1. - Jp)));
        // return std::max(
        //     (Type::NumT)0.1,
        //     std::min((Type::NumT)5, (Type::NumT)exp(10 * (1. - Jp)))
        // );
    }
    NumT hardeningParam(
        Eigen::Ref<const Vec3> sigOld, Eigen::Ref<const Vec3> sigNew, NumT pOld
    ) const override {
        return pOld * sigOld.prod() / sigNew.prod();
    }
    NumT initialParam() const override { return 1; }
};
}  // namespace Hardening
}  // namespace MPM
