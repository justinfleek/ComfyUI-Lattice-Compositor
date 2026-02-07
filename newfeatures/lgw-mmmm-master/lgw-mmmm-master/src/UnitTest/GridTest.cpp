#include <Grids/DenseGrid3d.hpp>
// #include <format>
#include "Common/CustomTypes.hpp"

int main() {
    Grid::DenseGrid3D<float> gA(
        Vec3(0, 0, 0), Vec3(1, 1, 1), (unsigned int)(5)
    );
    Grid::DenseGrid3D<int> gB(Vec3(0, 0, 0), Vec3(1, 1, 1), (unsigned int)(5));
    gA.setConst(0);
    gB.setConst(0);
    float e = 1.0;
    Grid::forEach(
        std::function([&e](const Vec3i& idx, float& aVal, int& bVal) {
            aVal += e;
            bVal -= e;
        }),
        gA, gB
    );
    Grid::rangeIter(
        std::function([&e](
                          const Vec3i& idx, const Vec3i& offset, float& aVal,
                          int& bVal
                      ) {
            aVal += e;
            bVal -= e;
        }),
        Vec3i(1, 1, 1), Vec3i(4, 4, 4), gA, gB
    );
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            for (int k = 0; k < 5; ++k) {
                // std::cout << std::format("({}, {}) ", gA(i, j, k), gB(i, j,
                // k));
                std::cout << "(" << gA(i, j, k) << ", " << gB(i, j, k) << ") ";
            }
            std::cout << "\n";
        }
        std::cout << "\n";
    }
    std::cout << e << "\n";
}
