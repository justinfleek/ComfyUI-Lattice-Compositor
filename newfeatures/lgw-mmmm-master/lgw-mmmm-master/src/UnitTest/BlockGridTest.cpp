#include "Common/CustomTypes.hpp"
#include "Grids/BlockGrid3d.hpp"
#include "Grids/DenseGrid3d.cpp"

// #include <format>
#include <iostream>

int main() {
    Grid::BlockGrid3D<float, 4> grid(
        Type::Vec3(0, 0, 0), Type::Vec3(1, 1, 1), (unsigned int)(1024)
    );
    grid.setConst(0.3);
    std::cout << grid.getDataSize() << std::endl;
    float g = grid(2, 2, 2);

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            for (int k = 0; k < 5; ++k) {
                float g = grid(i, j, k);
                std::cout << g << " ";
            }
            std::cout << "\n";
        }
        std::cout << "\n";
    }
    grid.set(200, 314, 512, 0.4);
    std::cout << grid.getDataSize() << std::endl;

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            for (int k = 0; k < 5; ++k) {
                std::cout << grid(i + 199, j + 313, k + 511) << " ";
            }
            std::cout << "\n";
        }
        std::cout << "\n";
    }
    std::cout << grid.getDataSize() << std::endl;

    Type::Vec3i start(100, 100, 100);
    Type::Vec3i size(3, 3, 3);
    Grid::rangeIter<false>(
        std::function([&grid](
                          const Type::Vec3i& ijk, const Type::Vec3i& offset,
                          float& f
                      ) { f = ijk[0] + ijk[1] + ijk[2]; }),
        start, start + size, grid
    );
    start += Type::Vec3i(-2, -2, -2);
    Grid::rangeIter<false>(
        std::function([](const Type::Vec3i& ijk, const Type::Vec3i& offset,
                         float& f) { f = 0.4; }),
        start, start + size, grid
    );
    // start += Type::Vec3i(3, 3, 3);
    Grid::forEach(
        std::function([](const Type::Vec3i& ijk, float& f) {
            f = (float)ijk[0] / ijk[1];
        }),
        grid
    );
    Grid::forEach(
        std::function([](const Type::Vec3i& ijk, float& f) {
            std::cout << ijk.transpose() << " " << f << "\n";
        }),
        grid
    );
}
