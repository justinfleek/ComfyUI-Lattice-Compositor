add_library(Sampling STATIC
    PoissonDisk.h
    PoissonDisk.cpp
)
target_link_libraries(Sampling
  Grids
  Physics
  Geometry)
