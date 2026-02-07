add_library(__ff_CollisionObject STATIC
    CollisionObject.h
    RigidObjectBase.cpp
    RigidObjectBase.h
    Mesh.cpp
    Mesh.h
    Cube.h
    Cube.cpp
    Sphere.cpp
    Sphere.h
    Ellipsoid.cpp
    Ellipsoid.h
    Convex.h
    Convex.cpp
)
add_dependencies(__ff_CollisionObject
    fcl
	ccd
	Discregrid
)
target_link_libraries(__ff_CollisionObject
    OpenMP::OpenMP_CXX
    Eigen3::Eigen
    
    ${FCL_LIBRARY}
    ${CCD_LIBRARY}
	${DISCREGRID_LIBRARY}
)
target_include_directories(__ff_CollisionObject PUBLIC
	${FRICTION_COMMON_DIR}
)
target_include_directories(__ff_CollisionObject SYSTEM PUBLIC
	${CCD_INCLUDE_PATH}
	${FCL_INCLUDE_PATH}
	${DISCREGRID_INCLUDE_PATH}
	${LIBIGL_INCLUDE_PATH}
)
add_library(FrictionFrenzy::CollisionObject ALIAS __ff_CollisionObject)
