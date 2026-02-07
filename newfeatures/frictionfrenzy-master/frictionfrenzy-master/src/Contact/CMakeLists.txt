# add_subdirectory(ContactGenerator)
add_library(__ff_Contact STATIC
    BroadPhase.h
    BroadPhase.cpp
    ContactCache.h
    ContactInfo.h
	ContactGenerator/ContactGeneratorBase.h
	ContactGenerator/MeshMeshContactGenerator.cpp
	ContactGenerator/SphereSphereContactGenerator.cpp
)
add_dependencies(__ff_Contact
    fcl
)
target_link_libraries(__ff_Contact
    OpenMP::OpenMP_CXX
	FrictionFrenzy::CollisionObject
    ${FCL_LIBRARY}
    ${CCD_LIBRARY}
)
target_include_directories(__ff_Contact PUBLIC
	${FRICTION_COMMON_DIR}
)

add_library(FrictionFrenzy::Contact ALIAS __ff_Contact)
