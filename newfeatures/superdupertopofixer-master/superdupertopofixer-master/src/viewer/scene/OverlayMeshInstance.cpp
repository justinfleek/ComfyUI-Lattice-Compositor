#include "scene/OverlayMeshInstance.h"

namespace sdtf::viewer::scene
{;

OverlayMeshInstance::OverlayMeshInstance(gl::TriangleMesh* mesh, Node* node)
	: mesh_(mesh), node_(node)
{

}

}