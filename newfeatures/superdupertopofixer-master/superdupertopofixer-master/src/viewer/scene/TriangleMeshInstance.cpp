#include "scene/TriangleMeshInstance.h"

namespace sdtf::viewer::scene
{;

TriangleMeshInstance::TriangleMeshInstance(gl::TriangleMesh* mesh, Node* node)
	: mesh_(mesh), node_(node)
{

}

}