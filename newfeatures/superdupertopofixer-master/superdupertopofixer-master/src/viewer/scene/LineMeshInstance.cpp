#include "scene/LineMeshInstance.h"

namespace sdtf::viewer::scene
{;

LineMeshInstance::LineMeshInstance(gl::LineMesh* mesh, Node* node)
	: mesh_(mesh), node_(node)
{

}

}