#pragma once

#include <gl/Buffer.h>

// Interface class for TriangleMesh, LineMesh, and PointSet.

namespace sdtf::viewer::gl {;

class Geometry
{
public:
	virtual GLuint vaoName() const  { return  0; }
	virtual int numVertices() const { return 0; }
	virtual int numElements() const { return 0; }
	virtual bool hasElements() const { return false; }
};

}