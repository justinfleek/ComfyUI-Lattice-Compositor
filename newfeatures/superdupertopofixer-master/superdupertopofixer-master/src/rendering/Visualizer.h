#pragma once

// clang-format off
#include <GL/glew.h>
#include <GL/glu.h>
#include <GL/glut.h>
#include <GL/gl.h>
// clang-format on

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../schemes/SDTopoFixer.h"
#include "../utilities/vec.h"

// Forward declare a class, so it can be friends with visualizers.
class ImGUIWindows;

class Visualizer {
 public:
	virtual ~Visualizer() = default;
	virtual void init(SDTopoFixer* topofixer, std::vector<Vec4d> colors) = 0;

	// Display elements based on the state.
	virtual void display() = 0;

	// Switch to the next rendering state.
	virtual void nextState() = 0;

	virtual bool isMeshChanged() const { return false; };
};