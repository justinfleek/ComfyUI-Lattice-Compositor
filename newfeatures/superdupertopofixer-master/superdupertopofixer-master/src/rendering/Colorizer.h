/* RenderingPrimitives.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header for the virtual parent class of Colorizer classes, which determine triangle
 * colors based on different modes and states of rendering.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "../datastructures/Mesh3DTriangle.h"
#include "../schemes/SDTopoFixer.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// Forward declare a class, so it can be a friend in child colorizers.
class ImGUIWindows;

class Colorizer {
 public:
	virtual ~Colorizer() = default;

	// Initializes a colorizer, which is used to assign colors to triangles. Some colorizers are made
	// to modify a specific visual aspect, such as transparency or highlighting of a specific region.
	// In these cases, `prev_colorizer` is used to retrieve the base triangle color.
	virtual void init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) = 0;

	// Return color on the input `triangle`.
	virtual Vec4d getFrontColor(Mesh3DTriangle* triangle) = 0;
	virtual Vec4d getBackColor(Mesh3DTriangle* triangle) = 0;
	virtual Vec4d getOutlineColor(Mesh3DTriangle* triangle) = 0;

	// Switch to the next coloring state.
	virtual void nextState() = 0;

	virtual bool isMeshChanged() const { return false; }
};