/* RenderingPrimitives.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header for the classes that determine triangle colors based on different
 * modes and states of rendering
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <unordered_set>

#include "../datastructures/Mesh3DTriangle.h"
#include "../schemes/SDTopoFixer.h"
#include "../utilities/vec.h"
#include "Colorizer.h"
#include "ImGUIWindows.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// Basic colorizer, stores data for assigning colors to triangles, namely a triangle is colored by
// its material labels.
class MaterialColorizer : public Colorizer {
 public:
	// Sets the `prev_colorizer_` pointer.
	virtual void init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) override;

	void setMaterialColors(std::vector<Vec4d> material_colors);
	void setOutlineColor(Vec4d color);

	// Returns color corresponding to the label on the 0-side of the input triangle.
	virtual Vec4d getFrontColor(Mesh3DTriangle* triangle) override;
	// Returns color corresponding to the label on the 1-side of the input triangle.
	virtual Vec4d getBackColor(Mesh3DTriangle* triangle) override;
	// Returns `outline_color_`.
	virtual Vec4d getOutlineColor(Mesh3DTriangle* triangle) override;

	// There is only one state, material colors are always returned.
	virtual void nextState() override{};

 private:
	Colorizer* prev_colorizer_ = nullptr;
	std::vector<Vec4d> material_colors_;
	Vec4d outline_color_;
};

// Colorizer used to emphasize color in the region around a selected triangle by setting the
// transparancy for other triangles to a given `alpha_` value. When no triangle is selected for
// visualization, the alpha value of the entire mesh is set to `alpha_` (therefore possibly making
// it fully transparent). `alpha_` takes values between the initial 1.0 (fully opaque), and 0.0
// (fully transparent), and is only changed by an imgui slider.
class SelectionColorizer : public Colorizer {
	friend ImGUIWindows;

 public:
	// Sets the `prev_colorizer_` pointer.
	virtual void init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) override;

	void setSelectedTriangles(absl::flat_hash_set<Mesh3DTriangle*> triangles);

	// Looks up front color of `triangle`/back color of `triangle`/outline color in `prev_colorizer_`,
	// overwrites its alpha value with `alpha_`, and returns the color vector.
	virtual Vec4d getFrontColor(Mesh3DTriangle* triangle) override;
	virtual Vec4d getBackColor(Mesh3DTriangle* triangle) override;
	virtual Vec4d getOutlineColor(Mesh3DTriangle* triangle) override;

	// There is only one state, material colors are always returned.
	virtual void nextState() override{};

 private:
	Colorizer* prev_colorizer_ = nullptr;
	// Transparency value that is used when returning front/back/outline color. Takes values between
	// the initial 1.0 (fully opaque), and 0.0 (fully transparent). Only changed by an imgui slider.
	float alpha_ = 1.0;

	// A set of triangles that will be kept fully visible and not affected by the `alpha_`.
	absl::flat_hash_set<Mesh3DTriangle*> triangles_;
};

// Debug colorizer that, based on the current state, sets a highlight color to triangles detected
// inside/outside bad cell region, or returns front/back/outline colors from `prev_colorizer_`.
// Current state is accessed by imgui.
class CellSeparationColorizer : public Colorizer {
	friend ImGUIWindows;

 public:
	// Sets the `prev_colorizer_` pointer, populates `inside_triangles_` and `outside_triangles_`.
	virtual void init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) override;
	void setHighlightColor(Vec4d color);

	// Either returns `highlight_color_` (when `triangle` is to be highlighted according to the
	// current state), or returns front color of `triangle`/back color of `triangle`/outline color in
	// `prev_colorizer_`.
	virtual Vec4d getFrontColor(Mesh3DTriangle* triangle) override;
	virtual Vec4d getBackColor(Mesh3DTriangle* triangle) override;
	virtual Vec4d getOutlineColor(Mesh3DTriangle* triangle) override;

	// State 0: no highlighting.
	// State 1: highlight inside triangles.
	// State 2: highlight outside triangles.
	virtual void nextState() override;
	virtual bool isMeshChanged() const override;

 private:
	absl::flat_hash_set<Mesh3DTriangle*> inside_triangles_;
	absl::flat_hash_set<Mesh3DTriangle*> outside_triangles_;
	Vec4d highlight_color_;
	Colorizer* prev_colorizer_ = nullptr;
	int current_state_ = 0;
	mutable int prev_state_ = 0;
	const int kMaxStates = 3;
};