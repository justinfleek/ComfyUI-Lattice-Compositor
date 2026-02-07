/* MeshColorizers.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for classes that determine triangle colors based on different
 * modes and states of rendering.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "MeshColorizers.h"

//------------------------------------------------------------
// MaterialColorizer functions
//------------------------------------------------------------

void MaterialColorizer::init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) {
	prev_colorizer_ = prev_colorizer;
}

void MaterialColorizer::setMaterialColors(std::vector<Vec4d> material_colors) {
	material_colors_ = std::move(material_colors);
}

void MaterialColorizer::setOutlineColor(Vec4d color) { outline_color_ = color; }

Vec4d MaterialColorizer::getFrontColor(Mesh3DTriangle* triangle) {
	assert(material_colors_.size());
	return material_colors_.at(triangle->getLabel(false) % material_colors_.size());
}

Vec4d MaterialColorizer::getBackColor(Mesh3DTriangle* triangle) {
	assert(material_colors_.size());
	return material_colors_.at(triangle->getLabel(true) % material_colors_.size());
}

Vec4d MaterialColorizer::getOutlineColor(Mesh3DTriangle* triangle) { return outline_color_; }

//------------------------------------------------------------
// SelectionColorizer functions
//------------------------------------------------------------

void SelectionColorizer::init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) {
	prev_colorizer_ = prev_colorizer;
}

void SelectionColorizer::setSelectedTriangles(absl::flat_hash_set<Mesh3DTriangle*> triangles) {
	triangles_ = std::move(triangles);
}

Vec4d SelectionColorizer::getFrontColor(Mesh3DTriangle* triangle) {
	assert(prev_colorizer_ != nullptr);
	Vec4d result = prev_colorizer_->getFrontColor(triangle);
	if (triangles_.find(triangle) == triangles_.end()) {
		result[3] = alpha_;
	} else {
		result[3] = 1.0;
	}
	return result;
}

Vec4d SelectionColorizer::getBackColor(Mesh3DTriangle* triangle) {
	assert(prev_colorizer_ != nullptr);
	Vec4d result = prev_colorizer_->getBackColor(triangle);
	if (triangles_.find(triangle) == triangles_.end()) {
		result[3] = alpha_;
	} else {
		result[3] = 1.0;
	}
	return result;
}

Vec4d SelectionColorizer::getOutlineColor(Mesh3DTriangle* triangle) {
	assert(prev_colorizer_ != nullptr);
	Vec4d result = prev_colorizer_->getOutlineColor(triangle);
	if (triangles_.find(triangle) == triangles_.end()) {
		result[3] = alpha_;
	} else {
		result[3] = 1.0;
	}
	return result;
}

//------------------------------------------------------------
// CellSeparationColorizer functions
//------------------------------------------------------------

void CellSeparationColorizer::init(SDTopoFixer* topofixer, Colorizer* prev_colorizer) {
	auto inside_tris = topofixer->getCellSeparator()->get_inside_triangles();
	inside_triangles_ = {inside_tris.begin(), inside_tris.end()};
	auto outside_tris = topofixer->getCellSeparator()->get_outside_triangles();
	outside_triangles_ = {outside_tris.begin(), outside_tris.end()};
	prev_colorizer_ = prev_colorizer;
}

void CellSeparationColorizer::setHighlightColor(Vec4d color) { highlight_color_ = color; }

Vec4d CellSeparationColorizer::getFrontColor(Mesh3DTriangle* triangle) {
	if (current_state_ == 1 && inside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	if (current_state_ == 2 && outside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	return prev_colorizer_->getFrontColor(triangle);
}

Vec4d CellSeparationColorizer::getBackColor(Mesh3DTriangle* triangle) {
	if (current_state_ == 1 && inside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	if (current_state_ == 2 && outside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	return prev_colorizer_->getBackColor(triangle);
}

Vec4d CellSeparationColorizer::getOutlineColor(Mesh3DTriangle* triangle) {
	if (current_state_ == 1 && inside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	if (current_state_ == 2 && outside_triangles_.count(triangle)) {
		return highlight_color_;
	}
	return prev_colorizer_->getOutlineColor(triangle);
}

void CellSeparationColorizer::nextState() { current_state_ = (current_state_ + 1) % kMaxStates; }

bool CellSeparationColorizer::isMeshChanged() const {
	if (prev_state_ != current_state_) {
		prev_state_ = current_state_;
		return true;
	}
	return false;
}
