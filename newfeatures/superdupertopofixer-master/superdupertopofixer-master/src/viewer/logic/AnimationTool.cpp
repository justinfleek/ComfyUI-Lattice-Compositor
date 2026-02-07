#include "AnimationTool.h"

#include <filesystem>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>

#include "../../datastructures/mesh_io/ObjFileHandler.h"
#include "include_glfw.h"
#include "logic/Tool.h"

namespace sdtf::viewer::logic {
;

AnimationTool::AnimationTool(ViewerInterface* interface, Mesh3DInterface* mesh,
                             const std::filesystem::path& current_mesh_path)
    : Tool(interface), mesh_(mesh) {
	dir_ = current_mesh_path.parent_path();

	std::filesystem::path filename = current_mesh_path.filename();
	if (bool ok = splitFilename(filename, file_prefix_, current_frame_, file_suffix_); !ok) {
		state_ = State::Error;
		updateStatus();
		return;
	}

	min_frame_ = std::numeric_limits<int>::max();
	max_frame_ = std::numeric_limits<int>::min();
	for (auto& iter : std::filesystem::directory_iterator(dir_)) {
		std::filesystem::path filename = iter.path().filename();
		if (filename.extension() != file_suffix_) {
			continue;
		}

		std::filesystem::path dummy_prefix;
		std::filesystem::path dummy_suffix;
		int frame_num;
		if (bool ok = splitFilename(filename, dummy_prefix, frame_num, dummy_suffix); !ok) {
			continue;
		}
		min_frame_ = std::min(min_frame_, frame_num);
		max_frame_ = std::max(max_frame_, frame_num);
	}
	state_ = State::Enabled;
	updateStatus();
}

ToolResponse AnimationTool::cursorCallback(logic::CursorEvent event) { return ToolResponse::None; }
ToolResponse AnimationTool::mouseButtonCallback(logic::MouseButtonEvent event) {
	return ToolResponse::None;
}
ToolResponse AnimationTool::scrollCallback(logic::ScrollEvent event) { return ToolResponse::None; }
ToolResponse AnimationTool::keyCallback(logic::KeyEvent event) {
	if (event.action == GLFW_RELEASE) {
		return ToolResponse::None;
	}

	if (event.key == GLFW_KEY_RIGHT) {
		current_frame_ = std::min(max_frame_, current_frame_ + 1);
		updateMesh();
		return ToolResponse::InstantAction;
	} else if (event.key == GLFW_KEY_LEFT) {
		current_frame_ = std::max(min_frame_, current_frame_ - 1);
		updateMesh();
		return ToolResponse::InstantAction;
	} else if (event.key == GLFW_KEY_DOWN) {
		current_frame_ = max_frame_;
		updateMesh();
		return ToolResponse::InstantAction;
	} else if (event.key == GLFW_KEY_UP) {
		current_frame_ = min_frame_;
		updateMesh();
		return ToolResponse::InstantAction;
	}
	return ToolResponse::None;
}

bool AnimationTool::isActive() const { return false; }

void AnimationTool::setEnabled(bool is_enabled) {
	if (state_ != State::Error) {
		state_ = is_enabled ? State::Enabled : State::Disabled;
		updateStatus();
	}
}

bool AnimationTool::pollUpdated() {
	if (is_updated_) {
		is_updated_ = false;
		return true;
	}
	return false;
}

void AnimationTool::advanceFrame() {
	if (isLastFrame()) {
		return;
	}
	current_frame_++;
	updateMesh();
}

void AnimationTool::updateMesh() {
	std::filesystem::path file = buildFullPath(file_prefix_, current_frame_, file_suffix_);
	if (file_suffix_.string() == ".bin") {
		mesh_->loadBinary(file.string());
	} else if (file_suffix_.string() == ".obj") {
		std::cout << "Verts: " << mesh_->ListVertices().size() << std::endl;
		ObjFileHandler obj_handler;
		obj_handler.readFromFile(mesh_, file);
		std::cout << "Verts: " << mesh_->ListVertices().size() << std::endl;
	}
	updateStatus();
	is_updated_ = true;
}

void AnimationTool::updateStatus() {
	if (state_ == State::Enabled) {
		status_ = "Rendering: ";
		status_ += buildFullPath(file_prefix_, current_frame_, file_suffix_);
	} else if (state_ == State::Disabled) {
		status_ = "";
	} else if (state_ == State::Error) {
		status_ = "Error during rendering at the following path [" + dir_.string() + "]";
	}
}

bool AnimationTool::splitFilename(const std::filesystem::path& filename,
                                  std::filesystem::path& prefix, int& frame_num,
                                  std::filesystem::path& suffix) {
	suffix = filename.extension();
	if (suffix.empty()) {
		return false;
	}
	std::filesystem::path stem = filename.stem();

	std::filesystem::path num_ext = stem.extension();
	if (num_ext.empty()) {
		return false;
	}

	std::string num_str = num_ext.string().substr(1);
	try {
		frame_num = std::stoi(num_str);
	} catch (const std::invalid_argument& ex) {
		return false;
	} catch (const std::out_of_range& ex) {
		return false;
	}

	prefix = stem.stem();
	return true;
}

std::filesystem::path AnimationTool::buildFullPath(const std::filesystem::path& prefix,
                                                   const int& frame_num,
                                                   const std::filesystem::path& suffix) const {
	std::filesystem::path filename = prefix;
	filename += "." + std::to_string(frame_num);
	filename += suffix;
	return dir_ / filename;
}

}  // namespace sdtf::viewer::logic