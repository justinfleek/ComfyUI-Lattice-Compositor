#pragma once

#include <filesystem>
#include <string>

#include "Tool.h"
#include "datastructures/Mesh3DInterface.h"

namespace sdtf::viewer::logic {
;

class AnimationTool : public Tool {
 public:
	AnimationTool(ViewerInterface* interface, Mesh3DInterface* mesh,
	              const std::filesystem::path& current_mesh_path);

	virtual ToolResponse cursorCallback(logic::CursorEvent event) override;
	virtual ToolResponse mouseButtonCallback(logic::MouseButtonEvent event) override;
	virtual ToolResponse scrollCallback(logic::ScrollEvent event) override;
	virtual ToolResponse keyCallback(logic::KeyEvent event) override;

	virtual const std::string& getToolStatus() const override { return status_; }

	virtual bool isActive() const override;

	bool isEnabled() const { return state_ == State::Enabled; }
	void setEnabled(bool is_enabled);

	bool pollUpdated();

	int getCurrentFrame() { return current_frame_; }
	bool isLastFrame() { return current_frame_ == max_frame_; }
	void advanceFrame();

 private:
	void updateMesh();
	void updateStatus();

	bool splitFilename(const std::filesystem::path& filename, std::filesystem::path& prefix,
	                   int& frame_num, std::filesystem::path& suffix);

	std::filesystem::path buildFullPath(const std::filesystem::path& prefix, const int& frame_num,
	                                    const std::filesystem::path& suffix) const;

	enum class State { Disabled, Enabled, Error };

	std::filesystem::path dir_;
	std::filesystem::path file_prefix_;
	std::filesystem::path file_suffix_;

	int min_frame_;
	int max_frame_;
	int current_frame_;

	std::string status_;

	State state_ = State::Disabled;
	bool is_updated_ = false;

	Mesh3DInterface* mesh_;
};

}  // namespace sdtf::viewer::logic
