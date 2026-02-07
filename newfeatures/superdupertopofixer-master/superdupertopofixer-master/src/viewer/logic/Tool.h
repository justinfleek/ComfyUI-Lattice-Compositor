#pragma once

#include <Eigen/Core>
#include <string>

#include "ViewerInterface.h"
#include "events.h"

// A tool represents a collection of interactions between the user and the scene. A tool will
// receive inputs (mouse, keyboard, etc) from the main application, and can modify the scene or
// other aspects of the application in response. The tool returns a "response" to each callback,
// indicating whether the input was ignored, had an effect, or put the tool in an "active" state.
// Once a tool is activated, it will be the sole receiver of inputs until it is deactivated.

// The main application must instantiate every tool it uses, and dispatch events to it.

// Example 1: A camera tool can respond to mouse events in order to manipulate the position of the
// camera. Example 2: A selection tool can respond to mouse and keyboard events to query scene
// objects and highlight them. Exapmle 3: A clipping plane tool can be activated with the press of a
// key, and then use mouse movement events to move the clipping plane until it is deactivated.

namespace sdtf::viewer::logic {
;

enum class ToolResponse { Activate, Deactivate, InstantAction, None };

class Tool {
 public:
	Tool(ViewerInterface* interface) : interface_(interface) {}
	virtual ~Tool() = default;

	// All callback functions can be overriden by tools in order to respond to events.
	virtual ToolResponse cursorCallback(logic::CursorEvent event) { return ToolResponse::None; }
	virtual ToolResponse mouseButtonCallback(logic::MouseButtonEvent event) {
		return ToolResponse::None;
	}
	virtual ToolResponse scrollCallback(logic::ScrollEvent event) { return ToolResponse::None; }
	virtual ToolResponse keyCallback(logic::KeyEvent event) { return ToolResponse::None; }

	// The "command" callback is a bit special in that it responds to command line commands,
	// represented as strings. If the tool indicated InstantAction or Activate, the main application
	// can then query a "CommandStatus", which will be displayed to the user. This command status can,
	// e.g., display an error message if the command was used indirectly, or another type of response.
	virtual ToolResponse commandCallback(logic::CommandEvent event) { return ToolResponse::None; }
	virtual void getCommandStatus(std::string* response) const { *response = ""; }

	// The tool status can be queries by the application at any time, and the contents will be
	// displayed to the user in a status window. If the tool has no information to share with the
	// user, an empty string should be returned.
	virtual const std::string& getToolStatus() const { return empty_string_; }

	virtual bool isActive() const = 0;

 protected:
	ViewerInterface* interface_;

 private:
	const std::string empty_string_ = "";
};

}  // namespace sdtf::viewer::logic