#pragma once

namespace sdtf::viewer::logic {
;

// Event structs that collect all data about input events, such as key presses, mouse movement etc

struct MouseButtonEvent {
	int button;
	int action;
	int mods;
	double xpos;
	double ypos;

	MouseButtonEvent(int button, int action, int mods, double xpos, double ypos)
	    : button(button), action(action), mods(mods), xpos(xpos), ypos(ypos) {}

	MouseButtonEvent() = default;
};

struct ScrollEvent {
	double xoffset;
	double yoffset;

	ScrollEvent(double xoffset, double yoffset) : xoffset(xoffset), yoffset(yoffset) {}

	ScrollEvent() = default;
};

struct KeyEvent {
	int key;
	int scancode;
	int action;
	int mods;

	KeyEvent(int key, int scancode, int action, int mods)
	    : key(key), scancode(scancode), action(action), mods(mods) {}

	KeyEvent() = default;
};

struct CursorEvent {
	double xpos;
	double ypos;

	CursorEvent(double xpos, double ypos) : xpos(xpos), ypos(ypos) {}

	CursorEvent() = default;
};

struct CommandEvent {
	std::string command;

	CommandEvent(const std::string& command) : command(command) {}
	CommandEvent() = default;
};

struct WindowSizeEvent {
	int width;
	int height;

	WindowSizeEvent(int width, int height) : width(width), height(height) {}

	WindowSizeEvent() = default;
};

}  // namespace sdtf::viewer::logic