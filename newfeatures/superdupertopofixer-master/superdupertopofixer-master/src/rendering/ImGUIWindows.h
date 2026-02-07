#pragma once

#include "../utilities/imgui/backends/imgui_impl_glut.h"
#include "../utilities/imgui/backends/imgui_impl_opengl2.h"

class ImGUIWindows {
 public:
	ImGUIWindows() = default;
	~ImGUIWindows() = default;

	void init() const;
	void renderWindows() const;

	void reshape(int w, int h) const;
	void keyboard(char c, int x, int y) const;
	void mouse(int button, int state, int x, int y) const;
	void motion(int x, int y) const;
	void passiveMotion(int x, int y) const;

 private:
	void renderGridElementsControls() const;
	void renderDebugTree() const;
	void renderIntersectionElementsTree() const;
};
