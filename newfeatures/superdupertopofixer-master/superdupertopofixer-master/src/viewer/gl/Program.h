#pragma once

#include <string>
#include <vector>

#include "Shader.h"

// Wrapper for an OpenGL shader program. Attach Shader objects to it before linking.

namespace sdtf::viewer::gl {
;

class Program {
 public:
	// Generate empty shader program. Need to attach Shader objects to it before linking
	static std::unique_ptr<Program> empty(std::string user_name);
	// Convenience function for loading source code for a vertex shader and fragment shader, and
	// attaching them to this program.
	static std::unique_ptr<Program> makeStandard(std::string user_name, const std::string& vs_file,
	                                             const std::string& fs_file);

	// Delete program from GPU, along with the shader objects
	void clear();
	~Program();

	// Attach shader object to program
	void attach(std::unique_ptr<Shader> shader);
	// Load source code from file and attach to program
	void attach(GLenum shaderType, const std::string& file);

	// Links the program (and compiles any non-compiled shaders before that)
	bool link();

	// Use the shader program on the GPU (needs to be linked to succeed)
	void use() const;
	GLint getUniformLocation(const char* uniformName) const;

 private:
	Program(std::string user_name = "Unnamed");

	std::vector<std::unique_ptr<Shader>> shaders_owned_;

	GLuint name_ = -1;
	std::string user_name_;
	bool created_ = false;
	bool linked_ = false;
};

}  // namespace sdtf::viewer::gl