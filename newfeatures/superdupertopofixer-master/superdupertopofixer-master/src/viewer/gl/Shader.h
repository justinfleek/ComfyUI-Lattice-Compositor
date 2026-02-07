#pragma once

#include <glad/glad.h>

#include <string>
#include <memory>

// Wrapper for OpenGL shader stage

namespace sdtf::viewer::gl {;

class Shader
{
public:
	// Generate shader stage by setting source code from string or file
	static std::unique_ptr<Shader> fromString(GLenum shader_type, const std::string& source);
	static std::unique_ptr<Shader> fromFile(GLenum shader_type, const std::string& path);

	void clear();
	~Shader();

	//void setSource(const std::string& source);
	//void setSourceFromFile(const std::string& file);

	bool compile();
	//void reloadSourceFromFile();

	// Returns the shader object ID used to represent it on the GPU
	inline GLuint name() const { return name_; }
	inline bool compiled() const { return compiled_; }

private:
	static std::unique_ptr<Shader> empty(GLenum shader_type);
	Shader() = default;

	void setShaderSourceFromCode();
	void setShaderSourceFromFile(const std::string& path);

	bool created_ = false;
	GLuint name_ = -1;
	std::string code_ = "";
	std::string path_ = "";
	GLenum shader_type_;

	enum SourceStatusType { SOURCE_NOT_SET, SOURCE_SET_FROM_STRING, SOURCE_SET_FROM_FILE } ;
	SourceStatusType source_status_ = SOURCE_NOT_SET;

	bool compiled_ = false;
};

}