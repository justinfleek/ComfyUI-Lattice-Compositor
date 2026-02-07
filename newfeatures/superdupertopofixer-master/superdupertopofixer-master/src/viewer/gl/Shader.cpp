#include "gl/Shader.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <cassert>

namespace sdtf::viewer::gl {;

std::unique_ptr<Shader> Shader::empty(GLenum shader_type)
{
	auto ret = std::unique_ptr<Shader>(new Shader());
	ret->shader_type_ = shader_type;

	ret->name_ = glCreateShader(shader_type);
	ret->created_ = true;

	return ret;
}

std::unique_ptr<Shader> Shader::fromString(GLenum shader_type, const std::string& source)
{
	auto ret = Shader::empty(shader_type);
	ret->code_ = source;

	ret->setShaderSourceFromCode();
	ret->source_status_ = SOURCE_SET_FROM_STRING;

	return ret;
}


std::unique_ptr<Shader> Shader::fromFile(GLenum shader_type, const std::string& path)
{
	auto ret = Shader::empty(shader_type);

	ret->setShaderSourceFromFile(path);
	ret->source_status_ = SOURCE_SET_FROM_FILE;

	return ret;
}

void Shader::setShaderSourceFromCode()
{
	auto str_ptr = code_.data();
	auto len = static_cast<GLint>(code_.length());
	glShaderSource(name_, 1, &str_ptr, &len);

	compiled_ = false;
}

void Shader::setShaderSourceFromFile(const std::string& path)
{
	path_ = path;

	std::ifstream t(path);
	std::stringstream buffer;
	buffer << t.rdbuf();
	code_ = buffer.str();

	setShaderSourceFromCode();
}

bool Shader::compile()
{
	if (compiled_)
		return true;

	assert(source_status_ != SOURCE_NOT_SET);

	glCompileShader(name_);
	GLint status;
	glGetShaderiv(name_, GL_COMPILE_STATUS, &status);

	GLint length;
	glGetShaderiv(name_, GL_INFO_LOG_LENGTH, &length);
	compiled_ = (status == GL_TRUE);

	if (length > 1)
	{
		char* log = new char[length];
		glGetShaderInfoLog(name_, length, NULL, log);
		if (std::string(log).find("No errors.") == std::string::npos)
		{
			if (source_status_ == SOURCE_SET_FROM_FILE)
				std::cout << "Shader " << path_ << ": ";
			else
				std::cout << "Shader: ";

			std::cout << ((status == GL_TRUE) ? "" : "Compilation failed!") << std::endl;

			std::cout << log << std::endl;
		}
		delete[] log;
	}

	return compiled_;
}

void Shader::clear()
{
	if (created_)
	{
		glDeleteShader(name_);
	}
	name_ = -1;
	created_ = false;
	code_ = "";
	compiled_ = false;
}

Shader::~Shader()
{
	if (created_)
		clear();
}

}