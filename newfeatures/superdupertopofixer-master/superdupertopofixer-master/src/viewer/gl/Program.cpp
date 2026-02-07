#include "gl/Program.h"

#include <iostream>
#include <cassert>


namespace sdtf::viewer::gl {
;

Program::Program(std::string user_name)
	: user_name_(user_name)
{}


void Program::use() const
{
	glUseProgram(name_);
}

GLint Program::getUniformLocation(const char* uniformName) const
{
	return glGetUniformLocation(name_, uniformName);
}

std::unique_ptr<Program> Program::empty(std::string user_name)
{
	auto ret = std::unique_ptr<Program>(new Program(user_name));

	ret->name_ = glCreateProgram();
	ret->created_ = true;

	return ret;
}

std::unique_ptr<Program> Program::makeStandard(std::string user_name, const std::string& vs_file,
	const std::string& fs_file)
{
	auto ret = empty(user_name);
	ret->attach(GL_VERTEX_SHADER, vs_file);
	ret->attach(GL_FRAGMENT_SHADER, fs_file);
	return ret;
}

void Program::attach(std::unique_ptr<Shader> shader) {
	shaders_owned_.push_back(std::move(shader));
}

void Program::attach(GLenum shaderType, const std::string& file) {
	shaders_owned_.push_back(Shader::fromFile(shaderType, file));
}

bool Program::link()
{
	if (linked_)
		return true;

	bool all_compiled = true;
	for (int i = 0; i < shaders_owned_.size(); i++)
	{
		all_compiled &= shaders_owned_[i]->compile();
		glAttachShader(name_, shaders_owned_[i]->name());
	}

	assert(all_compiled);
	glLinkProgram(name_);

	GLint status;
	glGetProgramiv(name_, GL_LINK_STATUS, &status);

	GLint length;
	glGetProgramiv(name_, GL_INFO_LOG_LENGTH, &length);

	linked_ = (status == GL_TRUE);

	if (length > 1)
	{
		char* log = new char[length];
		glGetProgramInfoLog(name_, length, NULL, log);

		std::cout << "Program " << user_name_ << ": ";
		std::cout << ((status != GL_TRUE) ? "Link failed!" : "") << std::endl;

		std::cout << log << std::endl;
		delete[] log;
	}
	
	return linked_;
}

void Program::clear()
{
	if (created_)
	{
		glDeleteProgram(name_);
	}
	for (int i = 0; i < shaders_owned_.size(); i++)
		shaders_owned_[i]->clear();

	created_ = false;
	name_ = -1;
}

Program::~Program()
{
	if (created_)
		clear();
}

}