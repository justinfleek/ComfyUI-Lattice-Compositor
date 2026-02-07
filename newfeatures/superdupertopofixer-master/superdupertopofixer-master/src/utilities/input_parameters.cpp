/* input_parameters.cpp
 *
 * Based on code by Christopher Batty, Fang Da 2014.
 * 
 * Modified by Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021
 * 
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------
#include "input_parameters.h"

#include <cassert>
#include <fstream>
#include <sstream>

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

std::map<std::string, InputParameters::Parameter> InputParameters::parameters;

//------------------------------------------------------------
// functions
//------------------------------------------------------------

void InputParameters::addStringParameter(const std::string& key, const std::string& default_value) {
	// ASSERT: check that this parameter doesn't already exist.
	assert(parameters.find(key) == parameters.end());

	Parameter p;
	p.key = key;
	p.type = STRING;
	p.str_value = default_value;

	parameters[key] = p;
}

void InputParameters::addIntegerParameter(const std::string& key, int default_value) {
	// ASSERT: check that this parameter doesn't already exist.
	assert(parameters.find(key) == parameters.end());

	Parameter p;
	p.key = key;
	p.type = INTEGER;
	p.int_value = default_value;

	parameters[key] = p;
}

void InputParameters::addDoubleParameter(const std::string& key, double default_value) {
	// ASSERT: check that this parameter doesn't already exist.
	assert(parameters.find(key) == parameters.end());

	Parameter p;
	p.key = key;
	p.type = DOUBLE;
	p.double_value = default_value;

	parameters[key] = p;
}

void InputParameters::addBooleanParameter(const std::string& key, bool default_value) {
	// ASSERT: check that this parameter doesn't already exist.
	assert(parameters.find(key) == parameters.end());

	Parameter p;
	p.key = key;
	p.type = BOOLEAN;
	p.bool_value = default_value;

	parameters[key] = p;
}

void InputParameters::parseParametersFile(std::string_view input_params_file) {
	// Set up the file input stream.
	std::ifstream fin(input_params_file.data());

	std::string line;
	while (!fin.eof()) {
		// Read a line.
		std::getline(fin, line);
		std::stringstream ss(line);

		// Read the parameter name.
		std::string key;
		ss >> key;

		// Skip comment lines and empty lines.
		if (key == "" || ss.eof() || key[0] == '#') {
			continue;
		}

		auto it = parameters.find(key);
		// ASSERT: check that a parameter with the same name has been initialized.
		assert(it != parameters.end());

		// Read the parameter value.
		switch (it->second.type) {
			case STRING:
				ss >> it->second.str_value;
				break;
			case INTEGER:
				ss >> it->second.int_value;
				break;
			case DOUBLE:
				ss >> it->second.double_value;
				break;
			case BOOLEAN:
				ss >> it->second.bool_value;
				break;
			default:
				// ASSERT: check that the type of the parameter is an allowed one.
				assert(!"ERROR: Unexpected parameter type.");
				break;
		}
	}
}

const std::string& InputParameters::getStrParam(const std::string& key) {
	// ASSERT: check that the parameter exists.
	assert(parameters.find(key) != parameters.end());
	// ASSERT: check that the parameter is of the correct type.
	assert(parameters[key].type == STRING);
	return parameters[key].str_value;
}

int InputParameters::getIntParam(const std::string& key) {
	// ASSERT: check that the parameter exists.
	assert(parameters.find(key) != parameters.end());
	// ASSERT: check that the parameter is of the correct type.
	assert(parameters[key].type == INTEGER);
	return parameters[key].int_value;
}

double InputParameters::getDoubleParam(const std::string& key) {
	// ASSERT: check that the parameter exists.
	assert(parameters.find(key) != parameters.end());
	// ASSERT: check that the parameter is of the correct type.
	assert(parameters[key].type == DOUBLE);
	return parameters[key].double_value;
}

bool InputParameters::getBoolParam(const std::string& key) {
	// ASSERT: check that the parameter exists.
	assert(parameters.find(key) != parameters.end());
	// ASSERT: check that the parameter is of the correct type.
	assert(parameters[key].type == BOOLEAN);
	return parameters[key].bool_value;
}

void InputParameters::printParameters() {
	std::cout << "-Listing input parameters:" << std::endl;
	for (const auto& parameter : parameters) {
		std::cout << parameter.first << " = ";
		switch (parameter.second.type) {
			case STRING:
				std::cout << parameter.second.str_value;
				break;
			case INTEGER:
				std::cout << parameter.second.int_value;
				break;
			case DOUBLE:
				std::cout << parameter.second.double_value;
				break;
			case BOOLEAN:
				std::cout << parameter.second.bool_value;
				break;
		}
		std::cout << std::endl;
	}
	std::cout
	    << "====================================================================================="
	    << std::endl;
}
