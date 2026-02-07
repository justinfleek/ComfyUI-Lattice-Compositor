/* input_parameters.h
 *
 * Based on code by Christopher Batty, Fang Da 2014.
 *
 * Modified by Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021
 *
 * This header defines a class to parse and store input parameter options.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <iostream>
#include <map>
#include <string>
#include <string_view>

//------------------------------------------------------------
// classes
//------------------------------------------------------------

class InputParameters {
 public:
	// Allowed types of input parameters that can be read from a file.
	enum Type {
		STRING,
		INTEGER,
		DOUBLE,
		BOOLEAN,

		TYPE_COUNT
	};

	// Functions that add parameters of different types. `key` is the name of the parameter,
	// `default_value` is the value that will be used, unless the parameter is specified in the input
	// parameter file, or is read from the command line.
	static void addStringParameter(const std::string& key, const std::string& default_value);
	static void addIntegerParameter(const std::string& key, int defaut_value);
	static void addDoubleParameter(const std::string& key, double default_value);
	static void addBooleanParameter(const std::string& key, bool default_value);

	// Function to read `input_params_file`, and assign parameter values. All parameters have to first
	// be initialized by the add function above.
	static void parseParametersFile(std::string_view input_params_file);

	// Functions to access stored parameters via their names.
	static const std::string& getStrParam(const std::string& key);
	static int getIntParam(const std::string& key);
	static double getDoubleParam(const std::string& key);
	static bool getBoolParam(const std::string& key);

	static void printParameters();

 protected:
	// For a parameter, this class holds its name `key`, its Type `type`, and its value.
	class Parameter {
	 public:
		std::string key;
		Type type;

		std::string str_value;
		int int_value;
		double double_value;
		bool bool_value;
	};

 public:
	// Maps each parameter's name to its Type.
	static std::map<std::string, Parameter> parameters;
};
