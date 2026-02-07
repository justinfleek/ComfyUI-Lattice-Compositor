#pragma once

#include <exception>
#include <functional>
#include <istream>
#include <map>
#include <memory>
#include <string_view>
#include <unordered_map>
#include <algorithm>
#include <cctype>

#include "TopoFixerSettings.h"

class TopoFixerSettingsParser {
 public:
	static std::unique_ptr<TopoFixerSettingsParser> fromFile(std::string_view input_path);

	void parse();
	const TopoFixerSettings& settings() const { return set_; }

 private:
	enum class LineResponse { OK, ONE_TOKEN, TOKEN_UNKNOWN, VALUE_INVALID };

	TopoFixerSettingsParser() { buildLookupTable(); }
	bool parseLine(LineResponse* response);

	void buildLookupTable();

	static bool parseIntParam(int* param, std::string&& str);
	static bool parseDoubleParam(double* param, std::string&& str);
        static bool parseBoolParam(bool* param, std::string&& str);
	static bool parseStringParam(std::string* param, std::string&& str);

	template <typename T>
	static bool parseEnumParam(T* param, std::map<std::string, T>&& map, std::string&& str) {
		auto it = map.find(str);
		if (it == map.end())
			return false;
		*param = it->second;
		return true;
	}

	std::unique_ptr<std::istream> is_;
	TopoFixerSettings set_;

	std::unordered_map<std::string, std::function<bool(std::string&& l)>> property_setter_map_;
};
