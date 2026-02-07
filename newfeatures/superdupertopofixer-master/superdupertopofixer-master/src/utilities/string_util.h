#pragma once

#include <algorithm>
#include <cctype>
#include <locale>
#include <vector>

// trim from start (in place)
inline void ltrim(std::string& s) {
	s.erase(s.begin(),
	        std::find_if(s.begin(), s.end(), [](unsigned char ch) { return !std::isspace(ch); }));
}

// trim from end (in place)
inline void rtrim(std::string& s) {
	s.erase(
	    std::find_if(s.rbegin(), s.rend(), [](unsigned char ch) { return !std::isspace(ch); }).base(),
	    s.end());
}

inline void trim(std::string& s) {
	rtrim(s);
	ltrim(s);
}

inline std::vector<std::string> tokenize(std::string s) {
	std::vector<std::string> ret;
	trim(s);
	while (!s.empty()) {
		if (s[0] == '"' && s.size() > 1) {
			auto closing_quote =
			    std::find_if(s.begin() + 1, s.end(), [](unsigned char ch) { return ch == '"'; });
			ret.push_back(std::string(s.begin() + 1, closing_quote));
			if (closing_quote == s.end()) {
				return ret;
			}

			s.erase(s.begin(), closing_quote + 1);
			ltrim(s);
		} else {
			auto first_space =
			    std::find_if(s.begin(), s.end(), [](unsigned char ch) { return std::isspace(ch); });
			ret.push_back(std::string(s.begin(), first_space));
			s.erase(s.begin(), first_space);
			ltrim(s);
		}
	}
	return ret;
}

inline std::vector<std::string> split(const std::string& s, const std::string& delim) {
	std::vector<std::string> result;

	std::string::size_type prev_idx = 0;
	while (prev_idx != s.npos) {
		std::string::size_type idx = s.find(delim, prev_idx);
		result.emplace_back(s.substr(prev_idx, idx - prev_idx));
		prev_idx = idx;
		if (idx != s.npos) {
			prev_idx += delim.size();
		}
	}
	return result;
}