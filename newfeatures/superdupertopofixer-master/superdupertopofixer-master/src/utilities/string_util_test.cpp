#include "string_util.h"

#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include "doctest/doctest.h"

TEST_CASE("split correctly splits strings") {
	SUBCASE("empty string") {
		std::vector<std::string> tokens = split("", ".");
		REQUIRE_EQ(tokens.size(), 1);
		CHECK_EQ(tokens[0], "");
	}

	SUBCASE("no delimiter") {
		std::string test = "test_string";
		std::vector<std::string> tokens = split(test, ".");
		REQUIRE_EQ(tokens.size(), 1);
		CHECK_EQ(tokens[0], test);
	}

	SUBCASE("delimiter in the middle") {
		std::string test = "test.string";
		std::vector<std::string> tokens = split(test, ".");
		REQUIRE_EQ(tokens.size(), 2);
		CHECK_EQ(tokens[0], "test");
		CHECK_EQ(tokens[1], "string");
	}

	SUBCASE("delimiter in the beginning") {
		std::string test = ".teststring";
		std::vector<std::string> tokens = split(test, ".");
		REQUIRE_EQ(tokens.size(), 2);
		CHECK_EQ(tokens[0], "");
		CHECK_EQ(tokens[1], "teststring");
	}

	SUBCASE("delimiter in the end") {
		std::string test = "teststring.";
		std::vector<std::string> tokens = split(test, ".");
		REQUIRE_EQ(tokens.size(), 2);
		CHECK_EQ(tokens[0], "teststring");
		CHECK_EQ(tokens[1], "");
	}

	SUBCASE("multiple delimiters") {
		std::string test = "test.string.big";
		std::vector<std::string> tokens = split(test, ".");
		REQUIRE_EQ(tokens.size(), 3);
		CHECK_EQ(tokens[0], "test");
		CHECK_EQ(tokens[1], "string");
		CHECK_EQ(tokens[2], "big");
	}

	SUBCASE("multicharacter delimiter") {
		std::string test = "test.+string";
		std::vector<std::string> tokens = split(test, ".+");
		REQUIRE_EQ(tokens.size(), 2);
		CHECK_EQ(tokens[0], "test");
		CHECK_EQ(tokens[1], "string");
	}
}