// s4-runtime // tests/unit/test_generator.cpp
// Unit tests for Generator coroutine.
#include <catch2/catch_test_macros.hpp>

#include <s4/core/generator.h>

#include <algorithm>
#include <numeric>
#include <ranges>
#include <stdexcept>
#include <string>
#include <vector>

using namespace s4::core;

// Simple generator that yields integers.
Generator<int> count_to(int n) {
  for (int i = 0; i < n; ++i) {
    co_yield i;
  }
}

// Generator that yields references.
Generator<int&> mutable_range(std::vector<int>& vec) {
  for (auto& elem : vec) {
    co_yield elem;
  }
}

// Generator that throws.
Generator<int> throw_after(int n) {
  for (int i = 0; i < n; ++i) {
    co_yield i;
  }
  throw std::runtime_error("Expected error");
}

// Recursive generator (flattening).
Generator<int> flatten_ranges(std::vector<std::vector<int>>& vecs) {
  for (auto& vec : vecs) {
    for (auto& elem : vec) {
      co_yield elem;
    }
  }
}

TEST_CASE("Generator basic iteration", "[generator]") {
  SECTION("count to 5") {
    std::vector<int> result;
    for (int x : count_to(5)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int>{0, 1, 2, 3, 4});
  }
  
  SECTION("count to 0 yields nothing") {
    std::vector<int> result;
    for (int x : count_to(0)) {
      result.push_back(x);
    }
    
    REQUIRE(result.empty());
  }
  
  SECTION("single element") {
    std::vector<int> result;
    for (int x : count_to(1)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int>{0});
  }
}

TEST_CASE("Generator reference yielding", "[generator]") {
  std::vector<int> data{1, 2, 3, 4, 5};
  
  SECTION("can read via reference") {
    std::vector<int> result;
    for (int& x : mutable_range(data)) {
      result.push_back(x);
    }
    
    REQUIRE(result == data);
  }
  
  SECTION("can modify via reference") {
    for (int& x : mutable_range(data)) {
      x *= 2;
    }
    
    REQUIRE(data == std::vector<int>{2, 4, 6, 8, 10});
  }
}

TEST_CASE("Generator exception propagation", "[generator]") {
  SECTION("exception thrown during iteration") {
    std::vector<int> result;
    
    REQUIRE_THROWS_AS([&]() {
      for (int x : throw_after(3)) {
        result.push_back(x);
      }
    }(), std::runtime_error);
    
    // Should have collected elements before the throw.
    REQUIRE(result == std::vector<int>{0, 1, 2});
  }
}

TEST_CASE("Generator move semantics", "[generator]") {
  SECTION("can move generator") {
    auto gen1 = count_to(5);
    auto gen2 = std::move(gen1);
    
    std::vector<int> result;
    for (int x : gen2) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int>{0, 1, 2, 3, 4});
  }
  
  SECTION("move assignment") {
    auto gen1 = count_to(3);
    auto gen2 = count_to(2);
    
    gen2 = std::move(gen1);
    
    std::vector<int> result;
    for (int x : gen2) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int>{0, 1, 2});
  }
}

TEST_CASE("Generator nested/flattening", "[generator]") {
  std::vector<std::vector<int>> vecs{{1, 2}, {3}, {4, 5, 6}};
  
  std::vector<int> result;
  for (int x : flatten_ranges(vecs)) {
    result.push_back(x);
  }
  
  REQUIRE(result == std::vector<int>{1, 2, 3, 4, 5, 6});
}

TEST_CASE("Generator utility functions", "[generator]") {
  SECTION("iota(n)") {
    std::vector<int64_t> result;
    for (int64_t x : iota(5)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 1, 2, 3, 4});
  }
  
  SECTION("iota(start, end)") {
    std::vector<int64_t> result;
    for (int64_t x : iota(3, 7)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{3, 4, 5, 6});
  }
  
  SECTION("from_range") {
    std::vector<int> source{10, 20, 30};
    std::vector<int> result;
    
    for (int x : from_range(source)) {
      result.push_back(x);
    }
    
    REQUIRE(result == source);
  }
  
  SECTION("filter") {
    auto even = [](int64_t x) { return x % 2 == 0; };
    
    std::vector<int64_t> result;
    for (int64_t x : filter(iota(10), even)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 2, 4, 6, 8});
  }
  
  SECTION("map") {
    auto square = [](int64_t x) { return x * x; };
    
    std::vector<int64_t> result;
    for (int64_t x : map(iota(5), square)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 1, 4, 9, 16});
  }
  
  SECTION("take") {
    std::vector<int64_t> result;
    for (int64_t x : take(iota(100), 5)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 1, 2, 3, 4});
  }
  
  SECTION("take fewer than available") {
    std::vector<int64_t> result;
    for (int64_t x : take(iota(3), 10)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 1, 2});
  }
  
  SECTION("combined: filter and map") {
    auto even = [](int64_t x) { return x % 2 == 0; };
    auto square = [](int64_t x) { return x * x; };
    
    std::vector<int64_t> result;
    for (int64_t x : map(filter(iota(10), even), square)) {
      result.push_back(x);
    }
    
    REQUIRE(result == std::vector<int64_t>{0, 4, 16, 36, 64});
  }
}

TEST_CASE("Generator with ranges compatibility", "[generator]") {
  SECTION("can use begin/end") {
    auto gen = count_to(3);
    auto it = gen.begin();
    auto end = gen.end();
    
    REQUIRE(it != end);
    REQUIRE(*it == 0);
    ++it;
    REQUIRE(*it == 1);
    ++it;
    REQUIRE(*it == 2);
    ++it;
    REQUIRE(it == end);
  }
  
  SECTION("can use std::ranges::for_each") {
    int sum = 0;
    std::ranges::for_each(count_to(5), [&sum](int x) { sum += x; });
    
    REQUIRE(sum == 10);  // 0+1+2+3+4
  }
}

TEST_CASE("Generator string types", "[generator]") {
  // Generator that yields strings.
  auto words = []() -> Generator<std::string> {
    co_yield "hello";
    co_yield "world";
    co_yield "!";
  };
  
  std::vector<std::string> result;
  for (const auto& s : words()) {
    result.push_back(s);
  }
  
  REQUIRE(result == std::vector<std::string>{"hello", "world", "!"});
}

TEST_CASE("Generator iterator post-increment", "[generator]") {
  auto gen = count_to(3);
  auto it = gen.begin();
  
  auto prev = it++;  // Post-increment.
  REQUIRE(*prev == 0);
  REQUIRE(*it == 1);
}
