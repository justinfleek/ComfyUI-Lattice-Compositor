// s4-runtime // tests/unit/test_containers.cpp
// Unit tests for container types.
#include <catch2/catch_test_macros.hpp>

#include <s4/containers/unique_vector.h>
#include <s4/containers/disjoint_sets.h>

using namespace s4::containers;

TEST_CASE("unique_vector maintains uniqueness", "[containers]") {
  SECTION("push_back rejects duplicates") {
    unique_vector<int> v;
    
    REQUIRE(v.push_back(1));
    REQUIRE(v.push_back(2));
    REQUIRE(v.push_back(3));
    REQUIRE_FALSE(v.push_back(1));
    REQUIRE_FALSE(v.push_back(2));
    
    REQUIRE(v.size() == 3);
    REQUIRE(v.contains(1));
    REQUIRE(v.contains(2));
    REQUIRE(v.contains(3));
  }

  SECTION("preserves insertion order") {
    unique_vector<int> v;
    v.push_back(3);
    v.push_back(1);
    v.push_back(2);
    v.push_back(1);  // Duplicate.
    
    REQUIRE(v.vector() == std::vector<int>{3, 1, 2});
  }

  SECTION("initializer list construction") {
    unique_vector<int> v{1, 2, 3, 2, 1};
    REQUIRE(v.size() == 3);
    REQUIRE(v.vector() == std::vector<int>{1, 2, 3});
  }

  SECTION("front and back") {
    unique_vector<int> v{10, 20, 30};
    REQUIRE(v.front() == 10);
    REQUIRE(v.back() == 30);
  }

  SECTION("pop_back removes and returns") {
    unique_vector<int> v{1, 2, 3};
    REQUIRE(v.pop_back() == 3);
    REQUIRE(v.size() == 2);
    REQUIRE_FALSE(v.contains(3));
  }

  SECTION("erase removes element") {
    unique_vector<int> v{1, 2, 3};
    REQUIRE(v.erase(2) == 1);
    REQUIRE(v.size() == 2);
    REQUIRE_FALSE(v.contains(2));
    REQUIRE(v.vector() == std::vector<int>{1, 3});
  }
}

TEST_CASE("unique_vector set operations", "[containers]") {
  unique_vector<int> a{1, 2, 3, 4};
  unique_vector<int> b{3, 4, 5, 6};

  SECTION("intersect") {
    auto intersection = a.intersect(b);
    REQUIRE(intersection.vector() == std::vector<int>{3, 4});
  }

  SECTION("has_intersection") {
    REQUIRE(a.has_intersection(b));
    
    unique_vector<int> c{10, 20};
    REQUIRE_FALSE(a.has_intersection(c));
  }

  SECTION("subtract") {
    auto diff = a.subtract(b);
    REQUIRE(diff.vector() == std::vector<int>{1, 2});
  }

  SECTION("unite") {
    auto united = a.unite(b);
    REQUIRE(united.size() == 6);
    REQUIRE(united.contains(1));
    REQUIRE(united.contains(6));
  }
}

TEST_CASE("unique_vector iteration", "[containers]") {
  unique_vector<int> v{1, 2, 3};
  
  SECTION("range-based for") {
    int sum = 0;
    for (int x : v) {
      sum += x;
    }
    REQUIRE(sum == 6);
  }

  SECTION("reverse iteration") {
    std::vector<int> reversed;
    for (auto it = v.rbegin(); it != v.rend(); ++it) {
      reversed.push_back(*it);
    }
    REQUIRE(reversed == std::vector<int>{3, 2, 1});
  }
}

TEST_CASE("disjoint_sets basic operations", "[containers]") {
  SECTION("initialize and map") {
    disjoint_sets<int> ds;
    
    ds.initialize_set(1);
    ds.initialize_set(2);
    ds.initialize_set(3);
    
    REQUIRE(ds.size() == 3);
    REQUIRE(ds.mapping_exists(1));
    REQUIRE(ds.mapping_exists(2));
    REQUIRE_FALSE(ds.mapping_exists(4));
  }

  SECTION("map_entries merges sets") {
    disjoint_sets<int> ds;
    
    ds.map_entries(1, 2);
    ds.map_entries(3, 4);
    
    REQUIRE(ds.size() == 2);
    REQUIRE(ds.strict_are_mapped(1, 2));
    REQUIRE(ds.strict_are_mapped(3, 4));
    REQUIRE_FALSE(ds.permissive_are_mapped(1, 3));
  }

  SECTION("transitive mapping") {
    disjoint_sets<int> ds;
    
    ds.map_entries(1, 2);
    ds.map_entries(2, 3);
    ds.map_entries(3, 4);
    
    REQUIRE(ds.size() == 1);
    REQUIRE(ds.strict_are_mapped(1, 4));
    REQUIRE(ds.strict_are_mapped(2, 3));
  }

  SECTION("get_set_of returns correct set") {
    disjoint_sets<int> ds;
    ds.map_entries(1, 2);
    ds.map_entries(1, 3);
    
    auto& set = ds.get_set_of(1);
    REQUIRE(set.size() == 3);
    REQUIRE(set.contains(1));
    REQUIRE(set.contains(2));
    REQUIRE(set.contains(3));
  }
}

TEST_CASE("disjoint_sets copy semantics", "[containers]") {
  disjoint_sets<int> original;
  original.map_entries(1, 2);
  original.map_entries(3, 4);
  
  SECTION("copy constructor") {
    disjoint_sets<int> copy(original);
    
    REQUIRE(copy.size() == 2);
    REQUIRE(copy.strict_are_mapped(1, 2));
    REQUIRE(copy.strict_are_mapped(3, 4));
    
    // Modifications don't affect original.
    copy.map_entries(1, 3);
    REQUIRE(copy.size() == 1);
    REQUIRE(original.size() == 2);
  }

  SECTION("copy assignment") {
    disjoint_sets<int> copy;
    copy = original;
    
    REQUIRE(copy.size() == 2);
    REQUIRE(copy.strict_are_mapped(1, 2));
  }
}

TEST_CASE("disjoint_sets erase", "[containers]") {
  disjoint_sets<int> ds;
  ds.map_entries(1, 2);
  ds.map_entries(1, 3);
  
  SECTION("erase from multi-element set") {
    REQUIRE(ds.erase(2));
    REQUIRE(ds.size() == 1);
    REQUIRE_FALSE(ds.mapping_exists(2));
    REQUIRE(ds.mapping_exists(1));
    REQUIRE(ds.mapping_exists(3));
  }

  SECTION("erase singleton set") {
    disjoint_sets<int> ds2;
    ds2.initialize_set(5);
    
    REQUIRE(ds2.erase(5));
    REQUIRE(ds2.size() == 0);
    REQUIRE_FALSE(ds2.mapping_exists(5));
  }

  SECTION("erase non-existent") {
    REQUIRE_FALSE(ds.erase(999));
  }
}

TEST_CASE("disjoint_sets all_elements", "[containers]") {
  disjoint_sets<int> ds;
  ds.map_entries(1, 2);
  ds.map_entries(3, 4);
  ds.map_entries(5, 6);
  
  auto all = ds.all_elements();
  REQUIRE(all.size() == 6);
  
  for (int i = 1; i <= 6; ++i) {
    REQUIRE(all.contains(i));
  }
}

TEST_CASE("disjoint_sets with strings", "[containers]") {
  disjoint_sets<std::string> ds;
  
  ds.map_entries("apple", "apricot");
  ds.map_entries("banana", "blueberry");
  ds.map_entries("apple", "avocado");
  
  REQUIRE(ds.size() == 2);
  REQUIRE(ds.strict_are_mapped("apple", "avocado"));
  REQUIRE(ds.strict_are_mapped("apple", "apricot"));
  REQUIRE_FALSE(ds.permissive_are_mapped("apple", "banana"));
}
