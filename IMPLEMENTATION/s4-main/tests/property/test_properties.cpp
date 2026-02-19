// s4-runtime // tests/property/test_properties.cpp
// Property-based tests using RapidCheck.
#include <catch2/catch_test_macros.hpp>
#include <rapidcheck.h>
#include <rapidcheck/catch.h>

#include <s4/dtypes/dtype.h>
#include <s4/containers/unique_vector.h>
#include <s4/containers/disjoint_sets.h>
#include <s4/core/workspace.h>
#include <s4/core/serialize.h>

#include <algorithm>
#include <cmath>
#include <set>

using namespace s4;

// ============================================================================
// dtype properties
// ============================================================================

TEST_CASE("dtype properties", "[property][dtype]") {
  SECTION("storage bytes roundtrip") {
    rc::check("storage bytes is invertible for non-packed types",
        [](std::size_t count) {
          if (count > 1000000) return;  // Avoid overflow.
          
          std::size_t bytes = 0;
          auto code = dtypes::dtype_code::float32;
          
          if (!dtypes::try_compute_storage_bytes(code, count, &bytes)) {
            return;  // Skip if computation fails.
          }
          
          std::size_t recovered = 0;
          RC_ASSERT(dtypes::try_compute_logical_elements(code, bytes, &recovered));
          RC_ASSERT(recovered == count);
        });
  }

  SECTION("describe is consistent") {
    rc::check("describe returns valid info for all valid codes",
        []() {
          auto codes = std::vector<dtypes::dtype_code>{
            dtypes::dtype_code::float16,
            dtypes::dtype_code::bfloat16,
            dtypes::dtype_code::float32,
            dtypes::dtype_code::float64,
            dtypes::dtype_code::int8,
            dtypes::dtype_code::int32,
            dtypes::dtype_code::uint8,
            dtypes::dtype_code::uint32,
          };
          
          auto code = *rc::gen::elementOf(codes);
          auto desc = dtypes::describe(code);
          
          RC_ASSERT(desc.storage_size_bytes > 0);
          RC_ASSERT(desc.storage_alignment_bytes > 0);
          RC_ASSERT(desc.storage_alignment_bytes <= desc.storage_size_bytes || 
                    desc.storage_alignment_bytes % desc.storage_size_bytes == 0);
        });
  }
}

// ============================================================================
// unique_vector properties
// ============================================================================

TEST_CASE("unique_vector properties", "[property][containers]") {
  SECTION("no duplicates") {
    rc::check("unique_vector never contains duplicates",
        [](std::vector<int> input) {
          containers::unique_vector<int> uv;
          for (int x : input) {
            uv.push_back(x);
          }
          
          std::set<int> as_set(uv.begin(), uv.end());
          RC_ASSERT(as_set.size() == uv.size());
        });
  }

  SECTION("size is bounded by input") {
    rc::check("size <= input size",
        [](std::vector<int> input) {
          containers::unique_vector<int> uv(input.begin(), input.end());
          RC_ASSERT(uv.size() <= input.size());
        });
  }

  SECTION("contains all unique elements") {
    rc::check("contains exactly the unique elements from input",
        [](std::vector<int> input) {
          containers::unique_vector<int> uv(input.begin(), input.end());
          std::set<int> input_set(input.begin(), input.end());
          
          for (int x : input_set) {
            RC_ASSERT(uv.contains(x));
          }
          RC_ASSERT(uv.size() == input_set.size());
        });
  }

  SECTION("intersection commutativity") {
    rc::check("a.intersect(b) has same elements as b.intersect(a)",
        [](std::vector<int> a_vec, std::vector<int> b_vec) {
          containers::unique_vector<int> a(a_vec.begin(), a_vec.end());
          containers::unique_vector<int> b(b_vec.begin(), b_vec.end());
          
          auto ab = a.intersect(b);
          auto ba = b.intersect(a);
          
          // Same elements, possibly different order.
          RC_ASSERT(ab.size() == ba.size());
          for (int x : ab) {
            RC_ASSERT(ba.contains(x));
          }
        });
  }

  SECTION("union completeness") {
    rc::check("a.unite(b) contains all elements from both",
        [](std::vector<int> a_vec, std::vector<int> b_vec) {
          containers::unique_vector<int> a(a_vec.begin(), a_vec.end());
          containers::unique_vector<int> b(b_vec.begin(), b_vec.end());
          
          auto united = a.unite(b);
          
          for (int x : a) {
            RC_ASSERT(united.contains(x));
          }
          for (int x : b) {
            RC_ASSERT(united.contains(x));
          }
        });
  }

  SECTION("subtract correctness") {
    rc::check("a.subtract(b) contains only elements in a but not b",
        [](std::vector<int> a_vec, std::vector<int> b_vec) {
          containers::unique_vector<int> a(a_vec.begin(), a_vec.end());
          containers::unique_vector<int> b(b_vec.begin(), b_vec.end());
          
          auto diff = a.subtract(b);
          
          for (int x : diff) {
            RC_ASSERT(a.contains(x));
            RC_ASSERT(!b.contains(x));
          }
        });
  }
}

// ============================================================================
// disjoint_sets properties
// ============================================================================

TEST_CASE("disjoint_sets properties", "[property][containers]") {
  SECTION("reflexivity") {
    rc::check("an element is always mapped to itself",
        [](int x) {
          containers::disjoint_sets<int> ds;
          ds.initialize_set(x);
          RC_ASSERT(ds.strict_are_mapped(x, x));
        });
  }

  SECTION("symmetry") {
    rc::check("if x is mapped to y, then y is mapped to x",
        [](int x, int y) {
          containers::disjoint_sets<int> ds;
          ds.map_entries(x, y);
          
          if (ds.mapping_exists(x) && ds.mapping_exists(y)) {
            RC_ASSERT(ds.permissive_are_mapped(x, y) == ds.permissive_are_mapped(y, x));
          }
        });
  }

  SECTION("transitivity") {
    rc::check("if x~y and y~z, then x~z",
        [](int x, int y, int z) {
          containers::disjoint_sets<int> ds;
          ds.map_entries(x, y);
          ds.map_entries(y, z);
          
          RC_ASSERT(ds.strict_are_mapped(x, z));
        });
  }

  SECTION("copy independence") {
    rc::check("modifying a copy doesn't affect original",
        [](std::vector<std::pair<int, int>> mappings) {
          containers::disjoint_sets<int> original;
          for (auto [a, b] : mappings) {
            original.map_entries(a, b);
          }
          
          std::size_t original_size = original.size();
          
          containers::disjoint_sets<int> copy(original);
          copy.map_entries(9999, 10000);
          
          RC_ASSERT(original.size() == original_size);
        });
  }

  SECTION("all_elements is complete") {
    rc::check("all_elements contains all mapped elements",
        [](std::vector<std::pair<int, int>> mappings) {
          containers::disjoint_sets<int> ds;
          std::set<int> expected;
          
          for (auto [a, b] : mappings) {
            ds.map_entries(a, b);
            expected.insert(a);
            expected.insert(b);
          }
          
          auto all = ds.all_elements();
          RC_ASSERT(all.size() == expected.size());
          
          for (int x : expected) {
            RC_ASSERT(all.contains(x));
          }
        });
  }
}

// ============================================================================
// workspace allocator properties
// ============================================================================

TEST_CASE("linear_allocator properties", "[property][workspace]") {
  SECTION("allocations don't exceed capacity") {
    rc::check("bytes_used never exceeds capacity",
        [](std::vector<std::pair<std::size_t, int>> requests) {
          std::vector<std::byte> buffer(65536);
          core::linear_allocator alloc(buffer.data(), buffer.size());
          
          for (auto [size, align_exp] : requests) {
            size = size % 1024;  // Cap request size.
            std::size_t alignment = std::size_t{1} << (align_exp % 7);
            
            alloc.try_allocate_bytes(size, alignment);
            RC_ASSERT(alloc.bytes_used() <= alloc.capacity_bytes());
          }
        });
  }

  SECTION("reset restores to initial state") {
    rc::check("after reset, bytes_used is zero",
        [](std::vector<std::size_t> sizes) {
          std::vector<std::byte> buffer(65536);
          core::linear_allocator alloc(buffer.data(), buffer.size());
          
          for (std::size_t size : sizes) {
            alloc.try_allocate_bytes(size % 1024, 16);
          }
          
          alloc.reset();
          RC_ASSERT(alloc.bytes_used() == 0);
        });
  }

  SECTION("successful allocations return aligned pointers") {
    rc::check("returned pointers are properly aligned",
        [](std::size_t size, int align_exp) {
          std::vector<std::byte> buffer(65536);
          core::linear_allocator alloc(buffer.data(), buffer.size());
          
          size = size % 1024;
          std::size_t alignment = std::size_t{1} << (align_exp % 7);
          
          auto result = alloc.try_allocate_bytes(size, alignment);
          if (result.succeeded()) {
            auto ptr_val = reinterpret_cast<std::uintptr_t>(result.pointer);
            RC_ASSERT((ptr_val % alignment) == 0);
          }
        });
  }
}

// ============================================================================
// serialization properties
// ============================================================================

TEST_CASE("serialization properties", "[property][serialize]") {
  SECTION("primitive roundtrip") {
    rc::check("primitives serialize and deserialize correctly",
        [](std::uint32_t a, std::int64_t b, std::uint8_t c) {
          core::binary_writer writer;
          writer.write(a);
          writer.write(b);
          writer.write(c);
          
          core::binary_reader reader(writer.bytes());
          RC_ASSERT(reader.read<std::uint32_t>() == a);
          RC_ASSERT(reader.read<std::int64_t>() == b);
          RC_ASSERT(reader.read<std::uint8_t>() == c);
          RC_ASSERT(reader.at_end());
        });
  }

  SECTION("string roundtrip") {
    rc::check("strings serialize and deserialize correctly",
        [](std::string s) {
          core::binary_writer writer;
          writer.write_string(s);
          
          core::binary_reader reader(writer.bytes());
          RC_ASSERT(reader.read_string() == s);
        });
  }

  SECTION("vector roundtrip") {
    rc::check("vectors serialize and deserialize correctly",
        [](std::vector<std::int32_t> vec) {
          core::binary_writer writer;
          writer.write_vector<std::int32_t>(vec);
          
          core::binary_reader reader(writer.bytes());
          auto result = reader.read_vector<std::int32_t>();
          RC_ASSERT(result == vec);
        });
  }

  SECTION("float bit preservation") {
    rc::check("float bits are preserved through serialization",
        [](std::uint32_t bits) {
          float original;
          std::memcpy(&original, &bits, sizeof(float));
          
          core::binary_writer writer;
          writer.write_float_bits(original);
          
          core::binary_reader reader(writer.bytes());
          float result = reader.read_float_bits();
          
          std::uint32_t result_bits;
          std::memcpy(&result_bits, &result, sizeof(float));
          
          RC_ASSERT(result_bits == bits);
        });
  }
}

// ============================================================================
// Generator properties
// ============================================================================

#include <s4/core/generator.h>
#include <numeric>

TEST_CASE("generator properties", "[property][generator]") {
  using namespace core;
  
  SECTION("iota produces correct sequence") {
    rc::check("iota(n) produces [0, n)",
        [](std::uint16_t n) {
          std::vector<int64_t> result;
          for (int64_t x : iota(n)) {
            result.push_back(x);
          }
          
          RC_ASSERT(result.size() == n);
          for (std::size_t i = 0; i < result.size(); ++i) {
            RC_ASSERT(result[i] == static_cast<int64_t>(i));
          }
        });
  }
  
  SECTION("iota range produces correct sequence") {
    rc::check("iota(a, b) produces [a, b)",
        [](std::int16_t a, std::int16_t b) {
          if (b < a) std::swap(a, b);
          
          std::vector<int64_t> result;
          for (int64_t x : iota(a, b)) {
            result.push_back(x);
          }
          
          RC_ASSERT(result.size() == static_cast<std::size_t>(b - a));
          for (std::size_t i = 0; i < result.size(); ++i) {
            RC_ASSERT(result[i] == a + static_cast<int64_t>(i));
          }
        });
  }
  
  SECTION("take limits output") {
    rc::check("take(gen, n) produces at most n elements",
        [](std::uint8_t gen_size, std::uint8_t take_size) {
          std::vector<int64_t> result;
          for (int64_t x : take(iota(gen_size), take_size)) {
            result.push_back(x);
          }
          
          RC_ASSERT(result.size() == std::min<std::size_t>(gen_size, take_size));
        });
  }
  
  SECTION("filter preserves predicate") {
    rc::check("filter only yields matching elements",
        [](std::uint8_t n) {
          auto is_even = [](int64_t x) { return x % 2 == 0; };
          
          for (int64_t x : filter(iota(n), is_even)) {
            RC_ASSERT(x % 2 == 0);
          }
        });
  }
  
  SECTION("map applies function") {
    rc::check("map applies function to all elements",
        [](std::uint8_t n) {
          auto square = [](int64_t x) { return x * x; };
          
          std::vector<int64_t> result;
          for (int64_t x : map(iota(n), square)) {
            result.push_back(x);
          }
          
          RC_ASSERT(result.size() == n);
          for (std::size_t i = 0; i < result.size(); ++i) {
            int64_t expected = static_cast<int64_t>(i * i);
            RC_ASSERT(result[i] == expected);
          }
        });
  }
  
  SECTION("from_range preserves elements") {
    rc::check("from_range yields same elements as input",
        [](std::vector<int> input) {
          std::vector<int> result;
          for (int x : from_range(input)) {
            result.push_back(x);
          }
          
          RC_ASSERT(result == input);
        });
  }
}
