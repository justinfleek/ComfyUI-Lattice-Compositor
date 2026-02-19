// s4-runtime // tests/unit/test_core.cpp
// Unit tests for core utilities.
#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>

#include <s4/core/workspace.h>
#include <s4/core/serialize.h>
#include <s4/core/exceptions.h>
#include <s4/core/hash.h>

#include <array>
#include <cstring>
#include <limits>
#include <unordered_set>
#include <vector>

using namespace s4::core;
using namespace s4::dtypes;

TEST_CASE("linear_allocator basic operations", "[workspace]") {
  std::array<std::byte, 1024> buffer{};
  linear_allocator alloc(buffer.data(), buffer.size());

  SECTION("initial state") {
    REQUIRE(alloc.bytes_used() == 0);
    REQUIRE(alloc.capacity_bytes() == 1024);
    REQUIRE(alloc.remaining_bytes() == 1024);
  }

  SECTION("simple allocation") {
    auto result = alloc.try_allocate_bytes(100, 16);
    REQUIRE(result.succeeded());
    REQUIRE(result.size_bytes == 100);
    REQUIRE(alloc.bytes_used() >= 100);
  }

  SECTION("aligned allocation") {
    auto result = alloc.try_allocate_bytes(10, 64);
    REQUIRE(result.succeeded());
    
    auto ptr_val = reinterpret_cast<std::uintptr_t>(result.pointer);
    REQUIRE((ptr_val % 64) == 0);
  }

  SECTION("multiple allocations don't overlap") {
    auto r1 = alloc.try_allocate_bytes(100, 16);
    auto r2 = alloc.try_allocate_bytes(100, 16);
    auto r3 = alloc.try_allocate_bytes(100, 16);
    
    REQUIRE(r1.succeeded());
    REQUIRE(r2.succeeded());
    REQUIRE(r3.succeeded());
    
    // Check non-overlapping.
    auto p1 = static_cast<std::byte*>(r1.pointer);
    auto p2 = static_cast<std::byte*>(r2.pointer);
    auto p3 = static_cast<std::byte*>(r3.pointer);
    
    REQUIRE((p2 >= p1 + 100 || p1 >= p2 + 100));
    REQUIRE((p3 >= p2 + 100 || p2 >= p3 + 100));
  }

  SECTION("allocation failure when full") {
    auto r1 = alloc.try_allocate_bytes(1000, 16);
    REQUIRE(r1.succeeded());
    
    auto r2 = alloc.try_allocate_bytes(100, 16);
    REQUIRE_FALSE(r2.succeeded());
    REQUIRE(r2.pointer == nullptr);
  }

  SECTION("reset clears state") {
    alloc.try_allocate_bytes(500, 16);
    REQUIRE(alloc.bytes_used() >= 500);
    
    alloc.reset();
    REQUIRE(alloc.bytes_used() == 0);
    
    // Can allocate again.
    auto result = alloc.try_allocate_bytes(1000, 16);
    REQUIRE(result.succeeded());
  }

  SECTION("zero-size allocation succeeds") {
    auto result = alloc.try_allocate_bytes(0, 16);
    REQUIRE(result.succeeded());
    REQUIRE(result.size_bytes == 0);
  }

  SECTION("invalid alignment fails") {
    // Non-power-of-two.
    auto r1 = alloc.try_allocate_bytes(100, 3);
    REQUIRE_FALSE(r1.succeeded());
    
    // Zero alignment.
    auto r2 = alloc.try_allocate_bytes(100, 0);
    REQUIRE_FALSE(r2.succeeded());
  }
}

TEST_CASE("linear_allocator element allocation", "[workspace]") {
  std::array<std::byte, 1024> buffer{};
  linear_allocator alloc(buffer.data(), buffer.size());

  SECTION("float32 elements") {
    auto result = alloc.try_allocate_elements(dtype_code::float32, 10, 16);
    REQUIRE(result.succeeded());
    REQUIRE(result.size_bytes == 40);
  }

  SECTION("packed nvfp4 elements") {
    auto result = alloc.try_allocate_elements(dtype_code::nvfp4_e2m1_packed, 16, 16);
    REQUIRE(result.succeeded());
    REQUIRE(result.size_bytes == 8);  // 16 elements / 2 per byte = 8 bytes.
  }

  SECTION("invalid dtype fails") {
    auto result = alloc.try_allocate_elements(dtype_code::invalid, 10, 16);
    REQUIRE_FALSE(result.succeeded());
  }
}

TEST_CASE("instrumented_allocator records events", "[workspace]") {
  std::array<std::byte, 1024> buffer{};
  auto sink = std::make_shared<recording_event_sink>();
  
  instrumented_allocator alloc(
      std::make_unique<linear_allocator>(buffer.data(), buffer.size()),
      sink);

  alloc.try_allocate_bytes(100, 16);
  alloc.try_allocate_elements(dtype_code::float32, 10, 32);
  alloc.reset();

  REQUIRE(sink->events().size() == 3);
  REQUIRE(sink->events()[0].event_kind == allocation_event::kind::allocate_bytes);
  REQUIRE(sink->events()[0].requested_bytes == 100);
  REQUIRE(sink->events()[1].event_kind == allocation_event::kind::allocate_elements);
  REQUIRE(sink->events()[1].dtype == dtype_code::float32);
  REQUIRE(sink->events()[2].event_kind == allocation_event::kind::reset);
}

TEST_CASE("binary_writer and binary_reader roundtrip", "[serialize]") {
  SECTION("primitive types") {
    binary_writer writer;
    writer.write<std::uint32_t>(42);
    writer.write<std::int64_t>(-12345);
    writer.write<std::uint8_t>(255);
    
    binary_reader reader(writer.bytes());
    REQUIRE(reader.read<std::uint32_t>() == 42);
    REQUIRE(reader.read<std::int64_t>() == -12345);
    REQUIRE(reader.read<std::uint8_t>() == 255);
    REQUIRE(reader.at_end());
  }

  SECTION("strings") {
    binary_writer writer;
    writer.write_string("hello");
    writer.write_string("world");
    writer.write_string("");
    
    binary_reader reader(writer.bytes());
    REQUIRE(reader.read_string() == "hello");
    REQUIRE(reader.read_string() == "world");
    REQUIRE(reader.read_string() == "");
  }

  SECTION("vectors") {
    std::vector<std::int32_t> original{1, 2, 3, 4, 5};
    
    binary_writer writer;
    writer.write_vector<std::int32_t>(original);
    
    binary_reader reader(writer.bytes());
    auto result = reader.read_vector<std::int32_t>();
    REQUIRE(result == original);
  }

  SECTION("floats as bits") {
    float f = 3.14159f;
    double d = 2.71828;
    
    binary_writer writer;
    writer.write_float_bits(f);
    writer.write_double_bits(d);
    
    binary_reader reader(writer.bytes());
    REQUIRE(reader.read_float_bits() == Catch::Approx(f));
    REQUIRE(reader.read_double_bits() == Catch::Approx(d));
  }

  SECTION("special float values") {
    binary_writer writer;
    writer.write_float_bits(std::numeric_limits<float>::infinity());
    writer.write_float_bits(-std::numeric_limits<float>::infinity());
    writer.write_float_bits(0.0f);
    writer.write_float_bits(-0.0f);
    
    binary_reader reader(writer.bytes());
    REQUIRE(reader.read_float_bits() == std::numeric_limits<float>::infinity());
    REQUIRE(reader.read_float_bits() == -std::numeric_limits<float>::infinity());
    
    float zero = reader.read_float_bits();
    float neg_zero = reader.read_float_bits();
    REQUIRE(zero == 0.0f);
    REQUIRE(neg_zero == 0.0f);
  }

  SECTION("optional values") {
    binary_writer writer;
    std::optional<std::int32_t> some_val = 42;
    std::optional<std::int32_t> no_val = std::nullopt;
    
    writer.write_optional(some_val);
    writer.write_optional(no_val);
    
    binary_reader reader(writer.bytes());
    std::optional<std::int32_t> read1, read2;
    REQUIRE(reader.try_read_optional(read1));
    REQUIRE(reader.try_read_optional(read2));
    
    REQUIRE(read1.has_value());
    REQUIRE(*read1 == 42);
    REQUIRE_FALSE(read2.has_value());
  }
}

TEST_CASE("binary_reader error handling", "[serialize]") {
  std::array<std::byte, 4> small_buffer{};
  
  SECTION("read past end fails") {
    binary_reader reader(small_buffer);
    std::uint64_t value;
    REQUIRE_FALSE(reader.try_read(value));
  }

  SECTION("can_read checks correctly") {
    binary_reader reader(small_buffer);
    REQUIRE(reader.can_read(4));
    REQUIRE_FALSE(reader.can_read(5));
  }

  SECTION("peek doesn't advance") {
    binary_writer writer;
    writer.write<std::uint32_t>(123);
    
    binary_reader reader(writer.bytes());
    std::uint32_t peeked;
    REQUIRE(reader.try_peek(peeked));
    REQUIRE(peeked == 123);
    REQUIRE(reader.position() == 0);  // Didn't advance.
    
    REQUIRE(reader.read<std::uint32_t>() == 123);
    REQUIRE(reader.position() == 4);  // Now advanced.
  }
}

TEST_CASE("versioned_header", "[serialize]") {
  SECTION("write and read header") {
    binary_writer writer;
    write_versioned_header(writer, 1, 100);
    
    binary_reader reader(writer.bytes());
    auto header = read_versioned_header(reader);
    
    REQUIRE(header.has_value());
    REQUIRE(header->magic == serialization_magic);
    REQUIRE(header->version == 1);
    REQUIRE(header->payload_size == 100);
  }

  SECTION("invalid magic fails") {
    std::array<std::byte, 16> bad_data{};
    binary_reader reader(bad_data);
    
    auto header = read_versioned_header(reader);
    REQUIRE_FALSE(header.has_value());
  }
}

TEST_CASE("to_str utility", "[exceptions]") {
  SECTION("empty arguments") {
    auto result = to_str();
    REQUIRE(std::string(result) == "");
  }

  SECTION("single argument") {
    auto result = to_str("hello");
    REQUIRE(result == "hello");
  }

  SECTION("multiple arguments") {
    auto result = to_str("value: ", 42, ", name: ", "test");
    REQUIRE(result == "value: 42, name: test");
  }
}

TEST_CASE("hash_combine", "[hash]") {
  SECTION("different inputs produce different hashes") {
    std::size_t h1 = 0, h2 = 0;
    hash_combine(h1, std::size_t{42});
    hash_combine(h2, std::size_t{43});
    
    REQUIRE(h1 != h2);
  }
  
  SECTION("order matters") {
    std::size_t h1 = 0, h2 = 0;
    hash_combine(h1, std::size_t{1});
    hash_combine(h1, std::size_t{2});
    
    hash_combine(h2, std::size_t{2});
    hash_combine(h2, std::size_t{1});
    
    REQUIRE(h1 != h2);
  }
  
  SECTION("same input produces same hash") {
    std::size_t h1 = 0, h2 = 0;
    hash_combine(h1, std::size_t{42});
    hash_combine(h2, std::size_t{42});
    
    REQUIRE(h1 == h2);
  }
}

TEST_CASE("combined_hash", "[hash]") {
  SECTION("single value") {
    auto h = combined_hash(42);
    REQUIRE(h != 0);  // Should produce a non-zero hash.
  }
  
  SECTION("multiple values") {
    auto h1 = combined_hash(1, 2, 3);
    auto h2 = combined_hash(1, 2, 4);
    
    REQUIRE(h1 != h2);
  }
  
  SECTION("different types") {
    auto h = combined_hash(42, std::string("hello"), 3.14);
    REQUIRE(h != 0);
  }
}

TEST_CASE("hash_range", "[hash]") {
  SECTION("empty range") {
    std::vector<int> v;
    auto h = hash_range(v.begin(), v.end());
    REQUIRE(h == 0);  // Empty range should produce seed (0).
  }
  
  SECTION("same elements produce same hash") {
    std::vector<int> v1{1, 2, 3};
    std::vector<int> v2{1, 2, 3};
    
    REQUIRE(hash_range(v1.begin(), v1.end()) == hash_range(v2.begin(), v2.end()));
  }
  
  SECTION("different elements produce different hash") {
    std::vector<int> v1{1, 2, 3};
    std::vector<int> v2{1, 2, 4};
    
    REQUIRE(hash_range(v1.begin(), v1.end()) != hash_range(v2.begin(), v2.end()));
  }
}

TEST_CASE("hash_container", "[hash]") {
  SECTION("vector") {
    std::vector<int> v{1, 2, 3};
    auto h = hash_container(v);
    REQUIRE(h != 0);
  }
  
  SECTION("array") {
    std::array<int, 3> a{1, 2, 3};
    auto h = hash_container(a);
    REQUIRE(h != 0);
  }
}

TEST_CASE("pair_hash", "[hash]") {
  pair_hash<int, std::string> hasher;
  
  SECTION("same pairs have same hash") {
    auto p1 = std::make_pair(42, std::string("hello"));
    auto p2 = std::make_pair(42, std::string("hello"));
    
    REQUIRE(hasher(p1) == hasher(p2));
  }
  
  SECTION("different pairs have different hash") {
    auto p1 = std::make_pair(42, std::string("hello"));
    auto p2 = std::make_pair(42, std::string("world"));
    
    REQUIRE(hasher(p1) != hasher(p2));
  }
  
  SECTION("can use in unordered_set") {
    std::unordered_set<std::pair<int, int>, pair_hash<int, int>> set;
    set.insert({1, 2});
    set.insert({3, 4});
    set.insert({1, 2});  // Duplicate.
    
    REQUIRE(set.size() == 2);
    REQUIRE(set.count({1, 2}) == 1);
  }
}

TEST_CASE("tuple_hash", "[hash]") {
  tuple_hash<int, std::string, double> hasher;
  
  SECTION("same tuples have same hash") {
    auto t1 = std::make_tuple(42, std::string("hello"), 3.14);
    auto t2 = std::make_tuple(42, std::string("hello"), 3.14);
    
    REQUIRE(hasher(t1) == hasher(t2));
  }
  
  SECTION("different tuples have different hash") {
    auto t1 = std::make_tuple(42, std::string("hello"), 3.14);
    auto t2 = std::make_tuple(43, std::string("hello"), 3.14);
    
    REQUIRE(hasher(t1) != hasher(t2));
  }
}
