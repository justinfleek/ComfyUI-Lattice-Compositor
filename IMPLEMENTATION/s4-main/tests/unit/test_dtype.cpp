// s4-runtime // tests/unit/test_dtype.cpp
// Unit tests for dtype system.
#include <catch2/catch_test_macros.hpp>
#include <catch2/catch_approx.hpp>

#include <s4/dtypes/dtype.h>
#include <s4/dtypes/dispatch.h>

using namespace s4::dtypes;

TEST_CASE("dtype_code describes all types correctly", "[dtype]") {
  SECTION("float16") {
    auto desc = describe(dtype_code::float16);
    REQUIRE(desc.code == dtype_code::float16);
    REQUIRE(desc.storage_size_bytes == 2);
    REQUIRE(desc.is_floating_point);
    REQUIRE(desc.is_signed);
    REQUIRE(desc.exponent_bits == 5);
    REQUIRE(desc.mantissa_bits == 10);
    REQUIRE_FALSE(desc.is_packed);
  }

  SECTION("bfloat16") {
    auto desc = describe(dtype_code::bfloat16);
    REQUIRE(desc.storage_size_bytes == 2);
    REQUIRE(desc.exponent_bits == 8);
    REQUIRE(desc.mantissa_bits == 7);
  }

  SECTION("float32") {
    auto desc = describe(dtype_code::float32);
    REQUIRE(desc.storage_size_bytes == 4);
    REQUIRE(desc.exponent_bits == 8);
    REQUIRE(desc.mantissa_bits == 23);
  }

  SECTION("nvfp4_e2m1_packed") {
    auto desc = describe(dtype_code::nvfp4_e2m1_packed);
    REQUIRE(desc.storage_size_bytes == 1);
    REQUIRE(desc.is_packed);
    REQUIRE(desc.logical_elements_per_storage_unit == 2);
    REQUIRE(desc.exponent_bits == 2);
    REQUIRE(desc.mantissa_bits == 1);
  }

  SECTION("integer types") {
    REQUIRE(describe(dtype_code::int8).storage_size_bytes == 1);
    REQUIRE(describe(dtype_code::int16).storage_size_bytes == 2);
    REQUIRE(describe(dtype_code::int32).storage_size_bytes == 4);
    REQUIRE(describe(dtype_code::int64).storage_size_bytes == 8);
    
    REQUIRE(describe(dtype_code::int32).is_signed);
    REQUIRE_FALSE(describe(dtype_code::uint32).is_signed);
    REQUIRE_FALSE(describe(dtype_code::int32).is_floating_point);
  }

  SECTION("invalid") {
    auto desc = describe(dtype_code::invalid);
    REQUIRE(desc.storage_size_bytes == 0);
  }
}

TEST_CASE("try_compute_storage_bytes handles all cases", "[dtype]") {
  SECTION("simple types") {
    std::size_t bytes = 0;
    
    REQUIRE(try_compute_storage_bytes(dtype_code::float32, 10, &bytes));
    REQUIRE(bytes == 40);
    
    REQUIRE(try_compute_storage_bytes(dtype_code::float16, 100, &bytes));
    REQUIRE(bytes == 200);
  }

  SECTION("packed types round up") {
    std::size_t bytes = 0;
    
    // 2 elements per byte for nvfp4.
    REQUIRE(try_compute_storage_bytes(dtype_code::nvfp4_e2m1_packed, 1, &bytes));
    REQUIRE(bytes == 1);  // ceil(1/2) = 1
    
    REQUIRE(try_compute_storage_bytes(dtype_code::nvfp4_e2m1_packed, 2, &bytes));
    REQUIRE(bytes == 1);  // ceil(2/2) = 1
    
    REQUIRE(try_compute_storage_bytes(dtype_code::nvfp4_e2m1_packed, 3, &bytes));
    REQUIRE(bytes == 2);  // ceil(3/2) = 2
    
    REQUIRE(try_compute_storage_bytes(dtype_code::nvfp4_e2m1_packed, 16, &bytes));
    REQUIRE(bytes == 8);  // ceil(16/2) = 8
  }

  SECTION("zero elements") {
    std::size_t bytes = 0;
    REQUIRE(try_compute_storage_bytes(dtype_code::float32, 0, &bytes));
    REQUIRE(bytes == 0);
  }

  SECTION("invalid dtype fails") {
    std::size_t bytes = 0;
    REQUIRE_FALSE(try_compute_storage_bytes(dtype_code::invalid, 10, &bytes));
  }

  SECTION("null output pointer fails") {
    REQUIRE_FALSE(try_compute_storage_bytes(dtype_code::float32, 10, nullptr));
  }
}

TEST_CASE("from_string parses dtype names", "[dtype]") {
  REQUIRE(from_string("float32") == dtype_code::float32);
  REQUIRE(from_string("float16") == dtype_code::float16);
  REQUIRE(from_string("bfloat16") == dtype_code::bfloat16);
  REQUIRE(from_string("int32") == dtype_code::int32);
  REQUIRE(from_string("nvfp4_e2m1_packed") == dtype_code::nvfp4_e2m1_packed);
  
  REQUIRE_FALSE(from_string("not_a_dtype").has_value());
  REQUIRE_FALSE(from_string("").has_value());
}

TEST_CASE("dtype dispatch calls correct overload", "[dtype]") {
  SECTION("dispatch_dtype") {
    bool called = false;
    std::size_t type_size = 0;
    
    dispatch_dtype(dtype_code::float32, [&](auto tag) {
      using T = typename decltype(tag)::type;
      if constexpr (!std::is_same_v<T, invalid_type>) {
        called = true;
        type_size = sizeof(T);
      }
    });
    
    REQUIRE(called);
    REQUIRE(type_size == 4);
  }

  SECTION("dispatch_compute_dtype") {
    int call_count = 0;
    
    for (auto code : {dtype_code::float16, dtype_code::bfloat16, dtype_code::float32}) {
      dispatch_compute_dtype(code, [&](auto tag) {
        using T = typename decltype(tag)::type;
        if constexpr (!std::is_same_v<T, invalid_type>) {
          call_count++;
        }
      });
    }
    
    REQUIRE(call_count == 3);
  }

  SECTION("invalid dtype returns invalid_type") {
    bool got_invalid = false;
    
    dispatch_dtype(dtype_code::invalid, [&](auto tag) {
      using T = typename decltype(tag)::type;
      if constexpr (std::is_same_v<T, invalid_type>) {
        got_invalid = true;
      }
    });
    
    REQUIRE(got_invalid);
  }
}

TEST_CASE("dtype_of trait maps types correctly", "[dtype]") {
  REQUIRE(dtype_of_v<float> == dtype_code::float32);
  REQUIRE(dtype_of_v<double> == dtype_code::float64);
  REQUIRE(dtype_of_v<std::int32_t> == dtype_code::int32);
  REQUIRE(dtype_of_v<std::uint8_t> == dtype_code::uint8);
  REQUIRE(dtype_of_v<bool> == dtype_code::boolean);
}
