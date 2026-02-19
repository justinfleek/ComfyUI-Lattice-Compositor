// s4-runtime // bindings/python/dtype_bindings.cpp
// Python bindings for dtype system.
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

#include <s4/dtypes/dtype.h>

namespace py = pybind11;
using namespace s4::dtypes;

void init_dtypes(py::module_& m) {
    // dtype_code enumeration
    py::enum_<dtype_code>(m, "DtypeCode", "Stable dtype enumeration for serialization")
        .value("invalid", dtype_code::invalid)
        .value("float16", dtype_code::float16)
        .value("bfloat16", dtype_code::bfloat16)
        .value("float32", dtype_code::float32)
        .value("float64", dtype_code::float64)
        .value("float8_e4m3", dtype_code::float8_e4m3)
        .value("float8_e5m2", dtype_code::float8_e5m2)
        .value("nvfp4_e2m1_packed", dtype_code::nvfp4_e2m1_packed)
        .value("int8", dtype_code::int8)
        .value("int16", dtype_code::int16)
        .value("int32", dtype_code::int32)
        .value("int64", dtype_code::int64)
        .value("uint8", dtype_code::uint8)
        .value("uint16", dtype_code::uint16)
        .value("uint32", dtype_code::uint32)
        .value("uint64", dtype_code::uint64)
        .value("boolean", dtype_code::boolean)
        .def("__hash__", [](dtype_code c) { return static_cast<std::uint32_t>(c); })
        .def("__int__", [](dtype_code c) { return static_cast<std::uint32_t>(c); });
    
    // dtype_description class
    py::class_<dtype_description>(m, "DtypeDescription", 
            "Comprehensive dtype description for runtime introspection")
        .def(py::init<>())
        .def_readonly("code", &dtype_description::code)
        .def_property_readonly("name", [](const dtype_description& d) {
            return std::string(d.name);
        })
        .def_readonly("storage_size_bytes", &dtype_description::storage_size_bytes)
        .def_readonly("storage_alignment_bytes", &dtype_description::storage_alignment_bytes)
        .def_readonly("is_packed", &dtype_description::is_packed)
        .def_readonly("logical_elements_per_storage_unit", 
                     &dtype_description::logical_elements_per_storage_unit)
        .def_readonly("is_floating_point", &dtype_description::is_floating_point)
        .def_readonly("is_signed", &dtype_description::is_signed)
        .def_readonly("exponent_bits", &dtype_description::exponent_bits)
        .def_readonly("mantissa_bits", &dtype_description::mantissa_bits)
        .def("__repr__", [](const dtype_description& d) {
            return "<DtypeDescription " + std::string(d.name) + ">";
        });
    
    // Free functions
    m.def("describe", &describe, py::arg("code"),
          "Get description for a dtype code");
    
    m.def("storage_size_bytes", &storage_size_bytes, py::arg("code"),
          "Get storage size in bytes");
    
    m.def("storage_alignment_bytes", &storage_alignment_bytes, py::arg("code"),
          "Get storage alignment in bytes");
    
    m.def("is_packed", &is_packed, py::arg("code"),
          "Check if dtype is a packed format");
    
    m.def("logical_elements_per_storage_unit", &logical_elements_per_storage_unit, 
          py::arg("code"),
          "Get number of logical elements per storage unit");
    
    m.def("is_floating_point", &is_floating_point, py::arg("code"),
          "Check if dtype is floating point");
    
    m.def("is_signed", &is_signed, py::arg("code"),
          "Check if dtype is signed");
    
    m.def("name", &name, py::arg("code"),
          "Get dtype name string");
    
    m.def("from_string", [](const std::string& s) -> std::optional<dtype_code> {
        return from_string(s);
    }, py::arg("str"), "Parse dtype from string");
    
    m.def("compute_storage_bytes", [](dtype_code code, std::size_t logical_count) 
            -> std::optional<std::size_t> {
        std::size_t result = 0;
        if (try_compute_storage_bytes(code, logical_count, &result)) {
            return result;
        }
        return std::nullopt;
    }, py::arg("code"), py::arg("logical_element_count"),
       "Compute storage bytes for logical element count");
    
    m.def("compute_logical_elements", [](dtype_code code, std::size_t storage_bytes) 
            -> std::optional<std::size_t> {
        std::size_t result = 0;
        if (try_compute_logical_elements(code, storage_bytes, &result)) {
            return result;
        }
        return std::nullopt;
    }, py::arg("code"), py::arg("storage_bytes"),
       "Compute logical element count from storage bytes");
    
    // Convenience: list all valid dtypes
    m.def("all_dtypes", []() {
        return std::vector<dtype_code>{
            dtype_code::float16, dtype_code::bfloat16, 
            dtype_code::float32, dtype_code::float64,
            dtype_code::float8_e4m3, dtype_code::float8_e5m2,
            dtype_code::nvfp4_e2m1_packed,
            dtype_code::int8, dtype_code::int16, 
            dtype_code::int32, dtype_code::int64,
            dtype_code::uint8, dtype_code::uint16, 
            dtype_code::uint32, dtype_code::uint64,
            dtype_code::boolean,
        };
    }, "Get list of all valid dtype codes");
    
    m.def("float_dtypes", []() {
        return std::vector<dtype_code>{
            dtype_code::float16, dtype_code::bfloat16,
            dtype_code::float32, dtype_code::float64,
            dtype_code::float8_e4m3, dtype_code::float8_e5m2,
            dtype_code::nvfp4_e2m1_packed,
        };
    }, "Get list of all floating point dtype codes");
    
    m.def("integer_dtypes", []() {
        return std::vector<dtype_code>{
            dtype_code::int8, dtype_code::int16, 
            dtype_code::int32, dtype_code::int64,
            dtype_code::uint8, dtype_code::uint16, 
            dtype_code::uint32, dtype_code::uint64,
        };
    }, "Get list of all integer dtype codes");
}
