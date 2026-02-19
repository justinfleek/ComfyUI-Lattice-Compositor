// s4-runtime // bindings/python/core_bindings.cpp
// Python bindings for core utilities.
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/functional.h>

#include <s4/core/workspace.h>
#include <s4/core/serialize.h>
#include <s4/dtypes/dtype.h>

#include <cstring>
#include <memory>
#include <vector>

namespace py = pybind11;

using namespace s4::core;
using namespace s4::dtypes;

// Wrapper that owns both the buffer and the reader.
// This ensures the buffer outlives the reader.
struct owned_binary_reader {
  std::vector<std::byte> buffer;
  binary_reader reader;

  explicit owned_binary_reader(std::vector<std::byte> data)
      : buffer(std::move(data)),
        reader(std::span<const std::byte>(buffer.data(), buffer.size())) {}
};

void init_core(py::module_& m) {
  // Allocation result.
  py::class_<allocation_result>(m, "AllocationResult")
      .def_readonly("pointer", &allocation_result::pointer)
      .def_readonly("size_bytes", &allocation_result::size_bytes)
      .def("succeeded", &allocation_result::succeeded)
      .def("__bool__", &allocation_result::succeeded)
      .def("__repr__", [](const allocation_result& r) {
        return r.succeeded()
            ? "<AllocationResult: " + std::to_string(r.size_bytes) + " bytes>"
            : "<AllocationResult: failed>";
      });

  // Abstract allocator interface.
  py::class_<workspace_allocator,
             std::shared_ptr<workspace_allocator>>(
      m, "WorkspaceAllocator",
      "Abstract interface for workspace memory allocation")
      .def("try_allocate_bytes", &workspace_allocator::try_allocate_bytes,
           py::arg("size_bytes"), py::arg("alignment") = 16)
      .def("try_allocate_elements",
           &workspace_allocator::try_allocate_elements,
           py::arg("dtype"), py::arg("num_elements"), py::arg("alignment") = 16)
      .def("reset", &workspace_allocator::reset)
      .def("bytes_used", &workspace_allocator::bytes_used)
      .def("capacity_bytes", &workspace_allocator::capacity_bytes)
      .def("remaining_bytes", &workspace_allocator::remaining_bytes);

  // Linear allocator with Python-managed buffer.
  // Uses custom deleter to ensure buffer outlives allocator.
  py::class_<linear_allocator,
             workspace_allocator,
             std::shared_ptr<linear_allocator>>(
      m, "LinearAllocator",
      "Bump allocator for sequential memory allocation")
      .def(py::init([](std::size_t capacity) {
        // Allocate buffer that will be captured by the custom deleter.
        auto buffer = std::make_shared<std::vector<std::byte>>(capacity);
        auto* raw_allocator = new linear_allocator(buffer->data(), buffer->size());
        // Custom deleter captures buffer, ensuring it outlives the allocator.
        return std::shared_ptr<linear_allocator>(
            raw_allocator,
            [buffer](linear_allocator* allocator_ptr) { delete allocator_ptr; });
      }),
           py::arg("capacity"),
           "Create a linear allocator with the given capacity in bytes")
      .def("__repr__", [](const linear_allocator& a) {
        return "<LinearAllocator: " + std::to_string(a.bytes_used()) + "/" +
               std::to_string(a.capacity_bytes()) + " bytes used>";
      });

  // Allocation event kinds.
  py::enum_<allocation_event::kind>(m, "AllocationEventKind")
      .value("allocate_bytes", allocation_event::kind::allocate_bytes)
      .value("allocate_elements",
             allocation_event::kind::allocate_elements)
      .value("reset", allocation_event::kind::reset);

  // Allocation event.
  py::class_<allocation_event>(m, "AllocationEvent")
      .def_readonly("event_kind", &allocation_event::event_kind)
      .def_readonly("requested_bytes", &allocation_event::requested_bytes)
      .def_readonly("alignment_bytes", &allocation_event::alignment_bytes)
      .def_readonly("dtype", &allocation_event::dtype)
      .def_readonly("element_count", &allocation_event::element_count)
      .def_readonly("result", &allocation_event::result);

  // Recording event sink.
  py::class_<allocation_event_sink,
             std::shared_ptr<allocation_event_sink>>(
      m, "AllocationEventSink",
      "Abstract interface for allocation event sinks")
      .def("on_event", &allocation_event_sink::on_event);

  py::class_<recording_event_sink,
             allocation_event_sink,
             std::shared_ptr<recording_event_sink>>(
      m, "RecordingEventSink",
      "Records allocation events for analysis")
      .def(py::init<>())
      .def("on_event", &recording_event_sink::on_event)
      .def("events", &recording_event_sink::events,
           py::return_value_policy::reference_internal)
      .def("clear", &recording_event_sink::clear)
      .def("__len__",
           [](const recording_event_sink& s) {
             return s.events().size();
           });

  // Binary writer.
  py::class_<binary_writer>(m, "BinaryWriter",
                             "Binary serialization writer")
      .def(py::init<>())
      .def("write_u8",
           [](binary_writer& w, std::uint8_t v) { w.write(v); })
      .def("write_u16",
           [](binary_writer& w, std::uint16_t v) { w.write(v); })
      .def("write_u32",
           [](binary_writer& w, std::uint32_t v) { w.write(v); })
      .def("write_u64",
           [](binary_writer& w, std::uint64_t v) { w.write(v); })
      .def("write_i8",
           [](binary_writer& w, std::int8_t v) { w.write(v); })
      .def("write_i16",
           [](binary_writer& w, std::int16_t v) { w.write(v); })
      .def("write_i32",
           [](binary_writer& w, std::int32_t v) { w.write(v); })
      .def("write_i64",
           [](binary_writer& w, std::int64_t v) { w.write(v); })
      .def("write_f32", &binary_writer::write_float_bits)
      .def("write_f64", &binary_writer::write_double_bits)
      .def("write_string", &binary_writer::write_string)
      .def("write_bytes",
           [](binary_writer& w, py::bytes data) {
             std::string s = data;
             w.write_bytes(s.data(), s.size());
           })
      .def("size", &binary_writer::size)
      .def("to_bytes",
           [](const binary_writer& w) {
             const auto& bytes = w.bytes();
             return py::bytes(reinterpret_cast<const char*>(bytes.data()),
                              bytes.size());
           });

  // Binary reader with owned buffer.
  // Uses owned_binary_reader wrapper to ensure buffer outlives reader.
  py::class_<owned_binary_reader>(m, "BinaryReader",
                                   "Binary serialization reader")
      .def(py::init([](py::bytes data) {
        std::string string_data = data;
        std::vector<std::byte> buffer(string_data.size());
        std::memcpy(buffer.data(), string_data.data(), string_data.size());
        return std::make_unique<owned_binary_reader>(std::move(buffer));
      }))
      .def("read_u8",
           [](owned_binary_reader& r) { return r.reader.read<std::uint8_t>(); })
      .def("read_u16",
           [](owned_binary_reader& r) { return r.reader.read<std::uint16_t>(); })
      .def("read_u32",
           [](owned_binary_reader& r) { return r.reader.read<std::uint32_t>(); })
      .def("read_u64",
           [](owned_binary_reader& r) { return r.reader.read<std::uint64_t>(); })
      .def("read_i8",
           [](owned_binary_reader& r) { return r.reader.read<std::int8_t>(); })
      .def("read_i16",
           [](owned_binary_reader& r) { return r.reader.read<std::int16_t>(); })
      .def("read_i32",
           [](owned_binary_reader& r) { return r.reader.read<std::int32_t>(); })
      .def("read_i64",
           [](owned_binary_reader& r) { return r.reader.read<std::int64_t>(); })
      .def("read_f32",
           [](owned_binary_reader& r) { return r.reader.read_float_bits(); })
      .def("read_f64",
           [](owned_binary_reader& r) { return r.reader.read_double_bits(); })
      .def("read_string",
           [](owned_binary_reader& r) { return r.reader.read_string(); })
      .def("read_bytes",
           [](owned_binary_reader& r, std::size_t n) {
             std::vector<std::byte> bytes(n);
             if (!r.reader.try_read_bytes(bytes.data(), n)) {
               throw std::runtime_error("Read past end of buffer");
             }
             return py::bytes(reinterpret_cast<const char*>(bytes.data()), n);
           })
      .def("position",
           [](const owned_binary_reader& r) { return r.reader.position(); })
      .def("remaining",
           [](const owned_binary_reader& r) { return r.reader.remaining(); })
      .def("at_end",
           [](const owned_binary_reader& r) { return r.reader.at_end(); })
      .def("can_read",
           [](const owned_binary_reader& r, std::size_t bytes) {
             return r.reader.can_read(bytes);
           });

  // Versioned header utilities.
  m.def("serialization_magic", []() { return serialization_magic; });

  py::class_<versioned_header>(m, "VersionedHeader")
      .def_readonly("magic", &versioned_header::magic)
      .def_readonly("version", &versioned_header::version)
      .def_readonly("payload_size", &versioned_header::payload_size)
      .def("__repr__", [](const versioned_header& h) {
        return "<VersionedHeader: v" + std::to_string(h.version) +
               ", payload=" + std::to_string(h.payload_size) + " bytes>";
      });

  m.def("write_versioned_header", &write_versioned_header);
  m.def("read_versioned_header",
        [](binary_reader& r) -> std::optional<versioned_header> {
          return read_versioned_header(r);
        });
}
