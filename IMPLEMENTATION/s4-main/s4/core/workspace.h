// s4-runtime // core/workspace.h
// Workspace allocation for GPU kernels.
#pragma once

#include <s4/core/exceptions.h>
#include <s4/dtypes/dtype.h>
#include <s4/traits/traits.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <vector>

namespace s4::core {

// Result of a workspace allocation attempt.
struct allocation_result final {
  void* pointer = nullptr;
  std::size_t offset = 0;
  std::size_t size_bytes = 0;
  
  [[nodiscard]] auto succeeded() const noexcept -> bool {
    return pointer != nullptr;
  }
  
  [[nodiscard]] explicit operator bool() const noexcept {
    return succeeded();
  }
};

// Event for allocation tracking/debugging.
struct allocation_event final {
  enum class kind : std::uint8_t {
    allocate_bytes,
    allocate_elements,
    reset,
  };
  
  kind event_kind = kind::allocate_bytes;
  std::size_t requested_bytes = 0;
  std::size_t alignment_bytes = 0;
  std::optional<dtypes::dtype_code> dtype;
  std::optional<std::size_t> element_count;
  allocation_result result{};
};

// Abstract interface for allocation event sinks.
class allocation_event_sink {
public:
  virtual ~allocation_event_sink() = default;
  virtual void on_event(const allocation_event& event) = 0;
};

// Abstract workspace allocator interface.
//
// Invariants (for proof/verification):
// 1. Monotonic allocation offset.
// 2. Non-overlapping allocations.
// 3. bytes_used() <= capacity_bytes().
// 4. Alignment correctness: returned pointers are aligned.
// 5. Reset correctness: after reset(), bytes_used() == 0.
// 6. Determinism: identical requests yield identical results.
class workspace_allocator : public traits::non_copyable {
public:
  virtual ~workspace_allocator() = default;

  // Try to allocate raw bytes.
  [[nodiscard]] virtual auto try_allocate_bytes(
      std::size_t byte_count, std::size_t alignment_bytes = 16) noexcept
      -> allocation_result = 0;

  // Try to allocate logical elements of a given dtype.
  [[nodiscard]] virtual auto try_allocate_elements(
      dtypes::dtype_code dtype, std::size_t element_count,
      std::size_t alignment_bytes = 16) noexcept
      -> allocation_result = 0;

  // Reset allocator state (invalidates all previous allocations).
  virtual auto reset() noexcept -> void = 0;

  // Query current state.
  [[nodiscard]] virtual auto bytes_used() const noexcept -> std::size_t = 0;
  [[nodiscard]] virtual auto capacity_bytes() const noexcept -> std::size_t = 0;

  // Check if allocation would succeed without actually allocating.
  [[nodiscard]] virtual auto can_allocate_bytes(
      std::size_t byte_count, std::size_t alignment_bytes = 16) const noexcept
      -> bool = 0;
  
  // Remaining capacity.
  [[nodiscard]] auto remaining_bytes() const noexcept -> std::size_t {
    return capacity_bytes() - bytes_used();
  }
};

// Simple linear bump allocator.
// Fast, deterministic, but cannot reclaim memory until reset.
class linear_allocator final : public workspace_allocator {
public:
  linear_allocator(void* base, std::size_t capacity) noexcept
      : base_(static_cast<std::byte*>(base)), capacity_(capacity) {}

  [[nodiscard]] auto try_allocate_bytes(
      std::size_t byte_count, std::size_t alignment) noexcept
      -> allocation_result override {
    
    if (!traits::is_power_of_two(alignment) || alignment == 0) {
      return {};
    }
    
    // Calculate aligned offset.
    const auto current = reinterpret_cast<std::uintptr_t>(base_) + offset_;
    const auto aligned = (current + alignment - 1) & ~(alignment - 1);
    const auto padding = aligned - current;
    
    // Check for overflow.
    if (offset_ + padding + byte_count > capacity_) {
      return {};
    }
    
    const std::size_t result_offset = offset_ + padding;
    offset_ = result_offset + byte_count;
    
    return {
      .pointer = base_ + result_offset,
      .offset = result_offset,
      .size_bytes = byte_count,
    };
  }

  [[nodiscard]] auto try_allocate_elements(
      dtypes::dtype_code dtype, std::size_t element_count,
      std::size_t alignment) noexcept -> allocation_result override {
    
    std::size_t byte_count = 0;
    if (!dtypes::try_compute_storage_bytes(dtype, element_count, &byte_count)) {
      return {};
    }
    
    // Use dtype's natural alignment if not specified.
    if (alignment < dtypes::storage_alignment_bytes(dtype)) {
      alignment = dtypes::storage_alignment_bytes(dtype);
    }
    
    return try_allocate_bytes(byte_count, alignment);
  }

  auto reset() noexcept -> void override { offset_ = 0; }

  [[nodiscard]] auto bytes_used() const noexcept -> std::size_t override {
    return offset_;
  }

  [[nodiscard]] auto capacity_bytes() const noexcept -> std::size_t override {
    return capacity_;
  }

  [[nodiscard]] auto can_allocate_bytes(
      std::size_t byte_count, std::size_t alignment) const noexcept 
      -> bool override {
    if (!traits::is_power_of_two(alignment) || alignment == 0) {
      return false;
    }
    
    const auto current = reinterpret_cast<std::uintptr_t>(base_) + offset_;
    const auto aligned = (current + alignment - 1) & ~(alignment - 1);
    const auto padding = aligned - current;
    
    return offset_ + padding + byte_count <= capacity_;
  }

  [[nodiscard]] auto base() const noexcept -> void* { return base_; }

private:
  std::byte* base_ = nullptr;
  std::size_t capacity_ = 0;
  std::size_t offset_ = 0;
};

// Instrumented allocator wrapper for debugging/profiling.
class instrumented_allocator final : public workspace_allocator {
public:
  instrumented_allocator(
      std::unique_ptr<workspace_allocator> inner,
      std::shared_ptr<allocation_event_sink> sink)
      : inner_(std::move(inner)), sink_(std::move(sink)) {}

  [[nodiscard]] auto try_allocate_bytes(
      std::size_t byte_count, std::size_t alignment) noexcept
      -> allocation_result override {
    
    auto result = inner_->try_allocate_bytes(byte_count, alignment);
    
    if (sink_) {
      sink_->on_event({
        .event_kind = allocation_event::kind::allocate_bytes,
        .requested_bytes = byte_count,
        .alignment_bytes = alignment,
        .result = result,
      });
    }
    
    return result;
  }

  [[nodiscard]] auto try_allocate_elements(
      dtypes::dtype_code dtype, std::size_t element_count,
      std::size_t alignment) noexcept -> allocation_result override {
    
    auto result = inner_->try_allocate_elements(dtype, element_count, alignment);
    
    if (sink_) {
      sink_->on_event({
        .event_kind = allocation_event::kind::allocate_elements,
        .dtype = dtype,
        .element_count = element_count,
        .alignment_bytes = alignment,
        .result = result,
      });
    }
    
    return result;
  }

  auto reset() noexcept -> void override {
    inner_->reset();
    
    if (sink_) {
      sink_->on_event({.event_kind = allocation_event::kind::reset});
    }
  }

  [[nodiscard]] auto bytes_used() const noexcept -> std::size_t override {
    return inner_->bytes_used();
  }

  [[nodiscard]] auto capacity_bytes() const noexcept -> std::size_t override {
    return inner_->capacity_bytes();
  }

  [[nodiscard]] auto can_allocate_bytes(
      std::size_t byte_count, std::size_t alignment) const noexcept 
      -> bool override {
    return inner_->can_allocate_bytes(byte_count, alignment);
  }

private:
  std::unique_ptr<workspace_allocator> inner_;
  std::shared_ptr<allocation_event_sink> sink_;
};

// Event sink that records all events for later analysis.
class recording_event_sink final : public allocation_event_sink {
public:
  void on_event(const allocation_event& event) override {
    events_.push_back(event);
  }

  [[nodiscard]] auto events() const noexcept 
      -> const std::vector<allocation_event>& {
    return events_;
  }

  auto clear() noexcept -> void { events_.clear(); }

private:
  std::vector<allocation_event> events_;
};

}  // namespace s4::core
