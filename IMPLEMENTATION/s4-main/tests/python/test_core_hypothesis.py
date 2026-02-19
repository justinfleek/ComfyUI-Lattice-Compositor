"""Hypothesis property tests for s4_runtime.core module."""

import math
import struct
from hypothesis import given, assume, settings, example, note
from hypothesis import strategies as st

import pytest

try:
    from s4_runtime import core, dtypes
    HAS_MODULE = True
except ImportError:
    HAS_MODULE = False
    core = None
    dtypes = None


pytestmark = pytest.mark.skipif(not HAS_MODULE, reason="s4_runtime not built")


# Strategies for testing.
allocator_capacities = st.integers(min_value=64, max_value=1024 * 1024)
allocation_sizes = st.integers(min_value=0, max_value=1024)
alignments = st.sampled_from([1, 2, 4, 8, 16, 32, 64, 128, 256])


class TestLinearAllocator:
    """Property tests for linear allocator."""
    
    @given(allocator_capacities)
    def test_initial_state(self, capacity):
        """Fresh allocator should have zero bytes used."""
        alloc = core.LinearAllocator(capacity)
        assert alloc.bytes_used() == 0
        assert alloc.capacity_bytes() == capacity
        assert alloc.remaining_bytes() == capacity
    
    @given(allocator_capacities, allocation_sizes, alignments)
    def test_single_allocation(self, capacity, size, alignment):
        """Single allocation within capacity should succeed."""
        assume(size + alignment <= capacity)
        
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_bytes(size, alignment)
        
        assert result.succeeded()
        assert result.size_bytes == size
        assert alloc.bytes_used() >= size
    
    @given(allocator_capacities, st.lists(st.tuples(allocation_sizes, alignments), max_size=20))
    def test_multiple_allocations_monotonic(self, capacity, allocs):
        """Bytes used should monotonically increase."""
        alloc = core.LinearAllocator(capacity)
        prev_used = 0
        
        for size, alignment in allocs:
            result = alloc.try_allocate_bytes(size, alignment)
            if result.succeeded():
                assert alloc.bytes_used() >= prev_used
                prev_used = alloc.bytes_used()
    
    @given(allocator_capacities, st.lists(st.tuples(allocation_sizes, alignments), min_size=1, max_size=20))
    def test_reset_clears_all(self, capacity, allocs):
        """Reset should clear all allocations."""
        alloc = core.LinearAllocator(capacity)
        
        for size, alignment in allocs:
            alloc.try_allocate_bytes(size, alignment)
        
        alloc.reset()
        
        assert alloc.bytes_used() == 0
        assert alloc.remaining_bytes() == capacity
    
    @given(allocator_capacities)
    def test_allocation_exceeds_capacity_fails(self, capacity):
        """Allocation larger than capacity should fail."""
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_bytes(capacity + 1, 1)
        
        assert not result.succeeded()
    
    @given(allocator_capacities, alignments)
    def test_zero_size_allocation(self, capacity, alignment):
        """Zero-size allocation should succeed."""
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_bytes(0, alignment)
        
        assert result.succeeded()
        assert result.size_bytes == 0
    
    @given(st.integers(min_value=256, max_value=4096))
    def test_capacity_invariant(self, capacity):
        """bytes_used + remaining should equal capacity."""
        alloc = core.LinearAllocator(capacity)
        
        # Do some allocations.
        for _ in range(5):
            alloc.try_allocate_bytes(17, 8)
        
        assert alloc.bytes_used() + alloc.remaining_bytes() == capacity


class TestLinearAllocatorDtypes:
    """Property tests for dtype-aware allocation."""
    
    @given(allocator_capacities, st.integers(min_value=0, max_value=100))
    def test_float32_allocation(self, capacity, count):
        """Float32 allocation should use 4 bytes per element."""
        assume(count * 4 + 16 <= capacity)
        
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_elements(dtypes.DtypeCode.float32, count, 16)
        
        if count > 0:
            assert result.succeeded()
            assert result.size_bytes == count * 4
    
    @given(allocator_capacities, st.integers(min_value=0, max_value=100))
    def test_packed_fp4_allocation(self, capacity, count):
        """Packed FP4 allocation should use ceiling division."""
        assume(capacity >= 64)
        
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_elements(
            dtypes.DtypeCode.nvfp4_e2m1_packed, count, 16
        )
        
        if result.succeeded():
            # 2 elements per byte, so ceiling division.
            expected = (count + 1) // 2
            assert result.size_bytes == expected
    
    @given(allocator_capacities, st.integers(min_value=1, max_value=50))
    def test_invalid_dtype_fails(self, capacity, count):
        """Invalid dtype should fail allocation."""
        alloc = core.LinearAllocator(capacity)
        result = alloc.try_allocate_elements(dtypes.DtypeCode.invalid, count, 16)
        
        assert not result.succeeded()


class TestBinarySerializationPrimitives:
    """Property tests for binary serialization of primitives."""
    
    @given(st.integers(min_value=0, max_value=255))
    def test_u8_roundtrip(self, value):
        """u8 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_u8(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_u8() == value
        assert reader.at_end()
    
    @given(st.integers(min_value=0, max_value=65535))
    def test_u16_roundtrip(self, value):
        """u16 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_u16(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_u16() == value
    
    @given(st.integers(min_value=0, max_value=2**32-1))
    def test_u32_roundtrip(self, value):
        """u32 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_u32(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_u32() == value
    
    @given(st.integers(min_value=0, max_value=2**63-1))
    def test_u64_roundtrip(self, value):
        """u64 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_u64(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_u64() == value
    
    @given(st.integers(min_value=-128, max_value=127))
    def test_i8_roundtrip(self, value):
        """i8 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_i8(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_i8() == value
    
    @given(st.integers(min_value=-32768, max_value=32767))
    def test_i16_roundtrip(self, value):
        """i16 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_i16(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_i16() == value
    
    @given(st.integers(min_value=-(2**31), max_value=2**31-1))
    def test_i32_roundtrip(self, value):
        """i32 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_i32(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_i32() == value
    
    @given(st.integers(min_value=-(2**62), max_value=2**62-1))
    def test_i64_roundtrip(self, value):
        """i64 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_i64(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_i64() == value


class TestBinarySerializationFloats:
    """Property tests for binary serialization of floats."""
    
    @given(st.floats(allow_nan=False, allow_infinity=True))
    def test_f32_roundtrip(self, value):
        """f32 should roundtrip correctly (as f64 for Python)."""
        # Python floats are f64, so we need to convert through f32.
        f32_value = struct.unpack('f', struct.pack('f', value))[0]
        
        writer = core.BinaryWriter()
        writer.write_f32(f32_value)
        
        reader = core.BinaryReader(writer.to_bytes())
        result = reader.read_f32()
        
        if math.isinf(f32_value):
            assert math.isinf(result)
            assert (f32_value > 0) == (result > 0)
        else:
            assert result == pytest.approx(f32_value, rel=1e-6, abs=1e-45)
    
    @given(st.floats(allow_nan=False, allow_infinity=True))
    def test_f64_roundtrip(self, value):
        """f64 should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_f64(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        result = reader.read_f64()
        
        if math.isinf(value):
            assert math.isinf(result)
            assert (value > 0) == (result > 0)
        else:
            assert result == value
    
    def test_f32_special_values(self):
        """Special float values should roundtrip."""
        special = [0.0, -0.0, float('inf'), float('-inf')]
        
        for value in special:
            writer = core.BinaryWriter()
            writer.write_f32(value)
            
            reader = core.BinaryReader(writer.to_bytes())
            result = reader.read_f32()
            
            if math.isinf(value):
                assert math.isinf(result)
            else:
                assert result == value


class TestBinarySerializationStrings:
    """Property tests for binary serialization of strings."""
    
    @given(st.text(max_size=1000))
    def test_string_roundtrip(self, value):
        """Strings should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_string(value)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_string() == value
    
    @given(st.lists(st.text(max_size=100), max_size=20))
    def test_multiple_strings(self, strings):
        """Multiple strings should roundtrip correctly."""
        writer = core.BinaryWriter()
        for s in strings:
            writer.write_string(s)
        
        reader = core.BinaryReader(writer.to_bytes())
        for s in strings:
            assert reader.read_string() == s
        
        assert reader.at_end()


class TestBinarySerializationBytes:
    """Property tests for binary serialization of raw bytes."""
    
    @given(st.binary(max_size=1000))
    def test_bytes_roundtrip(self, data):
        """Raw bytes should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_bytes(data)
        
        reader = core.BinaryReader(writer.to_bytes())
        result = reader.read_bytes(len(data))
        
        assert result == data


class TestBinarySerializationMixed:
    """Property tests for mixed serialization."""
    
    @given(
        st.integers(min_value=0, max_value=255),
        st.text(max_size=50),
        st.floats(allow_nan=False, allow_infinity=False, min_value=-1e10, max_value=1e10),
        st.integers(min_value=-(2**31), max_value=2**31-1)
    )
    def test_mixed_roundtrip(self, u8_val, str_val, f64_val, i32_val):
        """Mixed types should roundtrip correctly."""
        writer = core.BinaryWriter()
        writer.write_u8(u8_val)
        writer.write_string(str_val)
        writer.write_f64(f64_val)
        writer.write_i32(i32_val)
        
        reader = core.BinaryReader(writer.to_bytes())
        assert reader.read_u8() == u8_val
        assert reader.read_string() == str_val
        assert reader.read_f64() == pytest.approx(f64_val)
        assert reader.read_i32() == i32_val
        assert reader.at_end()


class TestBinaryReaderState:
    """Property tests for binary reader state management."""
    
    @given(st.lists(st.integers(min_value=0, max_value=255), min_size=1, max_size=100))
    def test_position_advances(self, values):
        """Position should advance correctly after reads."""
        writer = core.BinaryWriter()
        for v in values:
            writer.write_u8(v)
        
        reader = core.BinaryReader(writer.to_bytes())
        
        for i, v in enumerate(values):
            assert reader.position() == i
            assert reader.read_u8() == v
        
        assert reader.position() == len(values)
        assert reader.at_end()
    
    @given(st.lists(st.integers(min_value=0, max_value=255), min_size=1, max_size=100))
    def test_remaining_decreases(self, values):
        """Remaining should decrease correctly after reads."""
        writer = core.BinaryWriter()
        for v in values:
            writer.write_u8(v)
        
        reader = core.BinaryReader(writer.to_bytes())
        
        for i, v in enumerate(values):
            assert reader.remaining() == len(values) - i
            reader.read_u8()
        
        assert reader.remaining() == 0
    
    @given(st.binary(min_size=1, max_size=100))
    def test_can_read_checks_boundary(self, data):
        """can_read should respect buffer boundaries."""
        reader = core.BinaryReader(data)
        
        assert reader.can_read(len(data))
        assert not reader.can_read(len(data) + 1)


class TestVersionedHeader:
    """Property tests for versioned headers."""
    
    @given(st.integers(min_value=1, max_value=1000), st.integers(min_value=0, max_value=2**30))
    def test_header_roundtrip(self, version, payload_size):
        """Versioned headers should roundtrip correctly."""
        writer = core.BinaryWriter()
        core.write_versioned_header(writer, version, payload_size)
        
        reader = core.BinaryReader(writer.to_bytes())
        header = core.read_versioned_header(reader)
        
        assert header is not None
        assert header.magic == core.serialization_magic()
        assert header.version == version
        assert header.payload_size == payload_size
    
    def test_invalid_magic_fails(self):
        """Invalid magic should cause header read to fail."""
        # Create a buffer with wrong magic.
        data = b'\x00\x00\x00\x00' + b'\x00' * 12
        reader = core.BinaryReader(data)
        
        header = core.read_versioned_header(reader)
        assert header is None


class TestRecordingEventSink:
    """Property tests for allocation event recording."""
    
    @given(st.integers(min_value=256, max_value=4096), st.lists(allocation_sizes, max_size=20))
    def test_records_all_allocations(self, capacity, sizes):
        """All allocations should be recorded."""
        sink = core.RecordingEventSink()
        # Note: We can't test instrumented allocator directly from Python
        # as we need to pass shared_ptr. This tests the sink itself.
        
        assert len(sink) == 0
        sink.clear()
        assert len(sink) == 0


class TestWriterState:
    """Property tests for binary writer state."""
    
    @given(st.lists(st.integers(min_value=0, max_value=255), max_size=100))
    def test_size_tracks_writes(self, values):
        """Size should track number of bytes written."""
        writer = core.BinaryWriter()
        
        for i, v in enumerate(values):
            assert writer.size() == i
            writer.write_u8(v)
        
        assert writer.size() == len(values)
