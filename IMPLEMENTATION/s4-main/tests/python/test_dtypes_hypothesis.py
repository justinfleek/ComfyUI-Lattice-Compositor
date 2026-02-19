"""Hypothesis property tests for s4_runtime.dtypes module."""

import math
import struct
from hypothesis import given, assume, settings, example
from hypothesis import strategies as st

import pytest

# Import will fail until module is built, but tests define the interface.
try:
    from s4_runtime import dtypes
    HAS_MODULE = True
except ImportError:
    HAS_MODULE = False
    dtypes = None


pytestmark = pytest.mark.skipif(not HAS_MODULE, reason="s4_runtime not built")


# Strategy for generating valid dtype codes.
@st.composite
def dtype_codes(draw):
    """Generate valid dtype codes."""
    all_dtypes = dtypes.all_dtypes()
    return draw(st.sampled_from(all_dtypes))


@st.composite  
def float_dtype_codes(draw):
    """Generate floating-point dtype codes."""
    float_types = dtypes.float_dtypes()
    return draw(st.sampled_from(float_types))


@st.composite
def integer_dtype_codes(draw):
    """Generate integer dtype codes."""
    int_types = dtypes.integer_dtypes()
    return draw(st.sampled_from(int_types))


class TestDtypeDescription:
    """Property tests for dtype description."""
    
    @given(dtype_codes())
    def test_describe_returns_valid_description(self, code):
        """All valid dtypes should have a description."""
        desc = dtypes.describe(code)
        assert desc is not None
        assert desc.code == code
        assert len(desc.name) > 0
    
    @given(dtype_codes())
    def test_storage_size_is_positive(self, code):
        """Storage size should be positive for all types."""
        size = dtypes.storage_size_bytes(code)
        assert size >= 1
    
    @given(dtype_codes())
    def test_alignment_is_power_of_two(self, code):
        """Alignment should be a power of two."""
        align = dtypes.storage_alignment_bytes(code)
        assert align > 0
        assert (align & (align - 1)) == 0  # Power of two check.
    
    @given(dtype_codes())
    def test_alignment_divides_size(self, code):
        """Alignment should divide storage size for non-packed types."""
        desc = dtypes.describe(code)
        if not desc.is_packed:
            assert desc.storage_size_bytes % desc.storage_alignment_bytes == 0
    
    @given(dtype_codes())
    def test_name_roundtrip(self, code):
        """Name should parse back to same dtype."""
        name = dtypes.name(code)
        parsed = dtypes.from_string(name)
        assert parsed == code


class TestPackedTypes:
    """Property tests for packed dtype formats."""
    
    @given(dtype_codes())
    def test_packed_has_multiple_elements_per_unit(self, code):
        """Packed types should have >1 element per storage unit."""
        if dtypes.is_packed(code):
            assert dtypes.logical_elements_per_storage_unit(code) > 1
        else:
            assert dtypes.logical_elements_per_storage_unit(code) == 1
    
    @given(dtype_codes(), st.integers(min_value=0, max_value=10000))
    def test_storage_bytes_consistency(self, code, logical_count):
        """Storage bytes computation should be consistent."""
        result = dtypes.compute_storage_bytes(code, logical_count)
        if result is not None:
            # Inverse should give back at least the logical count.
            logical_back = dtypes.compute_logical_elements(code, result)
            assert logical_back is not None
            assert logical_back >= logical_count
    
    @given(dtype_codes(), st.integers(min_value=0, max_value=10000))
    def test_packed_storage_ceiling(self, code, logical_count):
        """Packed storage should use ceiling division."""
        result = dtypes.compute_storage_bytes(code, logical_count)
        if result is not None:
            elems_per_unit = dtypes.logical_elements_per_storage_unit(code)
            size = dtypes.storage_size_bytes(code)
            # Expected: ceil(logical_count / elems_per_unit) * size
            expected = ((logical_count + elems_per_unit - 1) // elems_per_unit) * size
            assert result == expected


class TestFloatingPointProperties:
    """Property tests for floating-point type metadata."""
    
    @given(float_dtype_codes())
    def test_is_floating_point(self, code):
        """Float types should be marked as floating point."""
        assert dtypes.is_floating_point(code)
    
    @given(float_dtype_codes())
    def test_has_exponent_and_mantissa(self, code):
        """Float types should have exponent and mantissa bits."""
        desc = dtypes.describe(code)
        assert desc.exponent_bits > 0
        assert desc.mantissa_bits >= 0  # Some formats have 0 explicit mantissa.
    
    @given(integer_dtype_codes())
    def test_integers_not_floating_point(self, code):
        """Integer types should not be marked as floating point."""
        assert not dtypes.is_floating_point(code)


class TestSignedness:
    """Property tests for signedness."""
    
    @given(float_dtype_codes())
    def test_floats_are_signed(self, code):
        """All floating-point types should be signed."""
        assert dtypes.is_signed(code)
    
    @given(integer_dtype_codes())
    def test_unsigned_prefix(self, code):
        """Unsigned types should have 'u' prefix in name."""
        name = dtypes.name(code)
        if name.startswith("u"):
            assert not dtypes.is_signed(code)
        else:
            assert dtypes.is_signed(code) or name == "boolean"


class TestInvalidDtype:
    """Tests for invalid dtype handling."""
    
    def test_invalid_code_properties(self):
        """Invalid dtype should have safe defaults."""
        code = dtypes.DtypeCode.invalid
        desc = dtypes.describe(code)
        assert desc.storage_size_bytes == 0
        assert desc.name == "invalid"
    
    def test_invalid_storage_computation(self):
        """Storage computation should fail for invalid dtype."""
        code = dtypes.DtypeCode.invalid
        result = dtypes.compute_storage_bytes(code, 100)
        assert result is None
    
    def test_unknown_string_parses_to_none(self):
        """Unknown dtype string should parse to None."""
        result = dtypes.from_string("not_a_real_dtype")
        assert result is None


class TestDtypeEnumeration:
    """Tests for dtype enumeration functions."""
    
    def test_all_dtypes_not_empty(self):
        """all_dtypes should return non-empty list."""
        all_types = dtypes.all_dtypes()
        assert len(all_types) > 0
    
    def test_float_dtypes_subset(self):
        """Float dtypes should be subset of all dtypes."""
        all_types = set(dtypes.all_dtypes())
        float_types = set(dtypes.float_dtypes())
        assert float_types.issubset(all_types)
    
    def test_integer_dtypes_subset(self):
        """Integer dtypes should be subset of all dtypes."""
        all_types = set(dtypes.all_dtypes())
        int_types = set(dtypes.integer_dtypes())
        assert int_types.issubset(all_types)
    
    def test_no_overlap_float_and_integer(self):
        """Float and integer dtypes should be disjoint."""
        float_types = set(dtypes.float_dtypes())
        int_types = set(dtypes.integer_dtypes())
        assert float_types.isdisjoint(int_types)


class TestDtypeHashing:
    """Tests for dtype hashing and equality."""
    
    @given(dtype_codes())
    def test_hash_consistency(self, code):
        """Hash should be consistent across calls."""
        h1 = hash(code)
        h2 = hash(code)
        assert h1 == h2
    
    @given(dtype_codes(), dtype_codes())
    def test_equal_implies_same_hash(self, code1, code2):
        """Equal codes should have equal hashes."""
        if code1 == code2:
            assert hash(code1) == hash(code2)
    
    @given(dtype_codes())
    def test_int_conversion(self, code):
        """Int conversion should give underlying enum value."""
        value = int(code)
        assert isinstance(value, int)
        assert value >= 0
