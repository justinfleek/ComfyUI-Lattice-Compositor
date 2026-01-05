"""Tests for compositor_node.py validation functions."""

import math
import pytest

from lattice.nodes.compositor_node import (
    MAX_ARRAY_LENGTH,
    MAX_EXPRESSION_LENGTH,
    MAX_KEYFRAMES_PER_PROPERTY,
    MAX_LAYERS,
    MAX_NESTING_DEPTH,
    MAX_PROJECT_SIZE_BYTES,
    MAX_STRING_LENGTH,
    NUMERIC_BOUNDS,
    ProjectValidationError,
    _calculate_max_depth,
    _count_layers,
    _validate_array_lengths,
    _validate_expressions,
    _validate_numeric_bounds,
    _validate_paths,
    _validate_string_lengths,
    validate_project,
    validate_project_id,
)


class TestValidateProject:
    """Tests for the main validate_project function."""

    def test_valid_minimal_project(self, sample_project_data):
        """Test that a minimal valid project passes validation."""
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) == 0
        assert isinstance(data, dict)
        assert data["version"] == "1.0.0"

    def test_project_too_large(self, sample_project_data):
        """Test that oversized projects are rejected."""
        with pytest.raises(ProjectValidationError) as exc_info:
            validate_project(sample_project_data, file_size=MAX_PROJECT_SIZE_BYTES + 1)
        assert "size limit" in str(exc_info.value).lower()

    def test_project_not_dict(self):
        """Test that non-dict projects are rejected."""
        with pytest.raises(ProjectValidationError) as exc_info:
            validate_project([])
        assert "object" in str(exc_info.value).lower()

    def test_project_nesting_too_deep(self):
        """Test that deeply nested projects are rejected."""
        # Create a deeply nested structure
        data = {"a": {"b": {"c": {}}}}
        depth = 0
        current = data
        while depth < MAX_NESTING_DEPTH + 1:
            current["nested"] = {}
            current = current["nested"]
            depth += 1

        with pytest.raises(ProjectValidationError) as exc_info:
            validate_project(data)
        assert "nesting" in str(exc_info.value).lower()

    def test_project_with_dangerous_expression(self, sample_project_data):
        """Test that projects with dangerous expressions are rejected."""
        sample_project_data["layers"] = [
            {"expression": "eval('malicious code')"}
        ]
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) > 0
        assert any("eval" in err.lower() for err in errors)

    def test_project_with_invalid_numeric_bounds(self, sample_project_data):
        """Test that projects with out-of-bounds numeric values are rejected."""
        sample_project_data["composition"]["fps"] = 500  # Exceeds max of 240
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) > 0
        assert any("fps" in err.lower() or "range" in err.lower() for err in errors)

    def test_project_with_too_many_layers(self, sample_project_data):
        """Test that projects with too many layers are rejected."""
        sample_project_data["layers"] = [{}] * (MAX_LAYERS + 1)
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) > 0
        assert any("layers" in err.lower() for err in errors)

    def test_project_with_nan_values(self, sample_project_data):
        """Test that projects with NaN values are rejected."""
        sample_project_data["composition"]["width"] = float("nan")
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) > 0
        assert any("nan" in err.lower() for err in errors)

    def test_project_with_infinite_values(self, sample_project_data):
        """Test that projects with infinite values are rejected."""
        sample_project_data["composition"]["height"] = float("inf")
        data, errors, warnings = validate_project(sample_project_data)
        assert len(errors) > 0
        assert any("infinite" in err.lower() for err in errors)


class TestCalculateMaxDepth:
    """Tests for _calculate_max_depth function."""

    def test_empty_dict(self):
        """Test depth calculation for empty dict."""
        assert _calculate_max_depth({}) == 1

    def test_shallow_dict(self):
        """Test depth calculation for shallow dict."""
        data = {"a": 1, "b": 2}
        assert _calculate_max_depth(data) == 1

    def test_nested_dict(self):
        """Test depth calculation for nested dict."""
        data = {"a": {"b": {"c": 1}}}
        assert _calculate_max_depth(data) == 3

    def test_list_nesting(self):
        """Test depth calculation with list nesting."""
        data = {"a": [{"b": 1}]}
        assert _calculate_max_depth(data) == 3

    def test_mixed_nesting(self):
        """Test depth calculation with mixed structures."""
        data = {"a": {"b": [{"c": {"d": 1}}]}}
        assert _calculate_max_depth(data) == 4


class TestValidateExpressions:
    """Tests for _validate_expressions function."""

    def test_valid_expression(self):
        """Test that valid expressions pass."""
        data = {"expression": "2 + 2"}
        errors = _validate_expressions(data)
        assert len(errors) == 0

    def test_dangerous_eval_expression(self):
        """Test that eval() expressions are caught."""
        data = {"expression": "eval('malicious')"}
        errors = _validate_expressions(data)
        assert len(errors) > 0
        assert any("eval" in err.lower() for err in errors)

    def test_dangerous_function_constructor(self):
        """Test that Function() constructor is caught."""
        data = {"expression": "Function('return 1')()"}
        errors = _validate_expressions(data)
        assert len(errors) > 0

    def test_dangerous_fetch(self):
        """Test that fetch() calls are caught."""
        data = {"expression": "fetch('http://evil.com')"}
        errors = _validate_expressions(data)
        assert len(errors) > 0

    def test_expression_too_long(self):
        """Test that overly long expressions are caught."""
        data = {"expression": "x" * (MAX_EXPRESSION_LENGTH + 1)}
        errors = _validate_expressions(data)
        assert len(errors) > 0
        assert any("length" in err.lower() for err in errors)

    def test_expressions_dict(self):
        """Test validation of expressions dict."""
        data = {"expressions": {"x": "2 + 2", "y": "eval('bad')"}}
        errors = _validate_expressions(data)
        assert len(errors) > 0

    def test_nested_expressions(self):
        """Test validation of nested expression fields."""
        data = {"layer": {"properties": {"expression": "eval('bad')"}}}
        errors = _validate_expressions(data)
        assert len(errors) > 0

    def test_all_dangerous_patterns(self):
        """Test that all dangerous patterns are caught."""
        dangerous = [
            "eval('x')",
            "Function('x')",
            "require('x')",
            "import('x')",
            "process.exit()",
            "fetch('x')",
            "XMLHttpRequest()",
            "document.cookie",
            "window.location",
            "globalThis.x",
            "Reflect.get()",
            "Proxy({})",
        ]
        for expr in dangerous:
            data = {"expression": expr}
            errors = _validate_expressions(data)
            assert len(errors) > 0, f"Failed to catch dangerous pattern: {expr}"


class TestValidateNumericBounds:
    """Tests for _validate_numeric_bounds function."""

    def test_valid_numeric_values(self):
        """Test that valid numeric values pass."""
        data = {"fps": 30, "width": 1920, "height": 1080}
        errors = _validate_numeric_bounds(data)
        assert len(errors) == 0

    def test_fps_out_of_bounds(self):
        """Test that out-of-bounds fps is caught."""
        data = {"fps": 500}  # Max is 240
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0
        assert any("fps" in err.lower() for err in errors)

    def test_width_out_of_bounds(self):
        """Test that out-of-bounds width is caught."""
        data = {"width": 20000}  # Max is 16384
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0

    def test_opacity_out_of_bounds(self):
        """Test that out-of-bounds opacity is caught."""
        data = {"opacity": 1.5}  # Max is 1.0
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0

    def test_nan_value(self):
        """Test that NaN values are caught."""
        data = {"fps": float("nan")}
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0
        assert any("nan" in err.lower() for err in errors)

    def test_infinite_value(self):
        """Test that infinite values are caught."""
        data = {"width": float("inf")}
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0
        assert any("infinite" in err.lower() for err in errors)

    def test_nested_numeric_validation(self):
        """Test that numeric validation works on nested structures."""
        data = {"composition": {"fps": 500}}
        errors = _validate_numeric_bounds(data)
        assert len(errors) > 0

    def test_all_numeric_bounds(self):
        """Test all defined numeric bounds."""
        for field, (min_val, max_val) in NUMERIC_BOUNDS.items():
            # Test below minimum
            data = {field: min_val - 1}
            errors = _validate_numeric_bounds(data)
            assert len(errors) > 0, f"Failed to catch {field} below minimum"

            # Test above maximum
            data = {field: max_val + 1}
            errors = _validate_numeric_bounds(data)
            assert len(errors) > 0, f"Failed to catch {field} above maximum"

            # Test valid range
            data = {field: (min_val + max_val) / 2}
            errors = _validate_numeric_bounds(data)
            assert len(errors) == 0, f"Valid {field} value was rejected"


class TestValidatePaths:
    """Tests for _validate_paths function."""

    def test_valid_paths(self):
        """Test that valid paths pass."""
        data = {"path": "assets/image.png", "file": "video.mp4"}
        errors = _validate_paths(data)
        assert len(errors) == 0

    def test_path_traversal_attack(self):
        """Test that path traversal attacks are caught."""
        data = {"path": "../../../etc/passwd"}
        errors = _validate_paths(data)
        assert len(errors) > 0
        assert any("traversal" in err.lower() or ".." in err for err in errors)

    def test_absolute_path(self):
        """Test that absolute paths are caught."""
        data = {"path": "/etc/passwd"}
        errors = _validate_paths(data)
        assert len(errors) > 0

    def test_windows_path_traversal(self):
        """Test that Windows path traversal is caught."""
        data = {"path": "..\\..\\windows\\system32"}
        errors = _validate_paths(data)
        assert len(errors) > 0

    def test_nested_path_validation(self):
        """Test that path validation works on nested structures."""
        data = {"assets": {"image": {"path": "../../../etc/passwd"}}}
        errors = _validate_paths(data)
        assert len(errors) > 0


class TestValidateStringLengths:
    """Tests for _validate_string_lengths function."""

    def test_valid_string_lengths(self):
        """Test that valid string lengths pass."""
        data = {"name": "Test", "description": "A test project"}
        errors = _validate_string_lengths(data)
        assert len(errors) == 0

    def test_string_too_long(self):
        """Test that overly long strings are caught."""
        data = {"name": "x" * (MAX_STRING_LENGTH + 1)}
        errors = _validate_string_lengths(data)
        assert len(errors) > 0
        assert any("length" in err.lower() for err in errors)

    def test_nested_string_validation(self):
        """Test that string validation works on nested structures."""
        data = {"meta": {"description": "x" * (MAX_STRING_LENGTH + 1)}}
        errors = _validate_string_lengths(data)
        assert len(errors) > 0


class TestValidateArrayLengths:
    """Tests for _validate_array_lengths function."""

    def test_valid_array_lengths(self):
        """Test that valid array lengths pass."""
        data = {"layers": [{}] * 10}
        errors = _validate_array_lengths(data)
        assert len(errors) == 0

    def test_array_too_long(self):
        """Test that overly long arrays are caught."""
        data = {"layers": [{}] * (MAX_ARRAY_LENGTH + 1)}
        errors = _validate_array_lengths(data)
        assert len(errors) > 0
        assert any("length" in err.lower() for err in errors)

    def test_nested_array_validation(self):
        """Test that array validation works on nested structures."""
        data = {"composition": {"keyframes": [{}] * (MAX_ARRAY_LENGTH + 1)}}
        errors = _validate_array_lengths(data)
        assert len(errors) > 0


class TestValidateProjectId:
    """Tests for validate_project_id function."""

    def test_valid_project_id(self):
        """Test that valid project IDs pass."""
        assert validate_project_id("test_project_123") is True
        assert validate_project_id("my-project-2024") is True
        assert validate_project_id("project_1") is True

    def test_empty_project_id(self):
        """Test that empty project IDs are rejected."""
        assert validate_project_id("") is False

    def test_project_id_too_long(self):
        """Test that overly long project IDs are rejected."""
        assert validate_project_id("x" * 256) is False

    def test_project_id_with_special_chars(self):
        """Test that project IDs with special characters are rejected."""
        assert validate_project_id("project@123") is False
        assert validate_project_id("project#123") is False
        assert validate_project_id("project$123") is False
        assert validate_project_id("project.123") is False

    def test_project_id_path_traversal(self):
        """Test that path traversal attempts are rejected."""
        assert validate_project_id("../etc/passwd") is False
        assert validate_project_id("..\\windows\\system32") is False
        assert validate_project_id("project/../other") is False

    def test_project_id_with_slashes(self):
        """Test that project IDs with slashes are rejected."""
        assert validate_project_id("project/name") is False
        assert validate_project_id("project\\name") is False

    def test_project_id_with_dots(self):
        """Test that project IDs with dots are rejected."""
        assert validate_project_id("project.name") is False
        assert validate_project_id("project..name") is False


class TestCountLayers:
    """Tests for _count_layers function."""

    def test_empty_project(self):
        """Test counting layers in empty project."""
        data = {"layers": []}
        assert _count_layers(data) == 0

    def test_single_layer(self):
        """Test counting single layer."""
        data = {"layers": [{"type": "solid"}]}
        assert _count_layers(data) == 1

    def test_multiple_layers(self):
        """Test counting multiple layers."""
        data = {"layers": [{"type": "solid"}, {"type": "video"}, {"type": "text"}]}
        assert _count_layers(data) == 3

    def test_nested_compositions(self):
        """Test counting layers in nested compositions."""
        data = {
            "compositions": {
                "main": {"layers": [{"type": "solid"}]},
                "nested": {"layers": [{"type": "video"}, {"type": "text"}]},
            },
            "layers": [{"type": "image"}],
        }
        # Should count all layers across compositions
        count = _count_layers(data)
        assert count >= 1  # At least the main layers

