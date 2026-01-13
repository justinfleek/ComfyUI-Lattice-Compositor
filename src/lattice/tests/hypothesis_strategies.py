"""
Hypothesis strategies for property-based testing of Lattice Compositor Python code.

These strategies generate random but valid inputs for testing:
- Composition settings
- Layer data
- Animation keyframes
- Export settings
- API payloads

Usage:
    from hypothesis import given
    from lattice.tests.hypothesis_strategies import composition_settings
    
    @given(composition_settings())
    def test_composition_valid(settings):
        # settings is a randomly generated valid composition
        pass
"""

from hypothesis import strategies as st
from hypothesis.strategies import composite


# ==============================================================================
# BASIC VALUE STRATEGIES
# ==============================================================================

def dimension():
    """Valid dimension value (1 to 8192 pixels)."""
    return st.integers(min_value=1, max_value=8192)


def large_dimension():
    """Dimension that might stress memory (up to 16K)."""
    return st.integers(min_value=1, max_value=16384)


def fps():
    """Valid frames per second (0.001 to 240)."""
    return st.floats(min_value=0.001, max_value=240, allow_nan=False, allow_infinity=False)


def frame_count():
    """Valid frame count (1 to 100000)."""
    return st.integers(min_value=1, max_value=100000)


def frame_number():
    """Any frame number (including negative for testing)."""
    return st.integers(min_value=-1000, max_value=100000)


def normalized_float():
    """Float in range [0, 1]."""
    return st.floats(min_value=0.0, max_value=1.0, allow_nan=False, allow_infinity=False)


def percentage():
    """Percentage value in range [0, 100]. Used for opacity, volume controls, etc."""
    return st.floats(min_value=0.0, max_value=100.0, allow_nan=False, allow_infinity=False)


def angle_degrees():
    """Angle in degrees (-360 to 360)."""
    return st.floats(min_value=-360.0, max_value=360.0, allow_nan=False, allow_infinity=False)


def color_component():
    """Single color channel value (0-255)."""
    return st.integers(min_value=0, max_value=255)


def hex_color():
    """Valid hex color string."""
    return st.from_regex(r'^#[0-9a-fA-F]{6}$', fullmatch=True)


def uuid():
    """UUID-like string."""
    return st.from_regex(r'^[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$', fullmatch=True)


# ==============================================================================
# COMPOSITION STRATEGIES
# ==============================================================================

@composite
def composition_settings(draw):
    """Generate valid composition settings."""
    return {
        'width': draw(dimension()),
        'height': draw(dimension()),
        'fps': draw(fps()),
        'duration': draw(frame_count()),
        'backgroundColor': draw(hex_color()),
    }


@composite
def composition_meta(draw):
    """Generate valid composition metadata."""
    return {
        'name': draw(st.text(min_size=1, max_size=100)),
        'description': draw(st.text(max_size=1000)),
        'author': draw(st.text(max_size=100)),
        'created': draw(st.datetimes().map(lambda d: d.isoformat())),
        'modified': draw(st.datetimes().map(lambda d: d.isoformat())),
    }


# ==============================================================================
# TRANSFORM STRATEGIES
# ==============================================================================

@composite
def transform_2d(draw):
    """Generate valid 2D transform."""
    return {
        'position': {
            'x': draw(st.floats(min_value=-10000, max_value=10000, allow_nan=False)),
            'y': draw(st.floats(min_value=-10000, max_value=10000, allow_nan=False)),
        },
        'scale': {
            'x': draw(st.floats(min_value=0.001, max_value=100, allow_nan=False)),
            'y': draw(st.floats(min_value=0.001, max_value=100, allow_nan=False)),
        },
        'rotation': draw(angle_degrees()),
        'anchor': {
            'x': draw(st.floats(min_value=-10000, max_value=10000, allow_nan=False)),
            'y': draw(st.floats(min_value=-10000, max_value=10000, allow_nan=False)),
        },
        'opacity': draw(percentage()),  # Frontend uses 0-100; Canvas converts to 0-1 at render
    }


@composite  
def transform_3d(draw):
    """Generate valid 3D transform."""
    t2d = draw(transform_2d())
    return {
        **t2d,
        'position': {
            **t2d['position'],
            'z': draw(st.floats(min_value=-10000, max_value=10000, allow_nan=False)),
        },
        'rotation3d': {
            'x': draw(angle_degrees()),
            'y': draw(angle_degrees()),
            'z': draw(angle_degrees()),
        },
        'scale': {
            **t2d['scale'],
            'z': draw(st.floats(min_value=0.001, max_value=100, allow_nan=False)),
        },
    }


# ==============================================================================
# KEYFRAME STRATEGIES
# ==============================================================================

@composite
def bezier_handle(draw):
    """Generate valid bezier handle."""
    return {
        'x': draw(st.floats(min_value=-10, max_value=10, allow_nan=False)),
        'y': draw(st.floats(min_value=-10, max_value=10, allow_nan=False)),
    }


@composite
def keyframe(draw, value_strategy=None):
    """Generate valid keyframe."""
    if value_strategy is None:
        value_strategy = st.floats(allow_nan=False, allow_infinity=False)
    
    return {
        'id': draw(uuid()),
        'frame': draw(st.integers(min_value=0, max_value=10000)),
        'value': draw(value_strategy),
        'easing': draw(st.sampled_from(['linear', 'ease', 'ease-in', 'ease-out', 'ease-in-out', 'hold'])),
        'outHandle': draw(bezier_handle()),
        'inHandle': draw(bezier_handle()),
    }


@composite
def keyframe_list(draw, min_keyframes=0, max_keyframes=100):
    """Generate list of keyframes sorted by frame."""
    keyframes = draw(st.lists(keyframe(), min_size=min_keyframes, max_size=max_keyframes))
    # Sort by frame and deduplicate frames
    seen_frames = set()
    unique_keyframes = []
    for kf in sorted(keyframes, key=lambda k: k['frame']):
        if kf['frame'] not in seen_frames:
            seen_frames.add(kf['frame'])
            unique_keyframes.append(kf)
    return unique_keyframes


# ==============================================================================
# LAYER STRATEGIES
# ==============================================================================

LAYER_TYPES = [
    'solid', 'image', 'video', 'text', 'shape', 'audio',
    'particle', 'camera', 'light', 'model', 'depth', 'pose',
    'spline', 'effect', 'group', 'adjustment', 'null'
]


@composite
def layer_base(draw):
    """Generate valid base layer data."""
    return {
        'id': draw(uuid()),
        'name': draw(st.text(min_size=1, max_size=100)),
        'type': draw(st.sampled_from(LAYER_TYPES)),
        'visible': draw(st.booleans()),
        'locked': draw(st.booleans()),
        'solo': draw(st.booleans()),
        'startFrame': draw(st.integers(min_value=0, max_value=10000)),
        'endFrame': draw(st.integers(min_value=1, max_value=10001)),
        'transform': draw(transform_2d()),
    }


@composite
def solid_layer(draw):
    """Generate valid solid layer."""
    base = draw(layer_base())
    base['type'] = 'solid'
    base['color'] = draw(hex_color())
    return base


@composite
def text_layer(draw):
    """Generate valid text layer."""
    base = draw(layer_base())
    base['type'] = 'text'
    base['text'] = draw(st.text(min_size=1, max_size=1000))
    base['fontSize'] = draw(st.integers(min_value=1, max_value=1000))
    base['fontFamily'] = draw(st.sampled_from(['Arial', 'Helvetica', 'Times', 'Courier']))
    base['color'] = draw(hex_color())
    return base


# ==============================================================================
# EFFECT STRATEGIES
# ==============================================================================

EFFECT_TYPES = [
    'blur', 'glow', 'shadow', 'color-correction', 'distort',
    'noise', 'sharpen', 'vignette', 'chromatic-aberration'
]


@composite
def effect_instance(draw):
    """Generate valid effect instance."""
    return {
        'id': draw(uuid()),
        'name': draw(st.text(min_size=1, max_size=50)),
        'effectKey': draw(st.sampled_from(EFFECT_TYPES)),
        'enabled': draw(st.booleans()),
        'parameters': {},  # Would need effect-specific strategies
    }


# ==============================================================================
# EXPORT STRATEGIES  
# ==============================================================================

EXPORT_FORMATS = ['png', 'jpg', 'webp', 'raw', 'exr']
DEPTH_FORMATS = ['raw', 'depth-anything', 'marigold', 'midas', 'png16']
COLORMAPS = ['grayscale', 'viridis', 'plasma', 'magma', 'inferno', 'turbo']


@composite
def depth_export_settings(draw):
    """Generate valid depth export settings."""
    near = draw(st.floats(min_value=0.001, max_value=100, allow_nan=False))
    far = draw(st.floats(min_value=near + 0.001, max_value=10000, allow_nan=False))
    
    return {
        'nearClip': near,
        'farClip': far,
        'format': draw(st.sampled_from(DEPTH_FORMATS)),
        'colormap': draw(st.sampled_from(COLORMAPS)),
        'normalize': draw(st.booleans()),
        'invert': draw(st.booleans()),
    }


@composite
def camera_export_settings(draw):
    """Generate valid camera export settings."""
    return {
        'format': draw(st.sampled_from(['motionctrl', 'wan-move', 'uni3c', 'cameractrl'])),
        'frameRange': {
            'start': draw(st.integers(min_value=0, max_value=1000)),
            'end': draw(st.integers(min_value=1, max_value=1001)),
        },
        'coordinateSystem': draw(st.sampled_from(['opengl', 'opencv', 'blender'])),
    }


# ==============================================================================
# API PAYLOAD STRATEGIES
# ==============================================================================

@composite
def render_request(draw):
    """Generate valid render request payload."""
    return {
        'project': draw(st.text(min_size=1, max_size=100)),
        'startFrame': draw(st.integers(min_value=0, max_value=10000)),
        'endFrame': draw(st.integers(min_value=1, max_value=10001)),
        'width': draw(dimension()),
        'height': draw(dimension()),
        'format': draw(st.sampled_from(EXPORT_FORMATS)),
        'quality': draw(st.integers(min_value=1, max_value=100)),
    }


# ==============================================================================
# ADVERSARIAL STRATEGIES (for security testing)
# ==============================================================================

def malicious_string():
    """Generate potentially malicious strings for security testing."""
    return st.sampled_from([
        '',  # Empty
        '\x00',  # Null byte
        '../../../etc/passwd',  # Path traversal
        '<script>alert(1)</script>',  # XSS
        "'; DROP TABLE projects; --",  # SQL injection
        '{{constructor.constructor("return this")()}}',  # Prototype pollution
    ]) | st.text(alphabet=st.characters(blacklist_categories=['Cs']), max_size=10000) | st.binary().map(lambda b: b.decode('utf-8', errors='replace'))


@composite
def malformed_project(draw):
    """Generate intentionally malformed project data for robustness testing."""
    return draw(st.one_of(
        st.just(None),
        st.just({}),
        st.just({'version': 'invalid'}),
        st.just({'layers': 'not-an-array'}),
        st.dictionaries(
            st.text(max_size=10),
            st.recursive(
                st.none() | st.booleans() | st.integers() | st.text(max_size=100),
                lambda children: st.lists(children, max_size=5) | st.dictionaries(st.text(max_size=10), children, max_size=5),
                max_leaves=100
            ),
            max_size=50
        ),
    ))
