"""Constants and availability flags for vectorization services."""

# Try to import vtracer (pip install vtracer)
try:
  import vtracer

  VTRACER_AVAILABLE = True
except ImportError:
  VTRACER_AVAILABLE = False
  print("[Lattice Vectorize] vtracer not installed. Run: pip install vtracer")

# StarVector is optional and loaded lazily
# Note: These are modified by handlers, so they need to be mutable
STARVECTOR_AVAILABLE = False
STARVECTOR_MODEL = None
STARVECTOR_LOADING = False
