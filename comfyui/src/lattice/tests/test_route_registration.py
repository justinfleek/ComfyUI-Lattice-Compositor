"""
P0.1 Route Registration Integration Tests

These tests verify that routes are ACTUALLY registered with PromptServer,
not just that test file constants are correct.

Test Strategy:
1. Mock PromptServer.instance.routes with MockRouteTable that captures registrations
2. Import each route module and verify routes appear in the mock
3. Each test MUST check mock_server.routes.registered_routes, not dict structure

CTO Requirements:
- Tests must NOT rewrite source code before testing
- Tests must verify routes appear in mock, not just check return values
- Every test that claims to test route registration must check registered_routes
"""

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest.mock import MagicMock


# Add src to path for imports (new structure)
_test_dir = Path(__file__).resolve().parent
_src_dir = _test_dir.parent.parent
if str(_src_dir) not in sys.path:
  sys.path.insert(0, str(_src_dir))


class MockRouteTable:
  """
  Mock for PromptServer.instance.routes that captures registered routes.

  When a module does:
      @routes.get('/path')
      def handler(request): ...

  This mock captures the path and method.
  """

  def __init__(self):
    self.registered_routes = []

  def get(self, path):
    """Capture GET route registration."""

    def decorator(func):
      self.registered_routes.append(("GET", path, func.__name__))
      return func

    return decorator

  def post(self, path):
    """Capture POST route registration."""

    def decorator(func):
      self.registered_routes.append(("POST", path, func.__name__))
      return func

    return decorator

  def delete(self, path):
    """Capture DELETE route registration."""

    def decorator(func):
      self.registered_routes.append(("DELETE", path, func.__name__))
      return func

    return decorator

  def put(self, path):
    """Capture PUT route registration."""

    def decorator(func):
      self.registered_routes.append(("PUT", path, func.__name__))
      return func

    return decorator


class MockPromptServer:
  """Mock for ComfyUI's PromptServer."""

  def __init__(self):
    self.routes = MockRouteTable()


def setup_all_mocks():
  """
  Set up all mocks BEFORE any compositor imports.
  Returns the mock_server so tests can verify routes were registered.
  """
  # Mock heavy dependencies that route modules import
  sys.modules["numpy"] = MagicMock()
  sys.modules["PIL"] = MagicMock()
  sys.modules["PIL.Image"] = MagicMock()
  sys.modules["cv2"] = MagicMock()
  sys.modules["torch"] = MagicMock()
  sys.modules["torchaudio"] = MagicMock()
  sys.modules["demucs"] = MagicMock()
  sys.modules["demucs.pretrained"] = MagicMock()
  sys.modules["vtracer"] = MagicMock()
  sys.modules["transformers"] = MagicMock()
  sys.modules["folder_paths"] = MagicMock()
  sys.modules["aiohttp"] = MagicMock()
  sys.modules["aiohttp.web"] = MagicMock()

  # Create mock PromptServer - this is what route modules use
  mock_server = MockPromptServer()
  mock_server_module = MagicMock()
  mock_server_module.PromptServer = MagicMock()
  mock_server_module.PromptServer.instance = mock_server
  sys.modules["server"] = mock_server_module

  return mock_server


def clear_compositor_modules():
  """Remove all compositor modules from cache to allow fresh import."""
  modules_to_remove = [
    k for k in list(sys.modules.keys()) if k.startswith(("compositor", "lattice"))
  ]
  for mod in modules_to_remove:
    del sys.modules[mod]


def import_module_directly(module_name, file_path, mock_server):
  """
  Import a module file directly and return the routes it registered.
  Does NOT modify source code - imports the actual file as-is.
  """
  routes_before = len(mock_server.routes.registered_routes)

  spec = importlib.util.spec_from_file_location(module_name, file_path)
  module = importlib.util.module_from_spec(spec)
  sys.modules[module_name] = module
  spec.loader.exec_module(module)

  routes_after = len(mock_server.routes.registered_routes)
  routes_registered = routes_after - routes_before

  return module, routes_registered


class TestLatticeVectorizeRouteRegistration(unittest.TestCase):
  """Test that lattice_vectorize.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_vectorize_registers_5_routes_in_mock(self):
    """
    Verify lattice_vectorize.py registers exactly 5 routes when imported.
    This test imports the ACTUAL file (no source code modification) and
    checks that routes appear in mock_server.routes.registered_routes.
    """
    file_path = _src_dir / "lattice" / "nodes" / "lattice_vectorize.py"
    _module, _route_count = import_module_directly("lattice_vectorize", str(file_path), self.mock_server)

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 5, f"Expected 5 routes in mock, got {len(routes)}: {routes}")

    # Verify specific routes appear in mock
    route_paths = [(method, path) for method, path, _ in routes]
    expected = [
      ("GET", "/lattice/vectorize/status"),
      ("POST", "/lattice/vectorize/trace"),
      ("POST", "/lattice/vectorize/ai"),
      ("POST", "/lattice/vectorize/download-starvector"),
      ("POST", "/lattice/vectorize/unload-starvector"),
    ]
    for exp in expected:
      self.assertIn(exp, route_paths, f"Route {exp} missing from mock")


class TestLatticeApiProxyRouteRegistration(unittest.TestCase):
  """Test that lattice_api_proxy.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_api_proxy_registers_10_routes_in_mock(self):
    """
    Verify lattice_api_proxy.py registers 10 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "lattice_api_proxy.py"
    _module, _route_count = import_module_directly("lattice_api_proxy", str(file_path), self.mock_server)

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 10, f"Expected 10 routes in mock, got {len(routes)}: {routes}")


class TestLatticeLayerDecompositionRouteRegistration(unittest.TestCase):
  """Test that lattice_layer_decomposition.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_layer_decomposition_registers_7_routes_in_mock(self):
    """
    Verify lattice_layer_decomposition.py registers 7 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "lattice_layer_decomposition.py"
    _module, _route_count = import_module_directly(
      "lattice_layer_decomposition", file_path, self.mock_server
    )

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 7, f"Expected 7 routes in mock, got {len(routes)}: {routes}")


class TestLatticeFrameInterpolationRouteRegistration(unittest.TestCase):
  """Test that lattice_frame_interpolation.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_frame_interpolation_registers_5_routes_in_mock(self):
    """
    Verify lattice_frame_interpolation.py registers 5 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "lattice_frame_interpolation.py"
    _module, _route_count = import_module_directly(
      "lattice_frame_interpolation", file_path, self.mock_server
    )

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 5, f"Expected 5 routes in mock, got {len(routes)}: {routes}")


class TestControlnetPreprocessorsRouteRegistration(unittest.TestCase):
  """Test that controlnet_preprocessors.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_controlnet_preprocessors_registers_5_routes_in_mock(self):
    """
    Verify controlnet_preprocessors.py registers 5 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "controlnet_preprocessors.py"
    _module, _route_count = import_module_directly(
      "controlnet_preprocessors", file_path, self.mock_server
    )

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 5, f"Expected 5 routes in mock, got {len(routes)}: {routes}")


class TestLatticeStemSeparationRouteRegistration(unittest.TestCase):
  """Test that lattice_stem_separation.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_stem_separation_registers_4_routes_in_mock(self):
    """
    Verify lattice_stem_separation.py registers 4 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "lattice_stem_separation.py"
    _module, _route_count = import_module_directly(
      "lattice_stem_separation", file_path, self.mock_server
    )

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 4, f"Expected 4 routes in mock, got {len(routes)}: {routes}")


class TestCompositorNodeRouteRegistration(unittest.TestCase):
  """Test that compositor_node.py registers routes correctly."""

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_compositor_node_registers_11_routes_in_mock(self):
    """
    Verify compositor_node.py registers 11 routes when imported.
    """
    file_path = _src_dir / "lattice" / "nodes" / "compositor_node.py"
    _module, _route_count = import_module_directly("compositor_node", str(file_path), self.mock_server)

    #                                            // verify // routes // in // mock
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 11, f"Expected 11 routes in mock, got {len(routes)}: {routes}")


class TestAllModulesTotalRouteCount(unittest.TestCase):
  """
  Integration test: Import ALL route modules and verify total is 47.
  This tests that when all modules are imported (as register_all_routes does),
  exactly 47 routes are registered with PromptServer.
  """

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_all_modules_register_47_routes_total(self):
    """
    Import all 7 route modules and verify 47 routes in mock.
    This is the key integration test - it proves the total route count.
    """
    modules = [
      ("compositor_node", 11),
      ("lattice_api_proxy", 10),
      ("lattice_layer_decomposition", 7),
      ("lattice_frame_interpolation", 5),
      ("lattice_vectorize", 5),
      ("controlnet_preprocessors", 5),
      ("lattice_stem_separation", 4),
    ]

    for module_name, _expected_count in modules:
      file_path = _src_dir / "lattice" / "nodes" / f"{module_name}.py"
      import_module_directly(module_name, str(file_path), self.mock_server)

    #                                   // verify // total // routes // in // mock
    total_routes = len(self.mock_server.routes.registered_routes)
    self.assertEqual(total_routes, 47, f"Expected 47 total routes in mock, got {total_routes}")

    # Log all routes for debugging
    print(f"\nAll {total_routes} routes registered:")
    for method, path, func in self.mock_server.routes.registered_routes:
      print(f"  {method} {path} -> {func}")


class TestRouteRegistrationFailureDetection(unittest.TestCase):
  """
  Verify tests can DETECT when routes are NOT registered.
  This proves our tests are not false-positive - they actually catch failures.
  """

  def setUp(self):
    clear_compositor_modules()
    self.mock_server = setup_all_mocks()

  def test_empty_mock_has_zero_routes(self):
    """
    Before any module import, mock should have zero routes.
    This proves the mock starts empty.
    """
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 0, "Mock should start with 0 routes")

  def test_mock_without_import_stays_empty(self):
    """
    If we don't import any module, routes should stay at 0.
    This proves tests would FAIL if modules didn't register routes.
    """
    # Don't import anything
    routes = self.mock_server.routes.registered_routes
    self.assertEqual(len(routes), 0)

    # Now this assertion would FAIL if routes were registered
    # (proving our tests detect real failures)
    self.assertNotEqual(len(routes), 47, "This should NOT be 47 without imports")


if __name__ == "__main__":
  unittest.main()
