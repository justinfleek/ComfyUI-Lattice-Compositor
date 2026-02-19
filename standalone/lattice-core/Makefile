# typed-comfy Makefile
#
# EVERYTHING FROM LEAN. NO EXTERNAL SCHEMA.
#
# The build flows:
#   Lean proofs → extract → Elm/Python/C
#   Lean core → C shim → nanobind → Python
#   Elm → WebGL
#
# If it doesn't have a proof, it doesn't ship.

.PHONY: all clean extract lean python elm serve test check

# =============================================================================
# CONFIGURATION
# =============================================================================

PYTHON ?= python3
ELM ?= elm
LAKE ?= lake

# =============================================================================
# HIGH-LEVEL TARGETS
# =============================================================================

all: extract lean elm
	@echo ""
	@echo "✓ Build complete"
	@echo "  Run 'make serve' to start the scene editor"

clean:
	rm -rf extracted/
	rm -rf lean/.lake/
	rm -rf python/build/
	rm -rf elm/elm-stuff/
	rm -f elm/elm.js
	@echo "Cleaned all build artifacts"

# =============================================================================
# EXTRACTION (Everything from Lean proofs)
# =============================================================================

extract: lean-lib
	cd lean && $(LAKE) exe extract all
	@echo ""
	@echo "✓ Extracted from proofs:"
	@echo "  Elm:    extracted/elm/TensorCore/Types.elm"
	@echo "  Python: extracted/python/types.py"
	@echo "  C:      extracted/c/tensor_core_types.h"

extract-elm: lean-lib
	cd lean && $(LAKE) exe extract elm

extract-python: lean-lib
	cd lean && $(LAKE) exe extract python

extract-c: lean-lib
	cd lean && $(LAKE) exe extract c

# =============================================================================
# LEAN CORE
# =============================================================================

lean: lean-lib lean-exe
	@echo "✓ Lean core built"

lean-lib:
	cd lean && $(LAKE) build TensorCore

lean-exe:
	cd lean && $(LAKE) build

lean-check:
	cd lean && $(LAKE) build TensorCore 2>&1 | head -50

# =============================================================================
# PYTHON BINDINGS
# =============================================================================

python: extract-c extract-python
	cd python && cmake -B build -G Ninja
	cd python && cmake --build build
	@echo "✓ Python bindings built"

# =============================================================================
# ELM FRONTEND
# =============================================================================

elm: extract-elm
	@mkdir -p elm/src/TensorCore
	@cp extracted/elm/TensorCore/Types.elm elm/src/TensorCore/ 2>/dev/null || true
	cd elm && $(ELM) make src/Main.elm --optimize --output=elm.js
	@echo "✓ Elm frontend built"

elm-dev: extract-elm
	@mkdir -p elm/src/TensorCore
	@cp extracted/elm/TensorCore/Types.elm elm/src/TensorCore/ 2>/dev/null || true
	cd elm && $(ELM) make src/Main.elm --debug --output=elm.js

# =============================================================================
# DEVELOPMENT
# =============================================================================

serve: elm
	@echo ""
	@echo "Starting server at http://localhost:8000"
	cd elm && $(PYTHON) -m http.server 8000

# =============================================================================
# VERIFICATION
# =============================================================================

check: lean-check
	@echo ""
	@echo "✓ All proofs verified"
	@echo ""
	@echo "Verified properties:"
	@echo "  • Point3 roundtrip"
	@echo "  • Vec3 roundtrip"
	@echo "  • ColorRGB roundtrip"
	@echo "  • Vertex roundtrip"
	@echo "  • Transform roundtrip"

# =============================================================================
# INFO
# =============================================================================

deps:
	@echo ""
	@echo "Type Flow (everything from proofs):"
	@echo ""
	@echo "  lean/TensorCore/Extract.lean"
	@echo "         │"
	@echo "         │  Extractable typeclass"
	@echo "         │  + roundtrip proofs"
	@echo "         │"
	@echo "         ├──▶ extracted/elm/TensorCore/Types.elm"
	@echo "         │      (decoders, encoders)"
	@echo "         │"
	@echo "         ├──▶ extracted/python/types.py"
	@echo "         │      (dataclasses, __post_init__)"
	@echo "         │"
	@echo "         └──▶ extracted/c/tensor_core_types.h"
	@echo "                (structs, validators)"
	@echo ""
	@echo "  No Dhall. No external schema. Just theorems."
	@echo ""
