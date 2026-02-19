#!/bin/bash
# Test script for Weyl Layer Decomposition
# Processes test images from screenshots folder

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

INPUT_DIR="$PROJECT_ROOT/screenshots"
OUTPUT_DIR="$PROJECT_ROOT/screenshots/decomp"
PYTHON_SCRIPT="$PROJECT_ROOT/nodes/weyl_layer_decomposition.py"

NUM_LAYERS=5
SEED=42

echo "=============================================="
echo "Weyl Layer Decomposition Test"
echo "=============================================="
echo "Input directory: $INPUT_DIR"
echo "Output directory: $OUTPUT_DIR"
echo "Number of layers: $NUM_LAYERS"
echo ""

# Create output directory
mkdir -p "$OUTPUT_DIR"

# Check if we have Python with required dependencies
if ! command -v python &> /dev/null; then
    echo "ERROR: Python not found"
    exit 1
fi

# Check model status first
echo "Checking model status..."
python "$PYTHON_SCRIPT" dummy --status 2>/dev/null || true

# Run decomposition on specific test images
echo ""
echo "Processing test images..."

# Process specific test files (exclude the current_implementations.png which is a screenshot)
for img in "$INPUT_DIR/anime-decomposition-test-2.jpg" "$INPUT_DIR/nature-photo-for-decomp.webp"; do
    if [[ -f "$img" ]]; then
        echo ""
        echo "Processing: $(basename "$img")"
        python "$PYTHON_SCRIPT" "$img" --output "$OUTPUT_DIR" --layers $NUM_LAYERS --seed $SEED
        SEED=$((SEED + 1))
    fi
done

echo ""
echo "=============================================="
echo "Test complete!"
echo "Output saved to: $OUTPUT_DIR"
echo "=============================================="

# List output files
if [[ -d "$OUTPUT_DIR" ]]; then
    echo ""
    echo "Generated files:"
    ls -la "$OUTPUT_DIR"/*.png 2>/dev/null || echo "No PNG files generated yet"
fi
