"""CLI test interface for layer decomposition."""

import argparse
import json
import logging
import sys
from pathlib import Path

from .constants import _model_state
from .decomposition import decompose_image
from .model_management import load_model
from .model_utils import _check_model_exists

logger = logging.getLogger("lattice.layer_decomposition")


def run_decomposition_test(
  input_path: str,
  output_dir: str,
  num_layers: int = 5,
  seed: int = 42,
  resolution: int = 640,
) -> dict:
  """
  Run decomposition test on a single image and save layers as PNGs.

  Args:
      input_path: Path to input image
      output_dir: Directory to save output layers
      num_layers: Number of layers to generate
      seed: Random seed for reproducibility
      resolution: Output resolution bucket (640 or 1024)

  Returns:
      dict with status and list of output file paths
  """
  from PIL import Image as PILImage

  # Ensure output directory exists
  output_path = Path(output_dir)
  output_path.mkdir(parents=True, exist_ok=True)

  # Load input image
  input_path_obj = Path(input_path)
  input_name = input_path_obj.stem
  logger.info(f"Loading image: {input_path}")

  try:
    image = PILImage.open(input_path)
  except Exception as e:
    return {"status": "error", "message": f"Failed to load image: {e}"}

  # Ensure model is loaded
  if not _model_state["loaded"]:
    load_result = load_model()
    if load_result["status"] != "success":
      return load_result

  # Run decomposition
  result = decompose_image(
    image,
    num_layers=num_layers,
    true_cfg_scale=4.0,
    num_inference_steps=50,
    seed=seed,
    resolution=resolution,
  )

  if result["status"] != "success":
    return result

  # Save each layer as PNG
  output_paths = []
  for layer_info in result["layers"]:
    layer_img = layer_info["image"]
    layer_name = f"{input_name}_layer_{layer_info['index']:02d}_{layer_info['label'].lower().replace(' ', '_')}.png"
    output_file = output_path / layer_name

    layer_img.save(output_file, format="PNG")
    output_paths.append(str(output_file))
    logger.info(f"Saved: {output_file}")

  return {
    "status": "success",
    "message": f"Saved {len(output_paths)} layers to {output_dir}",
    "output_paths": output_paths,
  }


def run_batch_decomposition_test(
  input_dir: str,
  output_dir: str,
  num_layers: int = 5,
  seed: int = 42,
  resolution: int = 640,
  extensions: tuple = (".png", ".jpg", ".jpeg", ".webp"),
) -> dict:
  """
  Run decomposition test on all images in a directory.

  Args:
      input_dir: Directory containing input images
      output_dir: Directory to save output layers
      num_layers: Number of layers to generate per image
      seed: Random seed (increments for each image)
      resolution: Output resolution bucket (640 or 1024)
      extensions: File extensions to process

  Returns:
      dict with status and results for each image
  """
  # Find all images
  input_dir_path = Path(input_dir)
  images = [
    str(item_path)
    for item_path in input_dir_path.iterdir()
    if item_path.is_file() and item_path.name.lower().endswith(extensions)
  ]

  if not images:
    return {"status": "error", "message": f"No images found in {input_dir}"}

  logger.info(f"Found {len(images)} images to process")

  results = []
  for i, image_path in enumerate(images):
    logger.info(f"\n{'=' * 60}")
    logger.info(f"Processing {i + 1}/{len(images)}: {Path(image_path).name}")
    logger.info(f"{'=' * 60}")

    result = run_decomposition_test(
      input_path=image_path,
      output_dir=output_dir,
      num_layers=num_layers,
      seed=seed + i,  # Different seed per image
      resolution=resolution,
    )
    results.append({"input": image_path, **result})

  # Summarize
  successful = sum(1 for r in results if r["status"] == "success")
  return {
    "status": "success" if successful == len(results) else "partial",
    "message": f"Processed {successful}/{len(results)} images",
    "results": results,
  }


def main():
  """CLI entry point."""
  import asyncio

  from .model_management import download_model, get_model_status
  from .model_utils import verify_model_integrity

  logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
  )

  parser = argparse.ArgumentParser(description="Lattice Layer Decomposition Test")
  parser.add_argument("input", help="Input image path or directory")
  parser.add_argument("--output", "-o", default="./decomp_output", help="Output directory")
  parser.add_argument("--layers", "-n", type=int, default=5, help="Number of layers (3-8)")
  parser.add_argument("--seed", "-s", type=int, default=42, help="Random seed")
  parser.add_argument(
    "--resolution",
    "-r",
    type=int,
    default=640,
    choices=[640, 1024],
    help="Output resolution bucket",
  )
  parser.add_argument("--download", action="store_true", help="Download model if needed")
  parser.add_argument("--status", action="store_true", help="Show model status and exit")
  parser.add_argument("--verify", action="store_true", help="Verify model integrity and exit")

  args = parser.parse_args()

  # Status check
  if args.status:
    print(json.dumps(get_model_status(), indent=2))
    sys.exit(0)

  # Verify check
  if args.verify:
    print(json.dumps(verify_model_integrity(verbose=True), indent=2))
    sys.exit(0)

  # Download if requested (for manual pre-download to local path)
  if args.download:
    print("Downloading model to local ComfyUI folder...")
    result = asyncio.run(download_model())
    print(f"Download result: {result}")
    if result["status"] != "success":
      sys.exit(1)

  # Note: Model will auto-download from HuggingFace if not cached
  # The --download flag is for explicit pre-download to ComfyUI models folder
  if not _check_model_exists():
    print("NOTE: Model not in local folder. Will download from HuggingFace (~28GB).")
    print("This may take a while on first run...")

  # Determine if input is file or directory
  input_path = Path(args.input)
  if input_path.is_file():
    result = run_decomposition_test(
      input_path=str(input_path),
      output_dir=args.output,
      num_layers=args.layers,
      seed=args.seed,
      resolution=args.resolution,
    )
  elif input_path.is_dir():
    result = run_batch_decomposition_test(
      input_dir=args.input,
      output_dir=args.output,
      num_layers=args.layers,
      seed=args.seed,
      resolution=args.resolution,
    )
  else:
    print(f"ERROR: Input path does not exist: {args.input}")
    sys.exit(1)

  print("\n" + "=" * 60)
  print("RESULT:")
  print("=" * 60)
  print(json.dumps(result, indent=2))

  sys.exit(0 if result["status"] == "success" else 1)


if __name__ == "__main__":
  main()
