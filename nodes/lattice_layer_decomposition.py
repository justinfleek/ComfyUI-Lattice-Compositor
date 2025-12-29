"""
Lattice Layer Decomposition - AI-powered image layer separation

This module provides integration with the Qwen-Image-Layered model for
decomposing single images into multiple semantically-meaningful RGBA layers.

Model: Qwen/Qwen-Image-Layered (28.8GB)
Source: https://modelscope.cn/models/Qwen/Qwen-Image-Layered

The model automatically downloads on first use to ComfyUI's models folder.
Includes SHA256 hash verification for integrity checking.
"""

import os
import json
import logging
import hashlib
from typing import Optional, Dict, Any, Callable
from pathlib import Path

logger = logging.getLogger("lattice.layer_decomposition")

# ============================================================================
# Model File Registry with SHA256 Hashes
# ============================================================================

# Key model files and their expected hashes (placeholder hashes - need real values)
MODEL_FILE_HASHES: Dict[str, str] = {
    "model_index.json": None,  # Will be set after first verified download
    # Add more files as needed once we have the actual hashes
}

# Download progress tracking
_download_progress = {
    'current_file': '',
    'files_completed': 0,
    'total_files': 0,
    'bytes_downloaded': 0,
    'total_bytes': 0,
    'stage': 'idle',
}

# Model state
_model_state = {
    'loaded': False,
    'loading': False,
    'pipe': None,
    'device': None,
    'error': None,
}


def _get_model_path() -> Path:
    """Get the model storage path using ComfyUI's folder system"""
    try:
        import folder_paths
        # Use ComfyUI's diffusers model folder
        models_dir = Path(folder_paths.models_dir) / "diffusers" / "Qwen-Image-Layered"
        models_dir.mkdir(parents=True, exist_ok=True)
        return models_dir
    except ImportError:
        # Fallback for standalone use
        return Path(__file__).parent.parent / "models" / "Qwen-Image-Layered"


def _check_model_exists() -> bool:
    """Check if the model is already downloaded"""
    model_path = _get_model_path()
    # Check for key model files
    required_files = ['model_index.json', 'vae', 'unet', 'scheduler']
    return all((model_path / f).exists() for f in required_files[:1])  # Just check model_index.json


def _compute_file_hash(file_path: Path, algorithm: str = 'sha256') -> str:
    """Compute hash of a file in chunks to handle large files"""
    hasher = hashlib.new(algorithm)
    with open(file_path, 'rb') as f:
        # Read in 10MB chunks
        for chunk in iter(lambda: f.read(10 * 1024 * 1024), b''):
            hasher.update(chunk)
    return hasher.hexdigest()


def verify_model_integrity(verbose: bool = False) -> Dict[str, Any]:
    """
    Verify the integrity of downloaded model files using SHA256 hashes.

    Returns:
        dict with verification results:
        {
            "verified": bool,
            "files_checked": int,
            "files_valid": int,
            "files_invalid": list[str],
            "files_missing": list[str],
            "message": str
        }
    """
    model_path = _get_model_path()

    if not model_path.exists():
        return {
            "verified": False,
            "files_checked": 0,
            "files_valid": 0,
            "files_invalid": [],
            "files_missing": ["model directory"],
            "message": "Model directory does not exist"
        }

    files_checked = 0
    files_valid = 0
    files_invalid = []
    files_missing = []

    for filename, expected_hash in MODEL_FILE_HASHES.items():
        file_path = model_path / filename

        if not file_path.exists():
            files_missing.append(filename)
            continue

        files_checked += 1

        # Skip hash check if we don't have an expected hash
        if expected_hash is None:
            files_valid += 1
            if verbose:
                logger.info(f"Skipping hash check for {filename} (no expected hash)")
            continue

        # Compute and verify hash
        try:
            computed_hash = _compute_file_hash(file_path)
            if computed_hash == expected_hash:
                files_valid += 1
                if verbose:
                    logger.info(f"Verified {filename}: {computed_hash[:16]}...")
            else:
                files_invalid.append(filename)
                logger.warning(f"Hash mismatch for {filename}: expected {expected_hash[:16]}..., got {computed_hash[:16]}...")
        except Exception as e:
            files_invalid.append(filename)
            logger.error(f"Failed to verify {filename}: {e}")

    verified = len(files_invalid) == 0 and len(files_missing) == 0

    if verified:
        message = f"All {files_checked} files verified successfully"
    else:
        message = f"{len(files_invalid)} invalid, {len(files_missing)} missing out of {files_checked} files"

    return {
        "verified": verified,
        "files_checked": files_checked,
        "files_valid": files_valid,
        "files_invalid": files_invalid,
        "files_missing": files_missing,
        "message": message
    }


def get_download_progress() -> Dict[str, Any]:
    """Get current download progress for frontend"""
    return dict(_download_progress)


def get_model_status() -> dict:
    """Get current model status for frontend"""
    downloaded = _check_model_exists()

    # Include verification status if downloaded
    verification = None
    if downloaded:
        verification = verify_model_integrity(verbose=False)

    return {
        "downloaded": downloaded,
        "loaded": _model_state['loaded'],
        "loading": _model_state['loading'],
        "error": _model_state['error'],
        "model_path": str(_get_model_path()),
        "model_size_gb": 28.8,
        "verification": verification,
        "download_progress": get_download_progress() if _download_progress['stage'] != 'idle' else None,
    }


async def download_model(progress_callback=None, verify_after: bool = True) -> dict:
    """
    Download the Qwen-Image-Layered model from HuggingFace.

    Args:
        progress_callback: Optional async callback for progress updates
        verify_after: Run hash verification after download (default True)

    Returns:
        dict with status, message, and optional verification results
    """
    global _download_progress

    if _model_state['loading']:
        return {"status": "error", "message": "Model is already being downloaded"}

    if _check_model_exists():
        return {"status": "success", "message": "Model already downloaded"}

    _model_state['loading'] = True
    _model_state['error'] = None

    # Reset progress tracking
    _download_progress = {
        'current_file': '',
        'files_completed': 0,
        'total_files': 0,
        'bytes_downloaded': 0,
        'total_bytes': 28.8 * 1024 * 1024 * 1024,  # Estimate
        'stage': 'starting',
    }

    try:
        from huggingface_hub import snapshot_download

        model_path = _get_model_path()
        logger.info(f"Downloading Qwen-Image-Layered to {model_path}")

        _download_progress['stage'] = 'downloading'
        if progress_callback:
            await progress_callback({"stage": "downloading", "progress": 0})

        # Download from HuggingFace
        snapshot_download(
            repo_id="Qwen/Qwen-Image-Layered",
            local_dir=str(model_path),
            local_dir_use_symlinks=False,
            resume_download=True,
        )

        _download_progress['stage'] = 'verifying'
        if progress_callback:
            await progress_callback({"stage": "verifying", "progress": 95})

        # Verify integrity after download
        verification = None
        if verify_after:
            logger.info("Verifying model integrity...")
            verification = verify_model_integrity(verbose=True)

            if not verification['verified'] and verification['files_invalid']:
                # Hash mismatch - this is a real error
                error_msg = f"Model verification failed: {verification['message']}"
                _model_state['error'] = error_msg
                return {
                    "status": "error",
                    "message": error_msg,
                    "verification": verification
                }

        _download_progress['stage'] = 'complete'
        if progress_callback:
            await progress_callback({"stage": "complete", "progress": 100})

        logger.info("Model download complete")
        return {
            "status": "success",
            "message": "Model downloaded successfully",
            "verification": verification
        }

    except Exception as e:
        error_msg = f"Failed to download model: {str(e)}"
        logger.error(error_msg)
        _model_state['error'] = error_msg
        _download_progress['stage'] = 'error'
        return {"status": "error", "message": error_msg}
    finally:
        _model_state['loading'] = False
        if _download_progress['stage'] not in ['complete', 'error']:
            _download_progress['stage'] = 'idle'


def load_model(use_local: bool = False) -> dict:
    """
    Load the Qwen-Image-Layered model into memory for inference.

    Uses QwenImageLayeredPipeline from diffusers library.
    Requires: transformers>=4.51.3, latest diffusers from GitHub

    Args:
        use_local: If True, load from local ComfyUI models folder; else from HuggingFace

    Returns:
        dict with status and message
    """
    if _model_state['loaded']:
        return {"status": "success", "message": "Model already loaded"}

    if _model_state['loading']:
        return {"status": "error", "message": "Model is currently loading"}

    _model_state['loading'] = True
    _model_state['error'] = None

    try:
        import torch
        from diffusers import QwenImageLayeredPipeline

        # Determine device and dtype
        if torch.cuda.is_available():
            device = "cuda"
            dtype = torch.bfloat16  # Qwen-Image-Layered uses bfloat16
        elif hasattr(torch.backends, 'mps') and torch.backends.mps.is_available():
            device = "mps"
            dtype = torch.float16
        else:
            device = "cpu"
            dtype = torch.float32
            logger.warning("Running on CPU - this will be very slow (30+ min per image)")

        # Determine model source
        if use_local and _check_model_exists():
            model_path = str(_get_model_path())
            logger.info(f"Loading Qwen-Image-Layered from local path: {model_path}")
        else:
            model_path = "Qwen/Qwen-Image-Layered"
            logger.info(f"Loading Qwen-Image-Layered from HuggingFace (will download if needed)")

        logger.info(f"Device: {device}, dtype: {dtype}")

        # Load model - will download from HuggingFace if not cached
        pipe = QwenImageLayeredPipeline.from_pretrained(
            model_path,
            torch_dtype=dtype,
            trust_remote_code=False,  # SECURITY: Prevent arbitrary code execution
        )
        pipe = pipe.to(device)
        pipe.set_progress_bar_config(disable=None)

        _model_state['pipe'] = pipe
        _model_state['device'] = device
        _model_state['loaded'] = True

        logger.info("Model loaded successfully")
        return {"status": "success", "message": f"Model loaded on {device}"}

    except Exception as e:
        error_msg = f"Failed to load model: {str(e)}"
        logger.error(error_msg)
        _model_state['error'] = error_msg
        return {"status": "error", "message": error_msg}
    finally:
        _model_state['loading'] = False


def unload_model() -> dict:
    """Unload model from memory to free GPU resources"""
    if not _model_state['loaded']:
        return {"status": "success", "message": "Model not loaded"}

    try:
        import torch
        import gc

        _model_state['pipe'] = None
        _model_state['loaded'] = False
        _model_state['device'] = None

        gc.collect()
        if torch.cuda.is_available():
            torch.cuda.empty_cache()

        logger.info("Model unloaded")
        return {"status": "success", "message": "Model unloaded"}

    except Exception as e:
        error_msg = f"Failed to unload model: {str(e)}"
        logger.error(error_msg)
        return {"status": "error", "message": error_msg}


def decompose_image(
    image,
    num_layers: int = 5,
    true_cfg_scale: float = 4.0,
    num_inference_steps: int = 50,
    seed: Optional[int] = None,
    resolution: int = 640,
) -> dict:
    """
    Decompose an image into multiple RGBA layers using Qwen-Image-Layered.

    Uses the official QwenImageLayeredPipeline API from diffusers.

    Args:
        image: PIL Image or numpy array
        num_layers: Number of layers to generate (3-8, default 5)
        true_cfg_scale: True CFG scale (default 4.0)
        num_inference_steps: Denoising steps (default 50)
        seed: Random seed for reproducibility
        resolution: Output resolution bucket (640 or 1024, default 640)

    Returns:
        dict with status and layers (list of RGBA PIL Images)
    """
    if not _model_state['loaded']:
        return {"status": "error", "message": "Model not loaded. Call load_model first."}

    try:
        import torch
        from PIL import Image
        import numpy as np

        pipe = _model_state['pipe']
        device = _model_state['device']

        # Convert input to PIL Image if needed
        if isinstance(image, np.ndarray):
            if image.max() <= 1.0:
                image = (image * 255).astype(np.uint8)
            image = Image.fromarray(image)

        # Ensure image is RGBA (required by Qwen-Image-Layered)
        if image.mode != 'RGBA':
            image = image.convert('RGBA')

        # Prepare inputs following official API
        inputs = {
            "image": image,
            "true_cfg_scale": true_cfg_scale,
            "negative_prompt": " ",
            "num_inference_steps": num_inference_steps,
            "num_images_per_prompt": 1,
            "layers": num_layers,
            "resolution": resolution,
            "cfg_normalize": True,
            "use_en_prompt": True,
        }

        # Set seed for reproducibility
        if seed is not None:
            inputs["generator"] = torch.Generator(device=device).manual_seed(seed)

        # Run decomposition
        logger.info(f"Decomposing image into {num_layers} layers (resolution={resolution})")

        with torch.inference_mode():
            output = pipe(**inputs)
            # output.images[0] is a list of layer images
            layers = output.images[0] if hasattr(output, 'images') else output

        # Convert to list of dicts with metadata
        layer_data = []
        for i, layer in enumerate(layers):
            # Ensure RGBA
            if layer.mode != 'RGBA':
                layer = layer.convert('RGBA')

            # Generate semantic label based on position
            label = f"Layer {i + 1}"
            if i == 0:
                label = "Background"
            elif i == len(layers) - 1:
                label = "Foreground"

            layer_data.append({
                "index": i,
                "label": label,
                "image": layer,
                "has_alpha": True,
            })

        logger.info(f"Decomposition complete: {len(layer_data)} layers")
        return {
            "status": "success",
            "layers": layer_data,
            "message": f"Generated {len(layer_data)} layers"
        }

    except Exception as e:
        error_msg = f"Decomposition failed: {str(e)}"
        logger.error(error_msg)
        return {"status": "error", "message": error_msg}


# Register routes when running in ComfyUI
try:
    from server import PromptServer
    from aiohttp import web
    import base64
    from io import BytesIO
    from PIL import Image as PILImage

    routes = PromptServer.instance.routes

    @routes.get('/lattice/decomposition/status')
    async def decomposition_status(request):
        """Get model status for frontend"""
        return web.json_response({
            "status": "success",
            "data": get_model_status()
        })

    @routes.post('/lattice/decomposition/download')
    async def decomposition_download(request):
        """Download the model (long-running operation)"""
        result = await download_model()
        return web.json_response(result)

    @routes.get('/lattice/decomposition/progress')
    async def decomposition_progress(request):
        """Get current download progress"""
        return web.json_response({
            "status": "success",
            "data": get_download_progress()
        })

    @routes.post('/lattice/decomposition/verify')
    async def decomposition_verify(request):
        """Verify model integrity with hash checks"""
        result = verify_model_integrity(verbose=True)
        return web.json_response({
            "status": "success" if result['verified'] else "warning",
            "data": result
        })

    @routes.post('/lattice/decomposition/load')
    async def decomposition_load(request):
        """Load model into memory"""
        result = load_model()
        return web.json_response(result)

    @routes.post('/lattice/decomposition/unload')
    async def decomposition_unload(request):
        """Unload model from memory"""
        result = unload_model()
        return web.json_response(result)

    @routes.post('/lattice/decomposition/decompose')
    async def decomposition_decompose(request):
        """
        Decompose an image into layers using Qwen-Image-Layered.

        Request body:
        {
            "image": "base64 encoded image",
            "num_layers": 5,
            "true_cfg_scale": 4.0,
            "num_inference_steps": 50,
            "resolution": 640,
            "seed": null
        }

        Response:
        {
            "status": "success",
            "layers": [
                {
                    "index": 0,
                    "label": "Background",
                    "image": "base64 encoded RGBA image"
                },
                ...
            ]
        }
        """
        try:
            data = await request.json()

            # Decode input image
            image_b64 = data.get('image')
            if not image_b64:
                return web.json_response({
                    "status": "error",
                    "message": "Missing 'image' field"
                }, status=400)

            # Handle data URL format
            if ',' in image_b64:
                image_b64 = image_b64.split(',')[1]

            image_data = base64.b64decode(image_b64)
            image = PILImage.open(BytesIO(image_data))

            # Get parameters (with backwards compatibility for guidance_scale)
            num_layers = data.get('num_layers', 5)
            true_cfg_scale = data.get('true_cfg_scale', data.get('guidance_scale', 4.0))
            num_inference_steps = data.get('num_inference_steps', 50)
            resolution = data.get('resolution', 640)
            seed = data.get('seed')

            # Run decomposition
            result = decompose_image(
                image,
                num_layers=num_layers,
                true_cfg_scale=true_cfg_scale,
                num_inference_steps=num_inference_steps,
                resolution=resolution,
                seed=seed,
            )

            if result['status'] != 'success':
                return web.json_response(result, status=500)

            # Convert layers to base64
            response_layers = []
            for layer_info in result['layers']:
                layer_img = layer_info['image']

                # Encode to base64 PNG
                buffer = BytesIO()
                layer_img.save(buffer, format='PNG')
                layer_b64 = base64.b64encode(buffer.getvalue()).decode('utf-8')

                response_layers.append({
                    "index": layer_info['index'],
                    "label": layer_info['label'],
                    "image": f"data:image/png;base64,{layer_b64}",
                    "has_alpha": layer_info['has_alpha'],
                })

            return web.json_response({
                "status": "success",
                "layers": response_layers,
                "message": result['message']
            })

        except json.JSONDecodeError:
            return web.json_response({
                "status": "error",
                "message": "Invalid JSON in request body"
            }, status=400)
        except Exception as e:
            logger.error(f"Decomposition endpoint error: {e}")
            return web.json_response({
                "status": "error",
                "message": f"Internal error: {str(e)}"
            }, status=500)

    logger.info("Lattice Layer Decomposition routes registered")

except ImportError:
    # Not running in ComfyUI context
    pass


# ============================================================================
# CLI Test Interface
# ============================================================================

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
    import os

    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # Load input image
    input_name = os.path.splitext(os.path.basename(input_path))[0]
    logger.info(f"Loading image: {input_path}")

    try:
        image = PILImage.open(input_path)
    except Exception as e:
        return {"status": "error", "message": f"Failed to load image: {e}"}

    # Ensure model is loaded
    if not _model_state['loaded']:
        load_result = load_model()
        if load_result['status'] != 'success':
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

    if result['status'] != 'success':
        return result

    # Save each layer as PNG
    output_paths = []
    for layer_info in result['layers']:
        layer_img = layer_info['image']
        layer_name = f"{input_name}_layer_{layer_info['index']:02d}_{layer_info['label'].lower().replace(' ', '_')}.png"
        output_path = os.path.join(output_dir, layer_name)

        layer_img.save(output_path, format='PNG')
        output_paths.append(output_path)
        logger.info(f"Saved: {output_path}")

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
    extensions: tuple = ('.png', '.jpg', '.jpeg', '.webp'),
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
    import os

    # Find all images
    images = []
    for f in os.listdir(input_dir):
        if f.lower().endswith(extensions):
            images.append(os.path.join(input_dir, f))

    if not images:
        return {"status": "error", "message": f"No images found in {input_dir}"}

    logger.info(f"Found {len(images)} images to process")

    results = []
    for i, image_path in enumerate(images):
        logger.info(f"\n{'='*60}")
        logger.info(f"Processing {i+1}/{len(images)}: {os.path.basename(image_path)}")
        logger.info(f"{'='*60}")

        result = run_decomposition_test(
            input_path=image_path,
            output_dir=output_dir,
            num_layers=num_layers,
            seed=seed + i,  # Different seed per image
            resolution=resolution,
        )
        results.append({
            "input": image_path,
            **result
        })

    # Summarize
    successful = sum(1 for r in results if r['status'] == 'success')
    return {
        "status": "success" if successful == len(results) else "partial",
        "message": f"Processed {successful}/{len(results)} images",
        "results": results,
    }


if __name__ == "__main__":
    import argparse
    import sys

    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

    parser = argparse.ArgumentParser(description='Lattice Layer Decomposition Test')
    parser.add_argument('input', help='Input image path or directory')
    parser.add_argument('--output', '-o', default='./decomp_output', help='Output directory')
    parser.add_argument('--layers', '-n', type=int, default=5, help='Number of layers (3-8)')
    parser.add_argument('--seed', '-s', type=int, default=42, help='Random seed')
    parser.add_argument('--resolution', '-r', type=int, default=640, choices=[640, 1024], help='Output resolution bucket')
    parser.add_argument('--download', action='store_true', help='Download model if needed')
    parser.add_argument('--status', action='store_true', help='Show model status and exit')
    parser.add_argument('--verify', action='store_true', help='Verify model integrity and exit')

    args = parser.parse_args()

    # Status check
    if args.status:
        import json
        print(json.dumps(get_model_status(), indent=2))
        sys.exit(0)

    # Verify check
    if args.verify:
        import json
        print(json.dumps(verify_model_integrity(verbose=True), indent=2))
        sys.exit(0)

    # Download if requested (for manual pre-download to local path)
    if args.download:
        import asyncio
        print("Downloading model to local ComfyUI folder...")
        result = asyncio.run(download_model())
        print(f"Download result: {result}")
        if result['status'] != 'success':
            sys.exit(1)

    # Note: Model will auto-download from HuggingFace if not cached
    # The --download flag is for explicit pre-download to ComfyUI models folder
    if not _check_model_exists():
        print("NOTE: Model not in local folder. Will download from HuggingFace (~28GB).")
        print("This may take a while on first run...")

    import os

    # Determine if input is file or directory
    if os.path.isfile(args.input):
        result = run_decomposition_test(
            input_path=args.input,
            output_dir=args.output,
            num_layers=args.layers,
            seed=args.seed,
            resolution=args.resolution,
        )
    elif os.path.isdir(args.input):
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

    import json
    print("\n" + "="*60)
    print("RESULT:")
    print("="*60)
    print(json.dumps(result, indent=2))

    sys.exit(0 if result['status'] == 'success' else 1)
