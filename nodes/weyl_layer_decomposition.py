"""
Weyl Layer Decomposition - AI-powered image layer separation

This module provides integration with the Qwen-Image-Layered model for
decomposing single images into multiple semantically-meaningful RGBA layers.

Model: Qwen/Qwen-Image-Layered (28.8GB)
Source: https://modelscope.cn/models/Qwen/Qwen-Image-Layered

The model automatically downloads on first use to ComfyUI's models folder.
"""

import os
import json
import logging
from typing import Optional
from pathlib import Path

logger = logging.getLogger("weyl.layer_decomposition")

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


def get_model_status() -> dict:
    """Get current model status for frontend"""
    return {
        "downloaded": _check_model_exists(),
        "loaded": _model_state['loaded'],
        "loading": _model_state['loading'],
        "error": _model_state['error'],
        "model_path": str(_get_model_path()),
        "model_size_gb": 28.8,
    }


async def download_model(progress_callback=None) -> dict:
    """
    Download the Qwen-Image-Layered model from HuggingFace.

    Args:
        progress_callback: Optional async callback for progress updates

    Returns:
        dict with status and message
    """
    if _model_state['loading']:
        return {"status": "error", "message": "Model is already being downloaded"}

    if _check_model_exists():
        return {"status": "success", "message": "Model already downloaded"}

    _model_state['loading'] = True
    _model_state['error'] = None

    try:
        from huggingface_hub import snapshot_download

        model_path = _get_model_path()
        logger.info(f"Downloading Qwen-Image-Layered to {model_path}")

        if progress_callback:
            await progress_callback({"stage": "downloading", "progress": 0})

        # Download from HuggingFace
        snapshot_download(
            repo_id="Qwen/Qwen-Image-Layered",
            local_dir=str(model_path),
            local_dir_use_symlinks=False,
            resume_download=True,
        )

        if progress_callback:
            await progress_callback({"stage": "complete", "progress": 100})

        logger.info("Model download complete")
        return {"status": "success", "message": "Model downloaded successfully"}

    except Exception as e:
        error_msg = f"Failed to download model: {str(e)}"
        logger.error(error_msg)
        _model_state['error'] = error_msg
        return {"status": "error", "message": error_msg}
    finally:
        _model_state['loading'] = False


def load_model() -> dict:
    """
    Load the model into memory for inference.

    Returns:
        dict with status and message
    """
    if _model_state['loaded']:
        return {"status": "success", "message": "Model already loaded"}

    if _model_state['loading']:
        return {"status": "error", "message": "Model is currently loading"}

    if not _check_model_exists():
        return {"status": "error", "message": "Model not downloaded. Call download first."}

    _model_state['loading'] = True
    _model_state['error'] = None

    try:
        import torch
        from diffusers import DiffusionPipeline

        # Determine device
        if torch.cuda.is_available():
            device = "cuda"
            dtype = torch.float16
        elif hasattr(torch.backends, 'mps') and torch.backends.mps.is_available():
            device = "mps"
            dtype = torch.float16
        else:
            device = "cpu"
            dtype = torch.float32

        logger.info(f"Loading model on {device}")

        model_path = _get_model_path()
        pipe = DiffusionPipeline.from_pretrained(
            str(model_path),
            torch_dtype=dtype,
            trust_remote_code=True,
        )
        pipe = pipe.to(device)

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
    num_layers: int = 4,
    guidance_scale: float = 3.0,
    num_inference_steps: int = 50,
    seed: Optional[int] = None,
) -> dict:
    """
    Decompose an image into multiple RGBA layers.

    Args:
        image: PIL Image or numpy array
        num_layers: Number of layers to generate (3-16)
        guidance_scale: CFG scale (default 3.0)
        num_inference_steps: Denoising steps (default 50)
        seed: Random seed for reproducibility

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

        # Convert input to PIL Image if needed
        if isinstance(image, np.ndarray):
            if image.max() <= 1.0:
                image = (image * 255).astype(np.uint8)
            image = Image.fromarray(image)

        # Set seed for reproducibility
        generator = None
        if seed is not None:
            generator = torch.Generator(device=_model_state['device']).manual_seed(seed)

        # Run decomposition
        logger.info(f"Decomposing image into {num_layers} layers")
        result = pipe(
            image=image,
            num_layers=num_layers,
            guidance_scale=guidance_scale,
            num_inference_steps=num_inference_steps,
            generator=generator,
        )

        # Extract layers from result
        layers = result.images if hasattr(result, 'images') else result

        # Convert to list of dicts with metadata
        layer_data = []
        for i, layer in enumerate(layers):
            # Ensure RGBA
            if layer.mode != 'RGBA':
                layer = layer.convert('RGBA')

            # Generate semantic label (placeholder - model may provide this)
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

    @routes.get('/weyl/decomposition/status')
    async def decomposition_status(request):
        """Get model status for frontend"""
        return web.json_response({
            "status": "success",
            "data": get_model_status()
        })

    @routes.post('/weyl/decomposition/download')
    async def decomposition_download(request):
        """Download the model (long-running operation)"""
        result = await download_model()
        return web.json_response(result)

    @routes.post('/weyl/decomposition/load')
    async def decomposition_load(request):
        """Load model into memory"""
        result = load_model()
        return web.json_response(result)

    @routes.post('/weyl/decomposition/unload')
    async def decomposition_unload(request):
        """Unload model from memory"""
        result = unload_model()
        return web.json_response(result)

    @routes.post('/weyl/decomposition/decompose')
    async def decomposition_decompose(request):
        """
        Decompose an image into layers.

        Request body:
        {
            "image": "base64 encoded image",
            "num_layers": 4,
            "guidance_scale": 3.0,
            "num_inference_steps": 50,
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

            # Get parameters
            num_layers = data.get('num_layers', 4)
            guidance_scale = data.get('guidance_scale', 3.0)
            num_inference_steps = data.get('num_inference_steps', 50)
            seed = data.get('seed')

            # Run decomposition
            result = decompose_image(
                image,
                num_layers=num_layers,
                guidance_scale=guidance_scale,
                num_inference_steps=num_inference_steps,
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

    logger.info("Weyl Layer Decomposition routes registered")

except ImportError:
    # Not running in ComfyUI context
    pass
