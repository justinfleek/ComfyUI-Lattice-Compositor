"""
ComfyUI Workflow Executor for Visual Generation.

Executes video/image generation workflows via ComfyUI's HTTP API.
Based on the preprocessor execution pattern but adapted for generation.
"""

import base64
import hashlib
import json
import logging
import uuid
from typing import Callable

logger = logging.getLogger("lattice.workflow_executor")


# ============================================================================
# Workflow Templates
# ============================================================================


def create_i2v_workflow(
    image_name: str,
    prompt: str,
    width: int = 1280,
    height: int = 720,
    num_frames: int = 81,
    steps: int = 20,
    cfg: float = 7.5,
    seed: int = -1,
) -> dict:
    """
    Create Wan 2.2 Image-to-Video workflow.

    Node structure:
    1. LoadImage -> 2. WanI2V -> 3. VAEDecode -> 4. SaveAnimatedWEBP
    """
    actual_seed = seed if seed >= 0 else hash(f"{image_name}{prompt}") % (2**31)

    workflow = {
        "1": {
            "class_type": "LoadImage",
            "inputs": {"image": image_name},
        },
        "2": {
            "class_type": "WanImageToVideo",
            "inputs": {
                "image": ["1", 0],
                "prompt": prompt,
                "negative_prompt": "blurry, low quality, distorted",
                "width": width,
                "height": height,
                "num_frames": num_frames,
                "steps": steps,
                "cfg": cfg,
                "seed": actual_seed,
            },
        },
        "3": {
            "class_type": "VAEDecode",
            "inputs": {
                "samples": ["2", 0],
                "vae": ["2", 1],
            },
        },
        "4": {
            "class_type": "SaveAnimatedWEBP",
            "inputs": {
                "images": ["3", 0],
                "filename_prefix": "lattice_i2v",
                "fps": 24,
                "lossless": False,
                "quality": 85,
            },
        },
    }

    return workflow


def create_t2v_workflow(
    prompt: str,
    width: int = 1280,
    height: int = 720,
    num_frames: int = 81,
    steps: int = 20,
    cfg: float = 7.5,
    seed: int = -1,
) -> dict:
    """
    Create Wan 2.2 Text-to-Video workflow.

    Node structure:
    1. WanT2V -> 2. VAEDecode -> 3. SaveAnimatedWEBP
    """
    actual_seed = seed if seed >= 0 else hash(prompt) % (2**31)

    workflow = {
        "1": {
            "class_type": "WanTextToVideo",
            "inputs": {
                "prompt": prompt,
                "negative_prompt": "blurry, low quality, distorted",
                "width": width,
                "height": height,
                "num_frames": num_frames,
                "steps": steps,
                "cfg": cfg,
                "seed": actual_seed,
            },
        },
        "2": {
            "class_type": "VAEDecode",
            "inputs": {
                "samples": ["1", 0],
                "vae": ["1", 1],
            },
        },
        "3": {
            "class_type": "SaveAnimatedWEBP",
            "inputs": {
                "images": ["2", 0],
                "filename_prefix": "lattice_t2v",
                "fps": 24,
                "lossless": False,
                "quality": 85,
            },
        },
    }

    return workflow


# ============================================================================
# Execution
# ============================================================================


async def execute_workflow(
    workflow: dict,
    server_address: str = "127.0.0.1:8188",
    on_progress: Callable[[float, str], None] | None = None,
    timeout_seconds: int = 600,
) -> dict:
    """
    Execute a ComfyUI workflow and return results.

    Args:
        workflow: ComfyUI workflow dict
        server_address: ComfyUI server address
        on_progress: Optional callback (progress_pct, message)
        timeout_seconds: Timeout for execution

    Returns:
        {
            "status": "success" | "error",
            "outputs": [{"filename": str, "subfolder": str, "type": str}, ...],
            "error": str (if error),
        }
    """
    import aiohttp
    import asyncio

    # Generate deterministic client_id
    workflow_hash = hashlib.sha256(json.dumps(workflow, sort_keys=True).encode()).hexdigest()[:16]
    namespace = uuid.UUID("6ba7b810-9dad-11d1-80b4-00c04fd430c8")
    client_id = str(uuid.uuid5(namespace, f"lattice:{workflow_hash}"))

    try:
        timeout = aiohttp.ClientTimeout(total=timeout_seconds)
        async with aiohttp.ClientSession(timeout=timeout) as session:
            # Step 1: Queue workflow
            prompt_url = f"http://{server_address}/prompt"
            payload = {"prompt": workflow, "client_id": client_id}

            async with session.post(prompt_url, json=payload) as resp:
                if resp.status != 200:
                    error_text = await resp.text()
                    return {"status": "error", "error": f"Queue failed: {error_text}"}
                queue_result = await resp.json()
                prompt_id = queue_result.get("prompt_id")

            logger.info(f"Queued workflow: {prompt_id}")
            if on_progress:
                on_progress(0.0, "Queued")

            # Step 2: Wait for completion via WebSocket
            ws_url = f"ws://{server_address}/ws?clientId={client_id}"
            total_steps = 0
            current_step = 0

            async with session.ws_connect(ws_url) as ws:
                async for msg in ws:
                    if msg.type == aiohttp.WSMsgType.TEXT:
                        data = json.loads(msg.data)
                        msg_type = data.get("type")
                        msg_data = data.get("data", {})

                        if msg_type == "progress":
                            current_step = msg_data.get("value", 0)
                            total_steps = msg_data.get("max", 1)
                            pct = current_step / total_steps if total_steps > 0 else 0
                            if on_progress:
                                on_progress(pct, f"Step {current_step}/{total_steps}")

                        elif msg_type == "executing":
                            if msg_data.get("prompt_id") == prompt_id:
                                if msg_data.get("node") is None:
                                    logger.info("Execution complete")
                                    break

                        elif msg_type == "execution_error":
                            error_msg = msg_data.get("exception_message", "Unknown error")
                            return {"status": "error", "error": error_msg}

            if on_progress:
                on_progress(1.0, "Complete")

            # Step 3: Get outputs from history
            history_url = f"http://{server_address}/history/{prompt_id}"

            async with session.get(history_url) as resp:
                if resp.status != 200:
                    return {"status": "error", "error": "Failed to get history"}
                history = await resp.json()

            outputs = []
            prompt_outputs = history.get(prompt_id, {}).get("outputs", {})

            for node_id, node_output in prompt_outputs.items():
                if "images" in node_output:
                    for img in node_output["images"]:
                        outputs.append({
                            "filename": img.get("filename"),
                            "subfolder": img.get("subfolder", ""),
                            "type": img.get("type", "output"),
                        })
                if "gifs" in node_output:
                    for gif in node_output["gifs"]:
                        outputs.append({
                            "filename": gif.get("filename"),
                            "subfolder": gif.get("subfolder", ""),
                            "type": gif.get("type", "output"),
                        })

            return {"status": "success", "outputs": outputs, "prompt_id": prompt_id}

    except asyncio.TimeoutError:
        return {"status": "error", "error": f"Timeout after {timeout_seconds}s"}
    except Exception as e:
        logger.error(f"Workflow execution failed: {e}")
        return {"status": "error", "error": str(e)}


async def download_output(
    filename: str,
    server_address: str = "127.0.0.1:8188",
    subfolder: str = "",
    output_type: str = "output",
) -> bytes | None:
    """
    Download an output file from ComfyUI.

    Returns:
        File bytes or None if failed
    """
    import aiohttp

    try:
        async with aiohttp.ClientSession() as session:
            view_url = f"http://{server_address}/view"
            params = {
                "filename": filename,
                "subfolder": subfolder,
                "type": output_type,
            }

            async with session.get(view_url, params=params) as resp:
                if resp.status != 200:
                    logger.error(f"Failed to download {filename}: {resp.status}")
                    return None
                return await resp.read()

    except Exception as e:
        logger.error(f"Download failed: {e}")
        return None


async def upload_image(
    image_data: bytes,
    server_address: str = "127.0.0.1:8188",
    filename: str = "input.png",
) -> str | None:
    """
    Upload an image to ComfyUI.

    Returns:
        The filename as stored by ComfyUI, or None if failed
    """
    import aiohttp

    try:
        async with aiohttp.ClientSession() as session:
            upload_url = f"http://{server_address}/upload/image"

            form = aiohttp.FormData()
            form.add_field("image", image_data, filename=filename, content_type="image/png")
            form.add_field("overwrite", "true")

            async with session.post(upload_url, data=form) as resp:
                if resp.status != 200:
                    logger.error(f"Upload failed: {resp.status}")
                    return None
                result = await resp.json()
                return result.get("name")

    except Exception as e:
        logger.error(f"Upload failed: {e}")
        return None
