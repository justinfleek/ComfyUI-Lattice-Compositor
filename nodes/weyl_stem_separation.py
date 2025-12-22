"""
Audio Stem Separation using Demucs - Weyl Compositor Backend

This module provides audio stem separation using Facebook Research's Demucs model
for separating music into individual stems (vocals, drums, bass, other).

==============================================================================
                         OPEN SOURCE ATTRIBUTION
==============================================================================

This implementation is inspired by:

1. ComfyUI_Fill-Nodes - Audio Processing Suite
   Repository: https://github.com/filliptm/ComfyUI_Fill-Nodes
   Author: filliptm
   License: MIT
   Contains: FL_AudioStemSplitter, audio reactive effects, and more

2. Demucs - Music Source Separation
   Repository: https://github.com/facebookresearch/demucs
   Authors: Facebook Research (Alexandre Défossez et al.)
   Paper: "Hybrid Transformers for Music Source Separation" (ICASSP 2023)
   License: MIT

3. torchaudio - PyTorch Audio Processing
   Repository: https://github.com/pytorch/audio
   Authors: PyTorch Team
   License: BSD-2-Clause

==============================================================================
                         HOW IT WORKS
==============================================================================

Demucs uses a hybrid architecture combining:
- Convolutional encoder/decoder for local patterns
- Transformer layers for global context
- Multi-head attention for long-range dependencies

The model separates audio into 4 stems:
- vocals: Lead and background vocals
- drums: Percussion and drum kit
- bass: Bass guitar and low-frequency instruments
- other: Everything else (guitars, synths, keys, etc.)

Processing is done in chunks with overlap to handle long audio files
efficiently and avoid memory issues.

==============================================================================
"""

import os
import io
import json
import logging
import base64
import uuid
import tempfile
import numpy as np
from typing import Optional, Dict, Any, List, Tuple
from pathlib import Path

logger = logging.getLogger("weyl.stem_separation")

# Demucs model configuration
DEMUCS_MODELS = {
    "htdemucs": {
        "name": "HT-Demucs",
        "description": "Hybrid Transformer Demucs - Best quality, slower",
        "stems": ["drums", "bass", "other", "vocals"],
        "sample_rate": 44100,
        "recommended": True
    },
    "htdemucs_ft": {
        "name": "HT-Demucs Fine-tuned",
        "description": "Fine-tuned on MusDB-HQ - Highest quality",
        "stems": ["drums", "bass", "other", "vocals"],
        "sample_rate": 44100,
        "recommended": False
    },
    "htdemucs_6s": {
        "name": "HT-Demucs 6 Stems",
        "description": "6 stem separation (includes piano, guitar)",
        "stems": ["drums", "bass", "other", "vocals", "guitar", "piano"],
        "sample_rate": 44100,
        "recommended": False
    },
    "mdx_extra": {
        "name": "MDX Extra",
        "description": "Fast and accurate - Good balance",
        "stems": ["drums", "bass", "other", "vocals"],
        "sample_rate": 44100,
        "recommended": False
    }
}

# Attribution info
SOURCE_ATTRIBUTION = {
    "fill_nodes": {
        "name": "ComfyUI_Fill-Nodes",
        "repo": "https://github.com/filliptm/ComfyUI_Fill-Nodes",
        "author": "filliptm",
        "license": "MIT",
        "note": "Concept and workflow inspiration"
    },
    "demucs": {
        "name": "Demucs",
        "repo": "https://github.com/facebookresearch/demucs",
        "author": "Facebook Research",
        "license": "MIT",
        "note": "Core separation model"
    }
}


class StemSeparator:
    """
    Audio stem separator using Demucs.

    Provides chunked processing for memory efficiency and
    progress tracking for long audio files.
    """

    def __init__(
        self,
        model_name: str = "htdemucs",
        device: str = "auto",
        segment_length: float = 10.0,
        overlap: float = 0.1
    ):
        """
        Initialize stem separator.

        Args:
            model_name: Demucs model variant to use
            device: 'cuda', 'cpu', or 'auto'
            segment_length: Length of audio chunks in seconds
            overlap: Overlap ratio between chunks (0-0.5)
        """
        self.model_name = model_name
        self.segment_length = segment_length
        self.overlap = min(max(overlap, 0), 0.5)
        self._model = None
        self._sample_rate = DEMUCS_MODELS.get(model_name, {}).get("sample_rate", 44100)

        # Determine device
        if device == "auto":
            import torch
            self.device = "cuda" if torch.cuda.is_available() else "cpu"
        else:
            self.device = device

    def _ensure_model_loaded(self) -> None:
        """Lazy load the model on first use."""
        if self._model is not None:
            return

        try:
            import torch
            import torchaudio

            logger.info(f"Loading Demucs model: {self.model_name}")

            # Use torchaudio's built-in Demucs models when available
            if hasattr(torchaudio.pipelines, 'HDEMUCS_HIGH_MUSDB_PLUS'):
                bundle = torchaudio.pipelines.HDEMUCS_HIGH_MUSDB_PLUS
                self._model = bundle.get_model().to(self.device)
                self._sample_rate = bundle.sample_rate
                logger.info(f"Loaded HDEMUCS_HIGH_MUSDB_PLUS at {self._sample_rate}Hz")
            else:
                # Fallback: try loading from demucs package directly
                try:
                    from demucs.pretrained import get_model
                    self._model = get_model(self.model_name).to(self.device)
                    logger.info(f"Loaded {self.model_name} from demucs package")
                except ImportError:
                    raise ImportError(
                        "Demucs not found. Install via: pip install demucs torchaudio"
                    )

            self._model.eval()

        except Exception as e:
            logger.error(f"Failed to load Demucs model: {e}")
            raise

    def _load_audio(self, audio_data: bytes) -> Tuple["torch.Tensor", int]:
        """
        Load audio from bytes.

        Returns:
            Tuple of (waveform tensor, sample rate)
        """
        import torch
        import torchaudio

        # Write to temp file for torchaudio to read
        with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as f:
            f.write(audio_data)
            temp_path = f.name

        try:
            waveform, sr = torchaudio.load(temp_path)

            # Resample if needed
            if sr != self._sample_rate:
                logger.info(f"Resampling from {sr}Hz to {self._sample_rate}Hz")
                resampler = torchaudio.transforms.Resample(sr, self._sample_rate)
                waveform = resampler(waveform)
                sr = self._sample_rate

            # Convert mono to stereo if needed
            if waveform.shape[0] == 1:
                waveform = waveform.repeat(2, 1)
            elif waveform.shape[0] > 2:
                waveform = waveform[:2]  # Take first 2 channels

            return waveform, sr

        finally:
            os.unlink(temp_path)

    def _apply_model(
        self,
        waveform: "torch.Tensor",
        progress_callback: Optional[callable] = None
    ) -> Dict[str, "torch.Tensor"]:
        """
        Apply Demucs model to separate stems with chunked processing.

        Args:
            waveform: Input audio tensor [channels, samples]
            progress_callback: Optional callback(progress, message)

        Returns:
            Dict mapping stem names to audio tensors
        """
        import torch

        self._ensure_model_loaded()

        # Calculate chunk parameters
        chunk_samples = int(self.segment_length * self._sample_rate)
        overlap_samples = int(chunk_samples * self.overlap)
        hop_samples = chunk_samples - overlap_samples

        total_samples = waveform.shape[1]
        num_chunks = max(1, (total_samples - overlap_samples) // hop_samples)

        # Initialize output accumulators
        stem_names = DEMUCS_MODELS.get(self.model_name, {}).get(
            "stems", ["drums", "bass", "other", "vocals"]
        )
        stems = {name: torch.zeros_like(waveform) for name in stem_names}
        weights = torch.zeros(1, total_samples, device=waveform.device)

        logger.info(f"Processing {total_samples/self._sample_rate:.1f}s audio in {num_chunks} chunks")

        with torch.no_grad():
            for i in range(num_chunks):
                start = i * hop_samples
                end = min(start + chunk_samples, total_samples)

                if progress_callback:
                    progress = (i + 1) / num_chunks
                    progress_callback(progress, f"Processing chunk {i+1}/{num_chunks}")

                # Extract chunk
                chunk = waveform[:, start:end]

                # Pad if necessary
                if chunk.shape[1] < chunk_samples:
                    pad_size = chunk_samples - chunk.shape[1]
                    chunk = torch.nn.functional.pad(chunk, (0, pad_size))

                # Add batch dimension and move to device
                chunk_batch = chunk.unsqueeze(0).to(self.device)

                # Run model
                try:
                    if hasattr(self._model, 'sources'):
                        # Demucs package model
                        separated = self._model(chunk_batch)
                        stem_order = self._model.sources
                    else:
                        # torchaudio pipeline model
                        separated = self._model(chunk_batch)
                        stem_order = stem_names

                    # separated shape: [batch, stems, channels, samples]
                    separated = separated.squeeze(0).cpu()

                except Exception as e:
                    logger.warning(f"Chunk {i} failed: {e}, using original audio")
                    for stem_name in stem_names:
                        stems[stem_name][:, start:end] += chunk[:, :end-start].cpu()
                    weights[:, start:end] += 1
                    continue

                # Create crossfade window for smooth overlap
                actual_samples = min(end - start, separated.shape[-1])
                window = self._create_window(actual_samples, overlap_samples)

                # Accumulate results with windowing
                for idx, stem_name in enumerate(stem_order):
                    if idx < separated.shape[0] and stem_name in stems:
                        stem_chunk = separated[idx, :, :actual_samples]
                        stems[stem_name][:, start:start+actual_samples] += stem_chunk * window

                weights[:, start:start+actual_samples] += window

        # Normalize by weights (handle divide by zero)
        weights = weights.clamp(min=1e-8)
        for stem_name in stems:
            stems[stem_name] = stems[stem_name] / weights

        return stems

    def _create_window(self, length: int, overlap: int) -> "torch.Tensor":
        """Create a smooth crossfade window for overlapping chunks."""
        import torch

        window = torch.ones(length)

        if overlap > 0 and length > overlap * 2:
            # Fade in
            fade_in = torch.linspace(0, 1, overlap)
            window[:overlap] = fade_in

            # Fade out
            fade_out = torch.linspace(1, 0, overlap)
            window[-overlap:] = fade_out

        return window

    def _save_audio(self, waveform: "torch.Tensor", sample_rate: int) -> bytes:
        """Save audio tensor to WAV bytes."""
        import torch
        import torchaudio

        with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as f:
            temp_path = f.name

        try:
            # Ensure proper range [-1, 1]
            waveform = torch.clamp(waveform, -1, 1)

            torchaudio.save(temp_path, waveform, sample_rate)

            with open(temp_path, "rb") as f:
                return f.read()
        finally:
            os.unlink(temp_path)

    def separate(
        self,
        audio_data: bytes,
        stems_to_return: Optional[List[str]] = None,
        progress_callback: Optional[callable] = None
    ) -> Dict[str, Any]:
        """
        Separate audio into stems.

        Args:
            audio_data: Input audio as WAV/MP3 bytes
            stems_to_return: List of stem names to return, or None for all
            progress_callback: Optional callback(progress, message)

        Returns:
            Dict with status, stems as base64 WAV, and metadata
        """
        try:
            import torch

            # Load audio
            if progress_callback:
                progress_callback(0.05, "Loading audio...")

            waveform, sr = self._load_audio(audio_data)

            logger.info(f"Loaded audio: {waveform.shape}, {sr}Hz")

            # Run separation
            if progress_callback:
                progress_callback(0.1, "Starting separation...")

            def adjusted_progress(p, msg):
                if progress_callback:
                    # Scale progress from 0.1 to 0.9
                    progress_callback(0.1 + p * 0.8, msg)

            stems = self._apply_model(waveform, adjusted_progress)

            # Prepare output
            if progress_callback:
                progress_callback(0.9, "Encoding output...")

            available_stems = list(stems.keys())
            if stems_to_return is None:
                stems_to_return = available_stems
            else:
                stems_to_return = [s for s in stems_to_return if s in available_stems]

            result_stems = {}
            for stem_name in stems_to_return:
                stem_audio = self._save_audio(stems[stem_name], sr)
                result_stems[stem_name] = base64.b64encode(stem_audio).decode('utf-8')

            if progress_callback:
                progress_callback(1.0, "Complete!")

            return {
                "status": "success",
                "stems": result_stems,
                "available_stems": available_stems,
                "sample_rate": sr,
                "duration": waveform.shape[1] / sr,
                "model": self.model_name,
                "attribution": SOURCE_ATTRIBUTION
            }

        except ImportError as e:
            logger.error(f"Missing dependency: {e}")
            return {
                "status": "error",
                "message": f"Missing dependency: {str(e)}. Install via: pip install torch torchaudio demucs"
            }
        except Exception as e:
            logger.error(f"Stem separation failed: {e}")
            return {
                "status": "error",
                "message": str(e)
            }


# Global separator instance (lazy loaded)
_separator: Optional[StemSeparator] = None


def get_separator(model_name: str = "htdemucs") -> StemSeparator:
    """Get or create a stem separator instance."""
    global _separator

    if _separator is None or _separator.model_name != model_name:
        _separator = StemSeparator(model_name=model_name)

    return _separator


def get_available_models() -> List[Dict[str, Any]]:
    """Get list of available Demucs models."""
    return [
        {
            "id": model_id,
            "name": info["name"],
            "description": info["description"],
            "stems": info["stems"],
            "sample_rate": info["sample_rate"],
            "recommended": info.get("recommended", False)
        }
        for model_id, info in DEMUCS_MODELS.items()
    ]


def get_attribution() -> Dict[str, Any]:
    """Get attribution information."""
    return {
        "message": "Audio stem separation powered by:",
        "sources": [
            {
                "name": v["name"],
                "repo": v["repo"],
                "author": v["author"],
                "license": v["license"],
                "note": v.get("note", "")
            }
            for v in SOURCE_ATTRIBUTION.values()
        ]
    }


# ============================================================================
# ComfyUI Route Registration
# ============================================================================

try:
    from server import PromptServer
    from aiohttp import web
    import asyncio

    routes = PromptServer.instance.routes

    @routes.get('/weyl/audio/stems/models')
    async def list_stem_models(request):
        """Get list of available stem separation models."""
        return web.json_response({
            "status": "success",
            "models": get_available_models(),
            "attribution": get_attribution()
        })

    @routes.get('/weyl/audio/stems/attribution')
    async def get_attribution_route(request):
        """Get attribution information."""
        return web.json_response({
            "status": "success",
            **get_attribution()
        })

    @routes.post('/weyl/audio/stems/separate')
    async def separate_stems_route(request):
        """
        Separate audio into stems.

        Request body:
        {
            "audio": "base64 encoded audio (WAV/MP3)",
            "model": "htdemucs" (optional),
            "stems": ["vocals", "drums", "bass", "other"] (optional, returns all if omitted)
        }

        Response:
        {
            "status": "success",
            "stems": {
                "vocals": "base64 WAV",
                "drums": "base64 WAV",
                ...
            },
            "sample_rate": 44100,
            "duration": 120.5
        }
        """
        try:
            data = await request.json()

            audio_b64 = data.get('audio')
            if not audio_b64:
                return web.json_response({
                    "status": "error",
                    "message": "Missing 'audio' field"
                }, status=400)

            # Strip data URL prefix if present
            if ',' in audio_b64:
                audio_b64 = audio_b64.split(',')[1]

            audio_bytes = base64.b64decode(audio_b64)

            model_name = data.get('model', 'htdemucs')
            stems_to_return = data.get('stems')  # None means all

            # Run separation in thread pool to avoid blocking
            loop = asyncio.get_event_loop()

            separator = get_separator(model_name)
            result = await loop.run_in_executor(
                None,
                lambda: separator.separate(audio_bytes, stems_to_return)
            )

            if result["status"] == "error":
                return web.json_response(result, status=500)

            return web.json_response(result)

        except json.JSONDecodeError:
            return web.json_response({
                "status": "error",
                "message": "Invalid JSON in request body"
            }, status=400)
        except Exception as e:
            logger.error(f"Stem separation endpoint error: {e}")
            return web.json_response({
                "status": "error",
                "message": f"Internal error: {str(e)}"
            }, status=500)

    @routes.post('/weyl/audio/stems/isolate')
    async def isolate_stem_route(request):
        """
        Isolate a single stem (remove everything else).

        Request body:
        {
            "audio": "base64 encoded audio",
            "stem": "vocals" (or "drums", "bass", "other"),
            "model": "htdemucs" (optional)
        }

        Response:
        {
            "status": "success",
            "isolated": "base64 WAV of isolated stem",
            "removed": "base64 WAV of everything else",
            ...
        }
        """
        try:
            data = await request.json()

            audio_b64 = data.get('audio')
            stem_name = data.get('stem')

            if not audio_b64:
                return web.json_response({
                    "status": "error",
                    "message": "Missing 'audio' field"
                }, status=400)

            if not stem_name:
                return web.json_response({
                    "status": "error",
                    "message": "Missing 'stem' field"
                }, status=400)

            if ',' in audio_b64:
                audio_b64 = audio_b64.split(',')[1]

            audio_bytes = base64.b64decode(audio_b64)
            model_name = data.get('model', 'htdemucs')

            # Run separation
            loop = asyncio.get_event_loop()
            separator = get_separator(model_name)

            result = await loop.run_in_executor(
                None,
                lambda: separator.separate(audio_bytes, None)  # Get all stems
            )

            if result["status"] == "error":
                return web.json_response(result, status=500)

            stems = result.get("stems", {})

            if stem_name not in stems:
                return web.json_response({
                    "status": "error",
                    "message": f"Stem '{stem_name}' not available. Available: {list(stems.keys())}"
                }, status=400)

            # Create "removed" by combining all other stems
            import torch
            import torchaudio

            isolated_b64 = stems[stem_name]

            # For "removed", we need to mix all other stems
            other_stems = [s for s in stems.keys() if s != stem_name]

            if other_stems:
                # Decode and mix other stems
                all_other = []
                for other_name in other_stems:
                    other_bytes = base64.b64decode(stems[other_name])
                    with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as f:
                        f.write(other_bytes)
                        temp_path = f.name
                    try:
                        waveform, sr = torchaudio.load(temp_path)
                        all_other.append(waveform)
                    finally:
                        os.unlink(temp_path)

                # Sum all other stems
                mixed = sum(all_other)

                # Normalize to prevent clipping
                max_val = mixed.abs().max()
                if max_val > 1:
                    mixed = mixed / max_val

                # Encode mixed result
                with tempfile.NamedTemporaryFile(suffix=".wav", delete=False) as f:
                    temp_path = f.name
                try:
                    torchaudio.save(temp_path, mixed, result["sample_rate"])
                    with open(temp_path, "rb") as f:
                        removed_bytes = f.read()
                    removed_b64 = base64.b64encode(removed_bytes).decode('utf-8')
                finally:
                    os.unlink(temp_path)
            else:
                removed_b64 = None

            return web.json_response({
                "status": "success",
                "isolated": isolated_b64,
                "removed": removed_b64,
                "stem": stem_name,
                "sample_rate": result["sample_rate"],
                "duration": result["duration"],
                "model": model_name,
                "attribution": SOURCE_ATTRIBUTION
            })

        except json.JSONDecodeError:
            return web.json_response({
                "status": "error",
                "message": "Invalid JSON in request body"
            }, status=400)
        except Exception as e:
            logger.error(f"Stem isolation endpoint error: {e}")
            return web.json_response({
                "status": "error",
                "message": f"Internal error: {str(e)}"
            }, status=500)

    logger.info("Weyl Audio Stem Separation routes registered")
    logger.info("Sources: filliptm/ComfyUI_Fill-Nodes (concept), Facebook Research/Demucs (model)")

except ImportError:
    logger.warning("Not running in ComfyUI - stem separation routes not registered")


# ============================================================================
# Standalone Testing
# ============================================================================

if __name__ == "__main__":
    import argparse

    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

    parser = argparse.ArgumentParser(description='Audio Stem Separation')
    parser.add_argument('--models', action='store_true', help='List available models')
    parser.add_argument('--attribution', action='store_true', help='Show attribution')
    parser.add_argument('--separate', type=str, help='Separate stems from audio file')
    parser.add_argument('--output', type=str, default='./stems', help='Output directory')
    parser.add_argument('--model', type=str, default='htdemucs', help='Model to use')

    args = parser.parse_args()

    if args.models:
        print(json.dumps(get_available_models(), indent=2))
    elif args.attribution:
        print(json.dumps(get_attribution(), indent=2))
    elif args.separate:
        # Separate an audio file
        input_path = Path(args.separate)
        output_dir = Path(args.output)
        output_dir.mkdir(exist_ok=True)

        print(f"Separating: {input_path}")
        print(f"Output to: {output_dir}")
        print(f"Model: {args.model}")

        with open(input_path, "rb") as f:
            audio_bytes = f.read()

        separator = StemSeparator(model_name=args.model)

        def progress_callback(p, msg):
            print(f"[{p*100:.0f}%] {msg}")

        result = separator.separate(audio_bytes, progress_callback=progress_callback)

        if result["status"] == "success":
            for stem_name, stem_b64 in result["stems"].items():
                stem_bytes = base64.b64decode(stem_b64)
                output_path = output_dir / f"{input_path.stem}_{stem_name}.wav"
                with open(output_path, "wb") as f:
                    f.write(stem_bytes)
                print(f"  Saved: {output_path}")

            print(f"\nDuration: {result['duration']:.1f}s")
            print(f"Sample rate: {result['sample_rate']}Hz")
        else:
            print(f"Error: {result['message']}")
    else:
        print("Audio Stem Separation - Weyl Compositor")
        print("=" * 50)
        print("\nAvailable models:")
        for model in get_available_models():
            rec = " (recommended)" if model["recommended"] else ""
            print(f"  {model['id']}: {model['name']}{rec}")
            print(f"    Stems: {', '.join(model['stems'])}")
        print("\nAttribution:")
        for source in SOURCE_ATTRIBUTION.values():
            print(f"  {source['name']} by {source['author']}")
            print(f"    {source['repo']}")
