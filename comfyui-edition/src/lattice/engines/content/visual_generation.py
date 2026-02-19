"""
COMPASS Visual Content Generation Engine for Lattice Compositor

Integrates COMPASS-style visual content generation with Lattice's ComfyUI workflows.
Provides unified API for image and video generation.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass
from typing import Dict, Optional, Union

from lattice.engines.content.text_generation import GeneratedContent


class ImageContentType(str, enum.Enum):
    """Types of image content that can be generated."""

    PRODUCT_IMAGE = "product_image"
    LIFESTYLE_IMAGE = "lifestyle_image"
    BACKGROUND = "background"
    BRAND_CONSISTENT = "brand_consistent"
    MOOD_BOARD = "mood_board"
    ICON = "icon"
    ILLUSTRATION = "illustration"
    INFOGRAPHIC_ELEMENT = "infographic_element"
    CHART_GRAPH = "chart_graph"
    QR_CODE = "qr_code"
    BARCODE = "barcode"
    AVATAR = "avatar"
    PROFILE_PICTURE = "profile_picture"
    THUMBNAIL = "thumbnail"
    AD_CREATIVE = "ad_creative"
    BANNER = "banner"
    HERO_IMAGE = "hero_image"
    EMAIL_HEADER = "email_header"
    PRODUCT_MOCKUP = "product_mockup"
    PACKAGING_MOCKUP = "packaging_mockup"
    COLLAGE = "collage"
    MEME = "meme"


class VideoContentType(str, enum.Enum):
    """Types of video content that can be generated."""

    TEXT_TO_VIDEO = "text_to_video"
    PRODUCT_VIDEO = "product_video"
    EXPLAINER_VIDEO = "explainer_video"
    SOCIAL_VIDEO_VERTICAL = "social_video_vertical"
    AD_VIDEO = "ad_video"
    ANIMATED_TEXT = "animated_text"
    KINETIC_TYPOGRAPHY = "kinetic_typography"
    LOGO_ANIMATION = "logo_animation"
    INTRO_OUTRO = "intro_outro"
    LOWER_THIRD = "lower_third"
    AVATAR_VIDEO = "avatar_video"
    PRESENTER_VIDEO = "presenter_video"


@dataclass
class GeneratedImage:
    """Result of image generation."""

    image_path: str
    width: int
    height: int
    format: str  # "png", "jpg", etc.
    metadata: Dict[str, Union[str, int, float, bool]]


@dataclass
class GeneratedVideo:
    """Result of video generation."""

    video_path: str
    width: int
    height: int
    frame_count: int
    fps: float
    duration: float
    format: str  # "mp4", "webm", etc.
    metadata: Dict[str, Union[str, int, float, bool]]


class VisualGenerator:
    """
    Visual content generation engine.

    Integrates with Lattice's ComfyUI workflows to generate images and videos.
    Maps COMPASS event types to appropriate generation workflows.
    """

    def __init__(self):
        """Initialize the visual generator."""
        # Will integrate with ComfyUI workflow system
        pass

    async def generate_image(
        self,
        content_type: ImageContentType,
        prompt: str,
        width: int = 1024,
        height: int = 1024,
        style: Optional[str] = None,
        brand_guidelines: Optional[Dict[str, Union[str, int, float, bool]]] = None,
        **kwargs: Dict[str, Union[str, int, float, bool]],
    ) -> GeneratedImage:
        """
        Generate an image based on content type and prompt.

        Args:
            content_type: Type of image to generate
            prompt: Text description of desired image
            width: Image width in pixels
            height: Image height in pixels
            style: Optional style specification
            brand_guidelines: Optional brand guidelines (colors, fonts, etc.)
            **kwargs: Additional generation parameters

        Returns:
            GeneratedImage with path and metadata
        """
        # Map content type to ComfyUI workflow
        workflow_type = self._map_image_type_to_workflow(content_type)

        # Build generation parameters
        params = {
            "prompt": prompt,
            "width": width,
            "height": height,
            "style": style,
            "brand_guidelines": brand_guidelines,
            **kwargs,
        }

        #                                                                      // todo
        # For now, return placeholder
        return GeneratedImage(
            image_path="",
            width=width,
            height=height,
            format="png",
            metadata={"content_type": content_type.value, "workflow": workflow_type},
        )

    async def generate_video(
        self,
        content_type: VideoContentType,
        prompt: str,
        width: int = 1024,
        height: int = 1024,
        frame_count: int = 81,
        fps: float = 24.0,
        reference_image: Optional[str] = None,
        **kwargs: Dict[str, Union[str, int, float, bool]],
    ) -> GeneratedVideo:
        """
        Generate a video based on content type and prompt.

        Args:
            content_type: Type of video to generate
            prompt: Text description of desired video
            width: Video width in pixels
            height: Video height in pixels
            frame_count: Number of frames
            fps: Frames per second
            reference_image: Optional reference image path for I2V
            **kwargs: Additional generation parameters

        Returns:
            GeneratedVideo with path and metadata
        """
        # Map content type to ComfyUI workflow
        workflow_type = self._map_video_type_to_workflow(content_type)

        # Build generation parameters
        params = {
            "prompt": prompt,
            "width": width,
            "height": height,
            "frameCount": frame_count,
            "fps": fps,
            "referenceImage": reference_image,
            **kwargs,
        }

        #                                                                      // todo
        # For now, return placeholder
        duration = frame_count / fps
        return GeneratedVideo(
            video_path="",
            width=width,
            height=height,
            frame_count=frame_count,
            fps=fps,
            duration=duration,
            format="mp4",
            metadata={"content_type": content_type.value, "workflow": workflow_type},
        )

    def _map_image_type_to_workflow(self, content_type: ImageContentType) -> str:
        """Map COMPASS image content type to Lattice ComfyUI workflow type."""
        # Map to appropriate workflow based on content type
        workflow_map = {
            ImageContentType.PRODUCT_IMAGE: "controlnet-depth",
            ImageContentType.LIFESTYLE_IMAGE: "controlnet-depth",
            ImageContentType.BACKGROUND: "controlnet-depth",
            ImageContentType.BRAND_CONSISTENT: "controlnet-lineart",
            ImageContentType.MOOD_BOARD: "controlnet-canny",
            ImageContentType.ICON: "controlnet-lineart",
            ImageContentType.ILLUSTRATION: "controlnet-lineart",
            ImageContentType.AD_CREATIVE: "controlnet-canny",
            ImageContentType.BANNER: "controlnet-canny",
            ImageContentType.HERO_IMAGE: "controlnet-depth",
            ImageContentType.EMAIL_HEADER: "controlnet-lineart",
            ImageContentType.PRODUCT_MOCKUP: "controlnet-depth",
            ImageContentType.PACKAGING_MOCKUP: "controlnet-depth",
            ImageContentType.COLLAGE: "controlnet-canny",
            ImageContentType.MEME: "controlnet-lineart",
        }
        return workflow_map.get(content_type, "controlnet-depth")

    def _map_video_type_to_workflow(self, content_type: VideoContentType) -> str:
        """Map COMPASS video content type to Lattice ComfyUI workflow type."""
        # Map to appropriate workflow based on content type
        workflow_map = {
            VideoContentType.TEXT_TO_VIDEO: "wan22-t2v",
            VideoContentType.PRODUCT_VIDEO: "wan22-i2v",
            VideoContentType.EXPLAINER_VIDEO: "wan22-i2v",
            VideoContentType.SOCIAL_VIDEO_VERTICAL: "wan22-i2v",
            VideoContentType.AD_VIDEO: "wan22-i2v",
            VideoContentType.ANIMATED_TEXT: "animatediff-cameractrl",
            VideoContentType.KINETIC_TYPOGRAPHY: "animatediff-cameractrl",
            VideoContentType.LOGO_ANIMATION: "animatediff-cameractrl",
            VideoContentType.INTRO_OUTRO: "animatediff-cameractrl",
            VideoContentType.LOWER_THIRD: "animatediff-cameractrl",
            VideoContentType.AVATAR_VIDEO: "wan22-i2v",
            VideoContentType.PRESENTER_VIDEO: "wan22-i2v",
        }
        return workflow_map.get(content_type, "wan22-t2v")
