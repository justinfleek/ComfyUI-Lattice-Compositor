"""
Text Content Generation Engine for Lattice Compositor

Port of COMPASS text generation capabilities:
- Blog post generation
- Social media content (Twitter, LinkedIn, Instagram)
- Ad copy generation (Google, Facebook, LinkedIn)
- Email content (subject lines, body copy, sequences)
- Sales content (proposals, objection handling)

Integration with Lattice AI agent for content generation.
"""

from __future__ import annotations

import json
import logging
import re
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from typing import Callable, Awaitable, Union, Optional

logger = logging.getLogger(__name__)

# Maximum content length for safety
MAX_CONTENT_LENGTH = 100_000


class TextContentType(str, Enum):
    """Text content generation types"""

    BLOG_POST = "blog_post"
    BLOG_OUTLINE = "blog_outline"
    ARTICLE_REWRITE = "article_rewrite"
    PRODUCT_DESCRIPTION = "product_description"
    HEADLINE = "headline"
    SUBHEADLINE = "subheadline"
    SUMMARY = "summary"
    TRANSLATION = "translation"
    PRESS_RELEASE = "press_release"
    CASE_STUDY = "case_study"
    FAQ = "faq"
    CAPTION = "caption"
    DESCRIPTION = "description"
    INTRODUCTION = "introduction"
    CONCLUSION = "conclusion"
    TESTIMONIAL = "testimonial"
    NEWSLETTER = "newsletter"
    SOCIAL_MEDIA_POST = "social_media_post"
    TWEET_THREAD = "tweet_thread"
    LINKEDIN_ARTICLE = "linkedin_article"
    FACEBOOK_POST = "facebook_post"
    INSTAGRAM_CAPTION = "instagram_caption"
    YOUTUBE_DESCRIPTION = "youtube_description"


class EmailContentType(str, Enum):
    """Email content generation types"""

    SUBJECT_LINE = "subject_line"
    PREHEADER = "preheader"
    BODY_COPY = "body_copy"
    CTA = "cta"
    WELCOME_SEQUENCE = "welcome_sequence"
    ABANDONED_CART = "abandoned_cart"
    WIN_BACK = "win_back"
    RE_ENGAGEMENT = "re_engagement"
    NEWSLETTER = "newsletter"
    PROMOTIONAL = "promotional"
    TRANSACTIONAL = "transactional"
    COLD_OUTREACH = "cold_outreach"
    FOLLOW_UP = "follow_up"
    THANK_YOU = "thank_you"


class SocialContentType(str, Enum):
    """Social media content generation types"""

    TWEET = "tweet"
    LINKEDIN_POST = "linkedin_post"
    FACEBOOK_POST = "facebook_post"
    INSTAGRAM_CAPTION = "instagram_caption"
    TIKTOK_CAPTION = "tiktok_caption"
    YOUTUBE_TITLE = "youtube_title"
    YOUTUBE_DESCRIPTION = "youtube_description"
    HASHTAGS = "hashtags"
    SOCIAL_BIO = "social_bio"
    THREAD = "thread"
    POLL_QUESTION = "poll_question"
    COMMENT_RESPONSE = "comment_response"


class AdCopyType(str, Enum):
    """Ad copy generation types"""

    GOOGLE_HEADLINE = "google_headline"
    GOOGLE_DESCRIPTION = "google_description"
    META_PRIMARY = "meta_primary"
    META_HEADLINE = "meta_headline"
    META_DESCRIPTION = "meta_description"
    INSTAGRAM_AD = "instagram_ad"
    LINKEDIN_SPONSORED = "linkedin_sponsored"
    TWITTER_AD = "twitter_ad"
    TIKTOK_SCRIPT = "tiktok_script"
    YOUTUBE_SCRIPT = "youtube_script"


class SalesContentType(str, Enum):
    """Sales content generation types"""

    SALES_EMAIL_SEQUENCE = "sales_email_sequence"
    COLD_PERSONALIZATION = "cold_personalization"
    LINKEDIN_CONNECTION = "linkedin_connection"
    PROPOSAL_SECTION = "proposal_section"
    DECK_TALKING_POINTS = "deck_talking_points"
    OBJECTION_HANDLING = "objection_handling"
    BATTLECARD = "battlecard"
    ROI_CALCULATOR_COPY = "roi_calculator_copy"
    PRICING_PAGE = "pricing_page"
    DEMO_FOLLOWUP = "demo_followup"
    UPSELL_MESSAGE = "upsell_message"
    RENEWAL_REMINDER = "renewal_reminder"


@dataclass
class GeneratedContent:
    """Generated content result"""

    content_type: str
    text: str
    metadata: dict[str, Union[str, int, float, bool]] = field(default_factory=dict)
    word_count: int = 0
    character_count: int = 0
    generated_at: datetime = field(default_factory=lambda: datetime.now(timezone.utc))


@dataclass
class LLMToolResult:
    """Result from an LLM tool call for text generation"""

    success: bool
    data: str = ""
    error: str = ""


# Type alias for LLM tool function signature
LLMToolFn = Callable[[str, int], Awaitable[LLMToolResult]]


class TextGenerator:
    """
    Generate text content using LLM.

    Supports multiple content types: blog posts, social media, ads, emails, sales.
    """

    llm_tool: Optional[LLMToolFn]

    def __init__(self, llm_tool: LLMToolFn | None = None):
        """
        Args:
            llm_tool: Async function to call LLM for generation.
                      Signature: async def llm_tool(prompt: str, max_tokens: int) -> LLMToolResult
        """
        self.llm_tool = llm_tool

    async def generate(
        self,
        content_type: TextContentType | EmailContentType | SocialContentType | AdCopyType | SalesContentType,
        topic: str,
        context: dict[str, Union[str, int, float, bool]] | None = None,
        max_tokens: int = 2000,
    ) -> GeneratedContent:
        """
        Generate text content.

        Args:
            content_type: Type of content to generate
            topic: Topic or prompt for generation
            context: Additional context (brand voice, platform, etc.)
            max_tokens: Maximum tokens to generate

        Returns:
            GeneratedContent with text and metadata
        """
        context = context or {}

        # Build prompt based on content type
        prompt = self._build_prompt(content_type, topic, context)

        # Generate using LLM
        if self.llm_tool:
            try:
                result = await self.llm_tool(prompt, max_tokens)
                text = result.data if result.success else self._generate_fallback(content_type, topic)
            except Exception as e:
                logger.warning(f"LLM generation failed, using fallback: {e}")
                text = self._generate_fallback(content_type, topic)
        else:
            text = self._generate_fallback(content_type, topic)

        # Sanitize and validate
        text = self._sanitize_text(text)

        # Calculate metrics
        word_count = len(text.split())
        character_count = len(text)

        return GeneratedContent(
            content_type=str(content_type.value),
            text=text,
            metadata=context,
            word_count=word_count,
            character_count=character_count,
        )

    def _build_prompt(
        self,
        content_type: TextContentType | EmailContentType | SocialContentType | AdCopyType | SalesContentType,
        topic: str,
        context: dict[str, Union[str, int, float, bool]],
    ) -> str:
        """Build prompt for LLM based on content type"""
        # Sanitize inputs
        safe_topic = self._sanitize_text(topic[:1000])

        # Platform-specific character limits
        char_limits = {
            "tweet": 280,
            "linkedin_post": 3000,
            "facebook_post": 5000,
            "instagram_caption": 2200,
            "youtube_description": 5000,
            "blog_post": 5000,
        }

        platform = context.get("platform", "general")
        char_limit = char_limits.get(platform.lower(), 2000)

        # Brand voice (if provided)
        brand_voice = context.get("brand_voice", {})
        voice_instructions = ""
        if brand_voice:
            voice_instructions = f"""
BRAND VOICE:
- Personality: {', '.join(brand_voice.get('personality', []))}
- Always: {', '.join(brand_voice.get('always', []))}
- Never: {', '.join(brand_voice.get('never', []))}
"""

        # Build type-specific prompt
        prompt = f"""Generate {content_type.value} content.

TOPIC: {safe_topic}
{voice_instructions}
CHARACTER LIMIT: {char_limit}

Generate the content text only. No explanations. Stay in character.
"""

        return prompt

    def _sanitize_text(self, text: str) -> str:
        """Sanitize generated text"""
        if not text:
            return ""

        # Remove potential injection patterns
        text = re.sub(
            r"(ignore\s+(?:previous|above|all)\s+(?:instructions?|prompts?)|system\s*:\s*|\[INST\]|<\|im_start\|>)",
            "[FILTERED]",
            text,
            flags=re.IGNORECASE,
        )

        # Limit length
        if len(text) > MAX_CONTENT_LENGTH:
            text = text[:MAX_CONTENT_LENGTH]

        return text.strip()

    def _generate_fallback(
        self,
        content_type: TextContentType | EmailContentType | SocialContentType | AdCopyType | SalesContentType,
        topic: str,
    ) -> str:
        """Generate fallback text when LLM is unavailable"""
        # Simple template-based generation
        if isinstance(content_type, SocialContentType):
            if content_type == SocialContentType.TWEET:
                return f"{topic}\n\n#motiongraphics #animation"
            elif content_type == SocialContentType.LINKEDIN_POST:
                return f"Excited to share: {topic}\n\nWhat are your thoughts?"
            elif content_type == SocialContentType.INSTAGRAM_CAPTION:
                return f"{topic} ✨\n\n#motiongraphics #animation #design"

        elif isinstance(content_type, TextContentType):
            if content_type == TextContentType.BLOG_POST:
                return f"# {topic}\n\n## Introduction\n\n{topic} is an important topic in motion graphics.\n\n## Main Content\n\n[Content about {topic}]\n\n## Conclusion\n\nIn summary, {topic} offers significant benefits."
            elif content_type == TextContentType.HEADLINE:
                return f"{topic}: The Complete Guide"

        elif isinstance(content_type, EmailContentType):
            if content_type == EmailContentType.SUBJECT_LINE:
                return f"About {topic}"
            elif content_type == EmailContentType.BODY_COPY:
                return f"Hi,\n\nI wanted to share some information about {topic}.\n\nBest regards"

        return f"Content about {topic}"


# Convenience function
async def generate_text_content(
    content_type: str,
    topic: str,
    context: dict[str, Union[str, int, float, bool]] | None = None,
    llm_tool: LLMToolFn | None = None,
) -> GeneratedContent:
    """Quick text content generation"""
    generator = TextGenerator(llm_tool=llm_tool)

    # Map string to enum
    type_map: dict[str, type[Enum]] = {
        "blog_post": TextContentType,
        "tweet": SocialContentType,
        "linkedin_post": SocialContentType,
        "email_subject": EmailContentType,
        "ad_copy": AdCopyType,
        "sales_email": SalesContentType,
    }

    # Find matching enum
    enum_type: Optional[type[Enum]] = None
    for prefix, enum_class in type_map.items():
        if content_type.startswith(prefix):
            enum_type = enum_class
            break

    if enum_type is None:
        enum_type = TextContentType

    try:
        content_enum = enum_type(content_type)
    except ValueError:
        content_enum = TextContentType.BLOG_POST

    return await generator.generate(content_enum, topic, context)
