"""
COMPASS Brand Voice Engine for Lattice Compositor

Manages brand voice configuration, scoring, and enforcement for content generation.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field
from typing import Dict, List, Optional


class BrandVoiceTone(str, enum.Enum):
    """Brand voice tones."""

    FORMAL = "formal"
    CASUAL = "casual"
    PROFESSIONAL = "professional"
    FRIENDLY = "friendly"
    AUTHORITATIVE = "authoritative"
    PLAYFUL = "playful"
    SERIOUS = "serious"
    INSPIRATIONAL = "inspirational"
    EDUCATIONAL = "educational"
    CONVERSATIONAL = "conversational"

    @classmethod
    def has_value(cls, value: str) -> bool:
        """Check if value is a valid BrandVoiceTone."""
        try:
            cls(value)
            return True
        except ValueError:
            return False


class ReadingLevel(str, enum.Enum):
    """Target reading levels."""

    ELEMENTARY = "elementary"
    MIDDLE_SCHOOL = "middle_school"
    HIGH_SCHOOL = "high_school"
    COLLEGE = "college"
    GRADUATE = "graduate"
    EXPERT = "expert"


@dataclass
class BrandVoice:
    """Brand voice configuration."""

    # Core personality traits
    personality: List[str] = field(default_factory=list)
    tones: List[BrandVoiceTone] = field(default_factory=list)

    # Phrase management
    always: List[str] = field(default_factory=list)  # Phrases to always include
    never: List[str] = field(default_factory=list)  # Banned phrases
    key_phrases: List[str] = field(default_factory=list)  # Preferred phrases
    key_numbers: Dict[str, str] = field(default_factory=dict)  # Key statistics

    # Style preferences
    reading_level: Optional[ReadingLevel] = None
    target_emotions: List[str] = field(default_factory=list)

    # Compliance
    required_disclaimers: List[str] = field(default_factory=list)
    trademark_symbols: Dict[str, str] = field(default_factory=dict)  # word -> symbol

    # Metadata
    organization_id: Optional[str] = None
    project_id: Optional[str] = None


@dataclass
class BrandVoiceScore:
    """Brand voice compliance score for content."""

    overall_score: float  # 0.0-1.0
    tone_match: float  # 0.0-1.0
    phrase_compliance: float  # 0.0-1.0
    reading_level_match: float  # 0.0-1.0
    emotion_match: float  # 0.0-1.0
    compliance_issues: List[str] = field(default_factory=list)
    suggestions: List[str] = field(default_factory=list)


class BrandVoiceEngine:
    """
    Brand voice engine for managing and enforcing brand voice.

    Provides scoring, validation, and enforcement of brand voice guidelines.
    """

    def __init__(self):
        """Initialize the brand voice engine."""
        # In-memory storage (can be extended to use database)
        self._brand_voices: Dict[str, BrandVoice] = {}

    def set_brand_voice(
        self,
        project_id: str,
        brand_voice: BrandVoice,
    ) -> None:
        """
        Set brand voice configuration for a project.

        Args:
            project_id: Lattice project ID
            brand_voice: Brand voice configuration
        """
        brand_voice.project_id = project_id
        self._brand_voices[project_id] = brand_voice

    def get_brand_voice(self, project_id: str) -> Optional[BrandVoice]:
        """
        Get brand voice configuration for a project.

        Args:
            project_id: Lattice project ID

        Returns:
            Brand voice configuration or None if not set
        """
        return self._brand_voices.get(project_id)

    def score_content(
        self,
        content: str,
        project_id: Optional[str] = None,
        brand_voice: Optional[BrandVoice] = None,
    ) -> BrandVoiceScore:
        """
        Score content against brand voice guidelines.

        Args:
            content: Content text to score
            project_id: Optional project ID to look up brand voice
            brand_voice: Optional brand voice to use (overrides project_id)

        Returns:
            BrandVoiceScore with compliance metrics
        """
        # Get brand voice
        if brand_voice is None and project_id is not None:
            brand_voice = self.get_brand_voice(project_id)

        if brand_voice is None:
            # No brand voice configured - return neutral score
            return BrandVoiceScore(
                overall_score=0.5,
                tone_match=0.5,
                phrase_compliance=0.5,
                reading_level_match=0.5,
                emotion_match=0.5,
            )

        content_lower = content.lower()
        issues: List[str] = []
        suggestions: List[str] = []

        # Check for banned phrases
        phrase_compliance = 1.0
        for banned in brand_voice.never:
            if banned.lower() in content_lower:
                issues.append(f"Contains banned phrase: '{banned}'")
                phrase_compliance = max(0.0, phrase_compliance - 0.2)

        # Check for required phrases
        for required in brand_voice.always:
            if required.lower() not in content_lower:
                issues.append(f"Missing required phrase: '{required}'")
                phrase_compliance = max(0.0, phrase_compliance - 0.1)
                suggestions.append(f"Consider including: '{required}'")

        # Check for key phrases (preferred but not required)
        key_phrase_count = sum(
            1 for phrase in brand_voice.key_phrases if phrase.lower() in content_lower
        )
        if brand_voice.key_phrases:
            phrase_compliance = min(
                1.0,
                phrase_compliance + (key_phrase_count / len(brand_voice.key_phrases)) * 0.3,
            )

        # Tone matching (simplified - would use LLM in production)
        tone_match = 0.7  # Placeholder

        # Reading level (simplified - would use Flesch-Kincaid in production)
        reading_level_match = 0.8  # Placeholder

        # Emotion matching (simplified)
        emotion_match = 0.7  # Placeholder

        # Calculate overall score
        overall_score = (
            tone_match * 0.3
            + phrase_compliance * 0.4
            + reading_level_match * 0.15
            + emotion_match * 0.15
        )

        return BrandVoiceScore(
            overall_score=overall_score,
            tone_match=tone_match,
            phrase_compliance=phrase_compliance,
            reading_level_match=reading_level_match,
            emotion_match=emotion_match,
            compliance_issues=issues,
            suggestions=suggestions,
        )

    def enforce_brand_voice(
        self,
        content: str,
        project_id: Optional[str] = None,
        brand_voice: Optional[BrandVoice] = None,
    ) -> str:
        """
        Enforce brand voice on content by applying transformations.

        Args:
            content: Content text to enforce
            project_id: Optional project ID to look up brand voice
            brand_voice: Optional brand voice to use (overrides project_id)

        Returns:
            Modified content with brand voice enforced
        """
        # Get brand voice
        if brand_voice is None and project_id is not None:
            brand_voice = self.get_brand_voice(project_id)

        if brand_voice is None:
            return content

        result = content

        # Replace banned phrases
        for banned in brand_voice.never:
            # Simple replacement (would use more sophisticated NLP in production)
            result = result.replace(banned, "")

        # Insert required disclaimers
        if brand_voice.required_disclaimers:
            for disclaimer in brand_voice.required_disclaimers:
                if disclaimer not in result:
                    result = f"{result}\n\n{disclaimer}"

        # Apply trademark symbols
        for word, symbol in brand_voice.trademark_symbols.items():
            # Replace word with word + symbol (simple approach)
            result = result.replace(word, f"{word}{symbol}")

        return result
