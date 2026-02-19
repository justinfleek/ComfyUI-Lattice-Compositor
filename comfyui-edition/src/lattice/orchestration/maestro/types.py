"""
MAESTRO Types

Immutable types for MAESTRO orchestration. All types are frozen dataclasses
to ensure immutability and enable content-addressing.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional


@dataclass(frozen=True)
class RoutingRequest:
    """
    Request to route user intent to an agent.

    Immutable - routing requests are input to the orchestrator.
    """

    request_id: str  # UUID5 from request content
    session_id: str  # Session ID for context
    user_input: str  # User's intent text
    context: dict[str, str | int | float | bool | None] = field(default_factory=dict)
    metadata: dict[str, str] = field(default_factory=dict)


@dataclass(frozen=True)
class SelectedAgent:
    """
    Result of agent selection for a routing request.

    Immutable - selection results are output from the orchestrator.
    """

    agent_id: str  # Selected agent ID
    agent_name: str  # Agent name for logging
    capability_id: str  # Matched capability ID
    capability_name: str  # Capability name for logging
    confidence: float  # Match confidence (0.0-1.0)
    domain: str  # Agent domain


@dataclass(frozen=True)
class UserContext:
    """
    User context for agent scoring.

    Immutable - context is input to scoring functions.
    """

    session_id: str
    user_id: Optional[str] = None
    brand_id: Optional[str] = None
    recent_intents: tuple[str, ...] = field(default_factory=tuple)
    preferences: dict[str, str | int | float | bool | None] = field(default_factory=dict)
