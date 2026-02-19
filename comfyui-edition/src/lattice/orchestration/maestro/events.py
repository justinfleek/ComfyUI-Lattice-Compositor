"""
MAESTRO Events

Event types for MAESTRO orchestration. All state changes are captured as
immutable events. State is derived from events via fold operations.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Optional

import hashlib
import json
import uuid


def make_uuid(namespace: str, content: str) -> str:
    """Generate UUID5 from namespace and content."""
    namespace_uuid = uuid.uuid5(uuid.NAMESPACE_DNS, namespace)
    return str(uuid.uuid5(namespace_uuid, content))


@dataclass(frozen=True)
class RoutingRequestedEvent:
    """Event: Routing request received by MAESTRO."""

    event_id: str  # UUID5 from request content
    timestamp: datetime  # UTC timestamp
    request_id: str  # UUID5 from request content
    session_id: str
    user_input: str
    context_hash: str  # Hash of context for determinism
    metadata: dict[str, str] = field(default_factory=dict)

    @classmethod
    def create(
        cls,
        request_id: str,
        session_id: str,
        user_input: str,
        context: Optional[dict[str, str | int | float | bool | None]] = None,
        metadata: Optional[dict[str, str]] = None,
    ) -> RoutingRequestedEvent:
        """Create routing requested event."""
        # Compute context hash for determinism
        context_json = json.dumps(context or {}, sort_keys=True)
        context_hash = hashlib.sha256(context_json.encode()).hexdigest()[:16]

        # Deterministic event ID from request content
        content = f"routing_requested:{request_id}:{session_id}:{user_input}"
        event_id = make_uuid("maestro_event", content)

        return cls(
            event_id=event_id,
            timestamp=datetime.now(timezone.utc),
            request_id=request_id,
            session_id=session_id,
            user_input=user_input,
            context_hash=context_hash,
            metadata=metadata or {},
        )


@dataclass(frozen=True)
class AgentSelectedEvent:
    """Event: Agent selected for routing request."""

    event_id: str  # UUID5 from selection content
    timestamp: datetime
    request_id: str  # Links to RoutingRequestedEvent
    agent_id: str
    agent_name: str
    capability_id: str
    capability_name: str
    confidence: float
    domain: str
    metadata: dict[str, str] = field(default_factory=dict)

    @classmethod
    def create(
        cls,
        request_id: str,
        agent_id: str,
        agent_name: str,
        capability_id: str,
        capability_name: str,
        confidence: float,
        domain: str,
        metadata: Optional[dict[str, str]] = None,
    ) -> AgentSelectedEvent:
        """Create agent selected event."""
        # Deterministic event ID from selection content
        content = f"agent_selected:{request_id}:{agent_id}:{capability_id}:{confidence}"
        event_id = make_uuid("maestro_event", content)

        return cls(
            event_id=event_id,
            timestamp=datetime.now(timezone.utc),
            request_id=request_id,
            agent_id=agent_id,
            agent_name=agent_name,
            capability_id=capability_id,
            capability_name=capability_name,
            confidence=confidence,
            domain=domain,
            metadata=metadata or {},
        )


@dataclass(frozen=True)
class RoutingCompletedEvent:
    """Event: Routing completed (message sent or no match found)."""

    event_id: str  # UUID5 from completion content
    timestamp: datetime
    request_id: str  # Links to RoutingRequestedEvent
    routing_type: str  # 'direct' | 'broadcast' | 'no_match'
    message_id: Optional[str]  # Message ID if routed
    correlation_id: Optional[str]  # Correlation ID for request/response
    agent_id: Optional[str]  # Selected agent ID (None if no_match)
    metadata: dict[str, str] = field(default_factory=dict)

    @classmethod
    def create(
        cls,
        request_id: str,
        routing_type: str,
        message_id: str | None = None,
        correlation_id: str | None = None,
        agent_id: str | None = None,
        metadata: Optional[dict[str, str]] = None,
    ) -> RoutingCompletedEvent:
        """Create routing completed event."""
        # Deterministic event ID from completion content
        msg_part = message_id or "none"
        agent_part = agent_id or "none"
        content = f"routing_completed:{request_id}:{routing_type}:{msg_part}:{agent_part}"
        event_id = make_uuid("maestro_event", content)

        return cls(
            event_id=event_id,
            timestamp=datetime.now(timezone.utc),
            request_id=request_id,
            routing_type=routing_type,
            message_id=message_id,
            correlation_id=correlation_id,
            agent_id=agent_id,
            metadata=metadata or {},
        )


@dataclass(frozen=True)
class NoMatchEvent:
    """Event: No matching agent found for routing request."""

    event_id: str  # UUID5 from no-match content
    timestamp: datetime
    request_id: str  # Links to RoutingRequestedEvent
    user_input: str  # Original input for debugging
    reason: str  # Why no match (e.g., "no_agents_available", "low_confidence")
    metadata: dict[str, str] = field(default_factory=dict)

    @classmethod
    def create(
        cls,
        request_id: str,
        user_input: str,
        reason: str,
        metadata: Optional[dict[str, str]] = None,
    ) -> NoMatchEvent:
        """Create no match event."""
        content = f"no_match:{request_id}:{reason}"
        event_id = make_uuid("maestro_event", content)

        return cls(
            event_id=event_id,
            timestamp=datetime.now(timezone.utc),
            request_id=request_id,
            user_input=user_input,
            reason=reason,
            metadata=metadata or {},
        )


# Union type for all MAESTRO events
MaestroEvent = (
    RoutingRequestedEvent
    | AgentSelectedEvent
    | RoutingCompletedEvent
    | NoMatchEvent
)
