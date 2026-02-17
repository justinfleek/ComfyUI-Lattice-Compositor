"""
MAESTRO State

Derived state from events. State is never mutated directly - it is only
derived from events via pure fold operations.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from .events import (
    AgentSelectedEvent,
    MaestroEvent,
    NoMatchEvent,
    RoutingCompletedEvent,
    RoutingRequestedEvent,
)
from .types import SelectedAgent


@dataclass(frozen=True)
class RoutingResult:
    """
    Result of a routing request.

    Immutable - results are derived from events.
    """

    request_id: str
    session_id: str
    user_input: str
    selected_agent: Optional[SelectedAgent]
    routing_type: str  # 'pending' | 'direct' | 'broadcast' | 'no_match'
    message_id: Optional[str]
    correlation_id: Optional[str]
    completed: bool


@dataclass(frozen=True)
class MaestroState:
    """
    Complete MAESTRO state derived from events.

    State is derived from events via fold operations, never mutated directly.
    """

    # Pending routing requests (not yet completed)
    pending_requests: dict[str, RoutingResult] = field(default_factory=dict)

    # Completed routing results (for audit trail, bounded to last 1000)
    completed_results: list[RoutingResult] = field(default_factory=list)

    # Routing statistics
    total_requests: int = 0
    total_matches: int = 0
    total_no_matches: int = 0


def empty_maestro_state() -> MaestroState:
    """
    Create empty MAESTRO state.

    Pure function with no side effects. Returns a fresh, empty state
    that can be used as the initial state for event folding.
    """
    return MaestroState()


def apply_event(state: MaestroState, event: MaestroEvent) -> MaestroState:
    """
    Apply event to state, producing new state.

    This is a pure function: the same state and event always produce the same
    resulting state. This enables deterministic replay - any state can be
    reached by folding events from the initial empty state.
    """
    if isinstance(event, RoutingRequestedEvent):
        return _apply_routing_requested(state, event)
    elif isinstance(event, AgentSelectedEvent):
        return _apply_agent_selected(state, event)
    elif isinstance(event, RoutingCompletedEvent):
        return _apply_routing_completed(state, event)
    elif isinstance(event, NoMatchEvent):
        return _apply_no_match(state, event)
    else:
        # Unknown event type - return state unchanged
        return state


def _apply_routing_requested(
    state: MaestroState, event: RoutingRequestedEvent
) -> MaestroState:
    """Apply routing requested event."""
    # Create pending result
    result = RoutingResult(
        request_id=event.request_id,
        session_id=event.session_id,
        user_input=event.user_input,
        selected_agent=None,
        routing_type="pending",
        message_id=None,
        correlation_id=None,
        completed=False,
    )

    # Update state (immutable - create new dict)
    new_pending = {**state.pending_requests, event.request_id: result}

    return MaestroState(
        pending_requests=new_pending,
        completed_results=state.completed_results,
        total_requests=state.total_requests + 1,
        total_matches=state.total_matches,
        total_no_matches=state.total_no_matches,
    )


def _apply_agent_selected(
    state: MaestroState, event: AgentSelectedEvent
) -> MaestroState:
    """Apply agent selected event."""
    if event.request_id not in state.pending_requests:
        # Request doesn't exist - return state unchanged
        return state

    # Get existing result
    existing = state.pending_requests[event.request_id]

    # Create selected agent
    selected = SelectedAgent(
        agent_id=event.agent_id,
        agent_name=event.agent_name,
        capability_id=event.capability_id,
        capability_name=event.capability_name,
        confidence=event.confidence,
        domain=event.domain,
    )

    # Update result with selected agent
    updated_result = RoutingResult(
        request_id=existing.request_id,
        session_id=existing.session_id,
        user_input=existing.user_input,
        selected_agent=selected,
        routing_type=existing.routing_type,
        message_id=existing.message_id,
        correlation_id=existing.correlation_id,
        completed=existing.completed,
    )

    new_pending = {**state.pending_requests, event.request_id: updated_result}

    return MaestroState(
        pending_requests=new_pending,
        completed_results=state.completed_results,
        total_requests=state.total_requests,
        total_matches=state.total_matches,
        total_no_matches=state.total_no_matches,
    )


def _apply_routing_completed(
    state: MaestroState, event: RoutingCompletedEvent
) -> MaestroState:
    """Apply routing completed event."""
    if event.request_id not in state.pending_requests:
        # Request doesn't exist - return state unchanged
        return state

    # Get existing result
    existing = state.pending_requests[event.request_id]

    # Create completed result
    completed_result = RoutingResult(
        request_id=existing.request_id,
        session_id=existing.session_id,
        user_input=existing.user_input,
        selected_agent=existing.selected_agent,
        routing_type=event.routing_type,
        message_id=event.message_id,
        correlation_id=event.correlation_id,
        completed=True,
    )

    # Remove from pending, add to completed
    new_pending = {
        k: v for k, v in state.pending_requests.items() if k != event.request_id
    }

    # Bound completed results to last 1000
    new_completed = [*state.completed_results, completed_result]
    if len(new_completed) > 1000:
        new_completed = new_completed[-1000:]

    # Update match count
    is_match = event.routing_type in ("direct", "broadcast")

    return MaestroState(
        pending_requests=new_pending,
        completed_results=new_completed,
        total_requests=state.total_requests,
        total_matches=state.total_matches + (1 if is_match else 0),
        total_no_matches=state.total_no_matches + (0 if is_match else 1),
    )


def _apply_no_match(state: MaestroState, event: NoMatchEvent) -> MaestroState:
    """Apply no match event."""
    if event.request_id not in state.pending_requests:
        # Request doesn't exist - return state unchanged
        return state

    # Get existing result
    existing = state.pending_requests[event.request_id]

    # Create no-match result
    no_match_result = RoutingResult(
        request_id=existing.request_id,
        session_id=existing.session_id,
        user_input=existing.user_input,
        selected_agent=None,
        routing_type="no_match",
        message_id=None,
        correlation_id=None,
        completed=True,
    )

    # Remove from pending, add to completed
    new_pending = {
        k: v for k, v in state.pending_requests.items() if k != event.request_id
    }

    # Bound completed results to last 1000
    new_completed = [*state.completed_results, no_match_result]
    if len(new_completed) > 1000:
        new_completed = new_completed[-1000:]

    return MaestroState(
        pending_requests=new_pending,
        completed_results=new_completed,
        total_requests=state.total_requests,
        total_matches=state.total_matches,
        total_no_matches=state.total_no_matches + 1,
    )
