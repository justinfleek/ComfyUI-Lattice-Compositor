"""
Lattice Orchestration System

Port of COMPASS MAESTRO orchestration (5-layer system, 199 tests).
Event-sourced orchestrator using pure functions.

Design Principles:
- Pure functions: All operations are referentially transparent
- Event sourcing: State changes produce events, state is derived from events
- Deterministic IDs: UUID5 generated from content ensures idempotency
- Bounded replay: Every state can be reached by folding events in order

Layer 0: Basic intent-to-agent routing
Layer 1: N-gram intent parsing with confidence scores
Layer 2: Multi-signal agent scoring
Layer 3: Content-addressed 4-tier caching
Layer 4: Predictive agent pre-loading for voice integration
"""

from .maestro import (
    MaestroState,
    RoutingRequest,
    RoutingResult,
    SelectedAgent,
    UserContext,
    empty_maestro_state,
    request_routing,
    route_to_agent,
    select_best_agent,
)

__all__ = [
    "MaestroState",
    "RoutingRequest",
    "RoutingResult",
    "SelectedAgent",
    "UserContext",
    "empty_maestro_state",
    "request_routing",
    "route_to_agent",
    "select_best_agent",
]
