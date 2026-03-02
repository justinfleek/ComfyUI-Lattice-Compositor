"""Type stub for ComfyUI server module."""

from typing import Any, Callable, TypeVar

F = TypeVar("F", bound=Callable[..., Any])


class RouteTable:
    """ComfyUI route table: .post/.get/.delete(path) return decorators."""

    def post(self, path: str) -> Callable[[F], F]: ...  # noqa: ARG002
    def get(self, path: str) -> Callable[[F], F]: ...  # noqa: ARG002
    def delete(self, path: str) -> Callable[[F], F]: ...  # noqa: ARG002


class PromptServer:
    instance: "PromptServer"
    routes: RouteTable

    def __init__(self) -> None: ...
    def register_route(self, path: str, handler: Any) -> None: ...  # noqa: ARG002


