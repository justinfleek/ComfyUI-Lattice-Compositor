"""Type stub for ComfyUI server module."""

from typing import Any, Callable, TypeVar

F = TypeVar("F", bound=Callable[..., Any])


class RouteTable:
    """ComfyUI route table: .post/.get/.delete(path) return decorators."""

    def post(self, _path: str) -> Callable[[F], F]: ...
    def get(self, _path: str) -> Callable[[F], F]: ...
    def delete(self, _path: str) -> Callable[[F], F]: ...


class PromptServer:
    instance: "PromptServer"
    routes: RouteTable

    def __init__(self) -> None: ...
    def register_route(self, _path: str, _handler: Any) -> None: ...


