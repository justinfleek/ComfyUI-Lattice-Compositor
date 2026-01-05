"""Type stub for ComfyUI server module."""

from typing import Any

class PromptServer:
    instance: "PromptServer"
    routes: dict[str, Any]
    
    def __init__(self) -> None: ...
    def register_route(self, path: str, handler: Any) -> None: ...


