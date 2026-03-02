"""Type stub for vtracer (optional dependency)."""

def convert_raw_image_to_svg(
    image_data: bytes,
    mode: str = "auto",
    color_mode: str = "color",
    hierarchical: str = "stacked",
    filter_speckle: int = 4,
    color_precision: int = 6,
    layer_difference: float = 16.0,
    corner_threshold: int = 60,
    length_threshold: float = 4.0,
    max_iterations: int = 10,
    splice_threshold: int = 45,
    path_precision: int = 3,
) -> str: ...

