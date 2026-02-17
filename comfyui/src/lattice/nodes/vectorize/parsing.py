"""SVG path parsing functions."""

import re

# JSON-compatible value types
JSONValue = str | int | float | bool | None | list | dict


def parse_svg_to_paths(svg_string: str, img_width: int, img_height: int) -> list[dict[str, JSONValue]]:
  """
  Parse SVG string and extract paths with control points.

  Converts SVG path commands to our ControlPoint format:
  - M = moveTo (start new path)
  - L = lineTo (straight line)
  - C = cubic bezier (with two control points)
  - Q = quadratic bezier (one control point, convert to cubic)
  - Z = closePath

  Returns list of path objects with controlPoints arrays.
  """
  paths = []

  # Extract path elements using regex
  # Match both <path d="..." .../> and <path d="..." ...></path>

  # Simpler approach: find all path elements and extract attributes
  path_elements = re.findall(r"<path([^>]*)/?>", svg_string, re.IGNORECASE)

  for idx, attrs in enumerate(path_elements):
    # Extract d attribute (path data)
    d_match = re.search(r'd=["\']([^"\']*)["\']', attrs)
    if not d_match:
      continue

    path_data = d_match.group(1)

    # Extract fill and stroke
    fill_match = re.search(r'fill=["\']([^"\']*)["\']', attrs)
    stroke_match = re.search(r'stroke=["\']([^"\']*)["\']', attrs)

    fill = fill_match.group(1) if fill_match else ""
    stroke = stroke_match.group(1) if stroke_match else ""

    # Skip invisible paths
    if fill == "none" and (not stroke or stroke == "none"):
      continue

    # Parse path commands to control points
    control_points, is_closed = parse_path_data(path_data, idx)

    if len(control_points) < 2:
      continue

    paths.append(
      {
        "id": f"path_{idx}",
        "fill": fill if fill != "none" else "",
        "stroke": stroke if stroke != "none" else "",
        "controlPoints": control_points,
        "closed": is_closed,
      }
    )

  return paths


def parse_path_data(d: str, path_idx: int) -> tuple[list[dict], bool]:
  """
  Parse SVG path data string into control points.

  Handles:
  - M/m: moveTo (absolute/relative)
  - L/l: lineTo
  - H/h: horizontal line
  - V/v: vertical line
  - C/c: cubic bezier
  - S/s: smooth cubic bezier
  - Q/q: quadratic bezier
  - T/t: smooth quadratic bezier
  - A/a: arc (approximated as line)
  - Z/z: close path

  Returns (control_points, is_closed)
  """
  control_points = []
  is_closed = False

  # Current position
  cx, cy = 0.0, 0.0
  # Start of current subpath (for Z command)
  start_x, start_y = 0.0, 0.0
  # Last control point (for smooth curves)
  last_cp_x, last_cp_y = None, None

  # Tokenize path data
  # Split by commands, keeping the command letter
  tokens = re.findall(r"([MmLlHhVvCcSsQqTtAaZz])|([+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?)", d)

  commands = []
  current_cmd = None
  current_args = []

  for token in tokens:
    cmd, num = token
    if cmd:
      if current_cmd is not None:
        commands.append((current_cmd, current_args))
      current_cmd = cmd
      current_args = []
    elif num:
      current_args.append(float(num))

  if current_cmd is not None:
    commands.append((current_cmd, current_args))

  point_idx = 0

  for cmd, args in commands:
    is_relative = cmd.islower()
    cmd_upper = cmd.upper()

    if cmd_upper == "M":
      # MoveTo - starts a new subpath
      i = 0
      while i < len(args):
        x = args[i] + (cx if is_relative else 0)
        y = args[i + 1] + (cy if is_relative else 0)

        if i == 0:
          # First M is moveTo
          start_x, start_y = x, y
          # Add point without handles (will be filled in by next command)
          control_points.append(
            {
              "id": f"cp_{path_idx}_{point_idx}",
              "x": x,
              "y": y,
              "handleIn": None,
              "handleOut": None,
              "type": "corner",
            }
          )
          point_idx += 1
        else:
          # Subsequent M coordinates are implicit lineTo
          control_points.append(
            {
              "id": f"cp_{path_idx}_{point_idx}",
              "x": x,
              "y": y,
              "handleIn": None,
              "handleOut": None,
              "type": "corner",
            }
          )
          point_idx += 1

        cx, cy = x, y
        i += 2
      last_cp_x, last_cp_y = None, None

    elif cmd_upper == "L":
      # LineTo
      i = 0
      while i < len(args):
        x = args[i] + (cx if is_relative else 0)
        y = args[i + 1] + (cy if is_relative else 0)

        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": None,
            "handleOut": None,
            "type": "corner",
          }
        )
        point_idx += 1
        cx, cy = x, y
        i += 2
      last_cp_x, last_cp_y = None, None

    elif cmd_upper == "H":
      # Horizontal line
      for x_val in args:
        x = x_val + (cx if is_relative else 0)
        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": cy,
            "handleIn": None,
            "handleOut": None,
            "type": "corner",
          }
        )
        point_idx += 1
        cx = x
      last_cp_x, last_cp_y = None, None

    elif cmd_upper == "V":
      # Vertical line
      for y_val in args:
        y = y_val + (cy if is_relative else 0)
        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": cx,
            "y": y,
            "handleIn": None,
            "handleOut": None,
            "type": "corner",
          }
        )
        point_idx += 1
        cy = y
      last_cp_x, last_cp_y = None, None

    elif cmd_upper == "C":
      # Cubic bezier: C cp1x cp1y cp2x cp2y x y
      i = 0
      while i + 5 < len(args):
        cp1x = args[i] + (cx if is_relative else 0)
        cp1y = args[i + 1] + (cy if is_relative else 0)
        cp2x = args[i + 2] + (cx if is_relative else 0)
        cp2y = args[i + 3] + (cy if is_relative else 0)
        x = args[i + 4] + (cx if is_relative else 0)
        y = args[i + 5] + (cy if is_relative else 0)

        # Set handleOut on previous point
        if control_points:
          control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
          # Determine point type based on handle symmetry
          if control_points[-1]["handleIn"]:
            control_points[-1]["type"] = "smooth"

        # Add new point with handleIn
        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": {"x": cp2x, "y": cp2y},
            "handleOut": None,
            "type": "smooth",
          }
        )
        point_idx += 1

        cx, cy = x, y
        last_cp_x, last_cp_y = cp2x, cp2y
        i += 6

    elif cmd_upper == "S":
      # Smooth cubic bezier: S cp2x cp2y x y
      # First control point is reflection of previous
      i = 0
      while i + 3 < len(args):
        # Reflect last control point
        if last_cp_x is not None:
          cp1x = 2 * cx - last_cp_x
          cp1y = 2 * cy - last_cp_y
        else:
          cp1x, cp1y = cx, cy

        cp2x = args[i] + (cx if is_relative else 0)
        cp2y = args[i + 1] + (cy if is_relative else 0)
        x = args[i + 2] + (cx if is_relative else 0)
        y = args[i + 3] + (cy if is_relative else 0)

        if control_points:
          control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
          control_points[-1]["type"] = "smooth"

        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": {"x": cp2x, "y": cp2y},
            "handleOut": None,
            "type": "smooth",
          }
        )
        point_idx += 1

        cx, cy = x, y
        last_cp_x, last_cp_y = cp2x, cp2y
        i += 4

    elif cmd_upper == "Q":
      # Quadratic bezier: Q cpx cpy x y
      # Convert to cubic by computing equivalent control points
      i = 0
      while i + 3 < len(args):
        qx = args[i] + (cx if is_relative else 0)
        qy = args[i + 1] + (cy if is_relative else 0)
        x = args[i + 2] + (cx if is_relative else 0)
        y = args[i + 3] + (cy if is_relative else 0)

        # Convert quadratic to cubic control points
        # CP1 = P0 + 2/3 * (Q - P0)
        # CP2 = P1 + 2/3 * (Q - P1)
        cp1x = cx + (2 / 3) * (qx - cx)
        cp1y = cy + (2 / 3) * (qy - cy)
        cp2x = x + (2 / 3) * (qx - x)
        cp2y = y + (2 / 3) * (qy - y)

        if control_points:
          control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
          control_points[-1]["type"] = "smooth"

        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": {"x": cp2x, "y": cp2y},
            "handleOut": None,
            "type": "smooth",
          }
        )
        point_idx += 1

        cx, cy = x, y
        last_cp_x, last_cp_y = qx, qy  # Store quadratic CP for T command
        i += 4

    elif cmd_upper == "T":
      # Smooth quadratic: T x y
      i = 0
      while i + 1 < len(args):
        # Reflect last quadratic control point
        if last_cp_x is not None:
          qx = 2 * cx - last_cp_x
          qy = 2 * cy - last_cp_y
        else:
          qx, qy = cx, cy

        x = args[i] + (cx if is_relative else 0)
        y = args[i + 1] + (cy if is_relative else 0)

        # Convert to cubic
        cp1x = cx + (2 / 3) * (qx - cx)
        cp1y = cy + (2 / 3) * (qy - cy)
        cp2x = x + (2 / 3) * (qx - x)
        cp2y = y + (2 / 3) * (qy - y)

        if control_points:
          control_points[-1]["handleOut"] = {"x": cp1x, "y": cp1y}
          control_points[-1]["type"] = "smooth"

        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": {"x": cp2x, "y": cp2y},
            "handleOut": None,
            "type": "smooth",
          }
        )
        point_idx += 1

        cx, cy = x, y
        last_cp_x, last_cp_y = qx, qy
        i += 2

    elif cmd_upper == "A":
      # Arc - approximate as line to endpoint for simplicity
      # Full arc support would require complex math
      i = 0
      while i + 6 < len(args):
        # Args: rx ry x-rotation large-arc sweep x y
        x = args[i + 5] + (cx if is_relative else 0)
        y = args[i + 6] + (cy if is_relative else 0)

        control_points.append(
          {
            "id": f"cp_{path_idx}_{point_idx}",
            "x": x,
            "y": y,
            "handleIn": None,
            "handleOut": None,
            "type": "corner",
          }
        )
        point_idx += 1

        cx, cy = x, y
        i += 7
      last_cp_x, last_cp_y = None, None

    elif cmd_upper == "Z":
      # Close path
      is_closed = True
      # If path should close smoothly, connect handles
      if control_points and len(control_points) > 1:
        # The first point's handleIn should connect from the last point
        # The last point's handleOut should connect to the first point
        pass  # Handles already set correctly by curve commands
      cx, cy = start_x, start_y
      last_cp_x, last_cp_y = None, None

  return control_points, is_closed
