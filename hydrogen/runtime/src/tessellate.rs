//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                         // hydrogen // runtime // tessellate
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Bezier path tessellation for GPU rendering.
//!
//! Converts vector paths (bezier curves) into triangle meshes suitable for
//! WebGPU rendering. Uses adaptive subdivision based on flatness criterion.

use crate::commands::{Contour, PathCommand};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                   // constants
// ═══════════════════════════════════════════════════════════════════════════════

/// Maximum subdivision depth for bezier curves.
const MAX_SUBDIVISION_DEPTH: u32 = 8;

/// Flatness threshold for curve subdivision (squared distance in pixels).
const FLATNESS_THRESHOLD: f32 = 0.25;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // types
// ═══════════════════════════════════════════════════════════════════════════════

/// A 2D point for tessellation.
#[derive(Debug, Clone, Copy, Default)]
pub struct Point {
    pub x: f32,
    pub y: f32,
}

impl Point {
    pub fn new(x: f32, y: f32) -> Self {
        Point { x, y }
    }

    pub fn lerp(self, other: Point, t: f32) -> Point {
        Point {
            x: self.x + (other.x - self.x) * t,
            y: self.y + (other.y - self.y) * t,
        }
    }

    pub fn distance_squared(self, other: Point) -> f32 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        dx * dx + dy * dy
    }
}

/// Tessellated path data ready for GPU rendering.
#[derive(Debug, Clone)]
pub struct TessellatedPath {
    /// Vertex positions (x, y pairs).
    pub vertices: Vec<f32>,
    /// Triangle indices.
    pub indices: Vec<u32>,
}

impl TessellatedPath {
    pub fn new() -> Self {
        TessellatedPath {
            vertices: Vec::new(),
            indices: Vec::new(),
        }
    }

    /// Number of vertices in the mesh.
    pub fn vertex_count(&self) -> usize {
        self.vertices.len() / 2
    }
}

impl Default for TessellatedPath {
    fn default() -> Self {
        Self::new()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                             // tessellation
// ═══════════════════════════════════════════════════════════════════════════════

/// Tessellate a list of contours into a triangle mesh.
///
/// Uses ear-clipping triangulation for filled paths.
pub fn tessellate_contours(contours: &[Contour]) -> TessellatedPath {
    let mut result = TessellatedPath::new();

    for contour in contours {
        let polygon = flatten_contour(contour);
        if polygon.len() < 3 {
            continue;
        }

        let base_vertex = result.vertex_count() as u32;

        // Add vertices
        for point in &polygon {
            result.vertices.push(point.x);
            result.vertices.push(point.y);
        }

        // Triangulate using ear clipping
        let triangles = ear_clip_triangulate(&polygon);
        for idx in triangles {
            result.indices.push(base_vertex + idx);
        }
    }

    result
}

/// Tessellate path commands into a triangle mesh.
pub fn tessellate_path_commands(commands: &[PathCommand]) -> TessellatedPath {
    let polygon = flatten_path_commands(commands);
    if polygon.len() < 3 {
        return TessellatedPath::new();
    }

    let mut result = TessellatedPath::new();

    // Add vertices
    for point in &polygon {
        result.vertices.push(point.x);
        result.vertices.push(point.y);
    }

    // Triangulate
    let triangles = ear_clip_triangulate(&polygon);
    for idx in triangles {
        result.indices.push(idx);
    }

    result
}

/// Flatten a contour's bezier curves into a polygon of line segments.
fn flatten_contour(contour: &Contour) -> Vec<Point> {
    flatten_path_commands(&contour.commands)
}

/// Flatten path commands into a polygon.
fn flatten_path_commands(commands: &[PathCommand]) -> Vec<Point> {
    let mut points = Vec::new();
    let mut current = Point::default();
    let mut start = Point::default();

    for cmd in commands {
        match cmd {
            PathCommand::MoveTo { x, y } => {
                current = Point::new(*x, *y);
                start = current;
                points.push(current);
            }
            PathCommand::LineTo { x, y } => {
                current = Point::new(*x, *y);
                points.push(current);
            }
            PathCommand::QuadTo { cx, cy, x, y } => {
                let control = Point::new(*cx, *cy);
                let end = Point::new(*x, *y);
                flatten_quadratic(&mut points, current, control, end, 0);
                current = end;
            }
            PathCommand::CubicTo {
                c1x,
                c1y,
                c2x,
                c2y,
                x,
                y,
            } => {
                let c1 = Point::new(*c1x, *c1y);
                let c2 = Point::new(*c2x, *c2y);
                let end = Point::new(*x, *y);
                flatten_cubic(&mut points, current, c1, c2, end, 0);
                current = end;
            }
            PathCommand::Close => {
                // Don't add duplicate point - polygon is implicitly closed
                current = start;
            }
        }
    }

    // Remove duplicate closing point if present
    if points.len() > 1 {
        let first = points[0];
        let last = points[points.len() - 1];
        if first.distance_squared(last) < 0.0001 {
            points.pop();
        }
    }

    points
}

/// Recursively flatten a quadratic bezier curve.
fn flatten_quadratic(points: &mut Vec<Point>, p0: Point, p1: Point, p2: Point, depth: u32) {
    if depth >= MAX_SUBDIVISION_DEPTH || is_quadratic_flat(p0, p1, p2) {
        points.push(p2);
        return;
    }

    // De Casteljau subdivision at t=0.5
    let q0 = p0.lerp(p1, 0.5);
    let q1 = p1.lerp(p2, 0.5);
    let mid = q0.lerp(q1, 0.5);

    flatten_quadratic(points, p0, q0, mid, depth + 1);
    flatten_quadratic(points, mid, q1, p2, depth + 1);
}

/// Recursively flatten a cubic bezier curve.
fn flatten_cubic(points: &mut Vec<Point>, p0: Point, p1: Point, p2: Point, p3: Point, depth: u32) {
    if depth >= MAX_SUBDIVISION_DEPTH || is_cubic_flat(p0, p1, p2, p3) {
        points.push(p3);
        return;
    }

    // De Casteljau subdivision at t=0.5
    let q0 = p0.lerp(p1, 0.5);
    let q1 = p1.lerp(p2, 0.5);
    let q2 = p2.lerp(p3, 0.5);
    let r0 = q0.lerp(q1, 0.5);
    let r1 = q1.lerp(q2, 0.5);
    let mid = r0.lerp(r1, 0.5);

    flatten_cubic(points, p0, q0, r0, mid, depth + 1);
    flatten_cubic(points, mid, r1, q2, p3, depth + 1);
}

/// Check if a quadratic bezier is flat enough to be approximated by a line.
fn is_quadratic_flat(p0: Point, p1: Point, p2: Point) -> bool {
    // Distance from control point to line segment p0-p2
    let dx = p2.x - p0.x;
    let dy = p2.y - p0.y;
    let len_sq = dx * dx + dy * dy;

    if len_sq < 0.0001 {
        return p1.distance_squared(p0) < FLATNESS_THRESHOLD;
    }

    let t = ((p1.x - p0.x) * dx + (p1.y - p0.y) * dy) / len_sq;
    let t = t.clamp(0.0, 1.0);

    let proj = Point {
        x: p0.x + t * dx,
        y: p0.y + t * dy,
    };

    p1.distance_squared(proj) < FLATNESS_THRESHOLD
}

/// Check if a cubic bezier is flat enough to be approximated by a line.
fn is_cubic_flat(p0: Point, p1: Point, p2: Point, p3: Point) -> bool {
    // Check both control points' distance from the line p0-p3
    let dx = p3.x - p0.x;
    let dy = p3.y - p0.y;
    let len_sq = dx * dx + dy * dy;

    if len_sq < 0.0001 {
        return p1.distance_squared(p0) < FLATNESS_THRESHOLD
            && p2.distance_squared(p0) < FLATNESS_THRESHOLD;
    }

    let d1 = point_line_distance_sq(p1, p0, dx, dy, len_sq);
    let d2 = point_line_distance_sq(p2, p0, dx, dy, len_sq);

    d1 < FLATNESS_THRESHOLD && d2 < FLATNESS_THRESHOLD
}

/// Calculate squared distance from point to line segment.
fn point_line_distance_sq(p: Point, line_start: Point, dx: f32, dy: f32, len_sq: f32) -> f32 {
    let t = ((p.x - line_start.x) * dx + (p.y - line_start.y) * dy) / len_sq;
    let t = t.clamp(0.0, 1.0);

    let proj = Point {
        x: line_start.x + t * dx,
        y: line_start.y + t * dy,
    };

    p.distance_squared(proj)
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // ear clipping
// ═══════════════════════════════════════════════════════════════════════════════

/// Simple ear-clipping triangulation for convex and simple concave polygons.
///
/// Returns indices into the original vertex array forming triangles.
fn ear_clip_triangulate(polygon: &[Point]) -> Vec<u32> {
    let n = polygon.len();
    if n < 3 {
        return Vec::new();
    }

    if n == 3 {
        return vec![0, 1, 2];
    }

    // Determine polygon winding order
    let clockwise = is_polygon_clockwise(polygon);

    let mut indices: Vec<usize> = (0..n).collect();
    let mut triangles = Vec::with_capacity((n - 2) * 3);

    let mut i = 0;
    let mut attempts = 0;
    let max_attempts = n * n;

    while indices.len() > 3 && attempts < max_attempts {
        let len = indices.len();
        let prev = indices[(i + len - 1) % len];
        let curr = indices[i % len];
        let next = indices[(i + 1) % len];

        if is_ear(polygon, &indices, prev, curr, next, clockwise) {
            triangles.push(prev as u32);
            triangles.push(curr as u32);
            triangles.push(next as u32);
            indices.remove(i % len);
            if i >= indices.len() && !indices.is_empty() {
                i = 0;
            }
            attempts = 0;
        } else {
            i = (i + 1) % indices.len();
            attempts += 1;
        }
    }

    // Add final triangle
    if indices.len() == 3 {
        triangles.push(indices[0] as u32);
        triangles.push(indices[1] as u32);
        triangles.push(indices[2] as u32);
    }

    triangles
}

/// Calculate signed area of polygon (positive = CCW, negative = CW).
fn polygon_signed_area(polygon: &[Point]) -> f32 {
    let n = polygon.len();
    let mut area = 0.0;
    for i in 0..n {
        let j = (i + 1) % n;
        area += polygon[i].x * polygon[j].y;
        area -= polygon[j].x * polygon[i].y;
    }
    area * 0.5
}

/// Check if polygon is clockwise.
fn is_polygon_clockwise(polygon: &[Point]) -> bool {
    polygon_signed_area(polygon) < 0.0
}

/// Check if a vertex forms an ear (valid triangle for clipping).
fn is_ear(
    polygon: &[Point],
    indices: &[usize],
    prev: usize,
    curr: usize,
    next: usize,
    clockwise: bool,
) -> bool {
    let a = polygon[prev];
    let b = polygon[curr];
    let c = polygon[next];

    // Check if triangle has correct winding (convex vertex)
    // For CW polygons, we need CW triangles (not CCW)
    let triangle_ccw = is_ccw(a, b, c);
    if clockwise && triangle_ccw {
        return false;
    }
    if !clockwise && !triangle_ccw {
        return false;
    }

    // Check that no other vertices are inside this triangle
    for &idx in indices {
        if idx == prev || idx == curr || idx == next {
            continue;
        }

        if point_in_triangle(polygon[idx], a, b, c) {
            return false;
        }
    }

    true
}

/// Check if three points are in counter-clockwise order.
fn is_ccw(a: Point, b: Point, c: Point) -> bool {
    (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x) > 0.0
}

/// Check if point p is inside triangle abc.
fn point_in_triangle(p: Point, a: Point, b: Point, c: Point) -> bool {
    let v0x = c.x - a.x;
    let v0y = c.y - a.y;
    let v1x = b.x - a.x;
    let v1y = b.y - a.y;
    let v2x = p.x - a.x;
    let v2y = p.y - a.y;

    let dot00 = v0x * v0x + v0y * v0y;
    let dot01 = v0x * v1x + v0y * v1y;
    let dot02 = v0x * v2x + v0y * v2y;
    let dot11 = v1x * v1x + v1y * v1y;
    let dot12 = v1x * v2x + v1y * v2y;

    let inv_denom = 1.0 / (dot00 * dot11 - dot01 * dot01);
    let u = (dot11 * dot02 - dot01 * dot12) * inv_denom;
    let v = (dot00 * dot12 - dot01 * dot02) * inv_denom;

    u >= 0.0 && v >= 0.0 && (u + v) <= 1.0
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tessellate_triangle() {
        let commands = vec![
            PathCommand::MoveTo { x: 0.0, y: 0.0 },
            PathCommand::LineTo { x: 100.0, y: 0.0 },
            PathCommand::LineTo { x: 50.0, y: 100.0 },
            PathCommand::Close,
        ];

        let result = tessellate_path_commands(&commands);

        // Should have 3 vertices (6 floats)
        assert_eq!(result.vertex_count(), 3);
        // Should have 1 triangle (3 indices)
        assert_eq!(result.indices.len(), 3);
    }

    #[test]
    fn test_tessellate_quad() {
        let commands = vec![
            PathCommand::MoveTo { x: 0.0, y: 0.0 },
            PathCommand::LineTo { x: 100.0, y: 0.0 },
            PathCommand::LineTo { x: 100.0, y: 100.0 },
            PathCommand::LineTo { x: 0.0, y: 100.0 },
            PathCommand::Close,
        ];

        let result = tessellate_path_commands(&commands);

        // Should have 4 vertices
        assert_eq!(result.vertex_count(), 4);
        // Should produce 2 triangles (6 indices)
        assert_eq!(result.indices.len(), 6);
    }

    #[test]
    fn test_flatten_quadratic() {
        let commands = vec![
            PathCommand::MoveTo { x: 0.0, y: 0.0 },
            PathCommand::QuadTo {
                cx: 50.0,
                cy: 100.0,
                x: 100.0,
                y: 0.0,
            },
            PathCommand::Close,
        ];

        let result = tessellate_path_commands(&commands);

        // Should have multiple vertices from curve subdivision
        assert!(result.vertex_count() > 3);
    }

    #[test]
    fn test_is_ccw() {
        let a = Point::new(0.0, 0.0);
        let b = Point::new(1.0, 0.0);
        let c = Point::new(0.5, 1.0);

        assert!(is_ccw(a, b, c));
        assert!(!is_ccw(a, c, b));
    }
}
