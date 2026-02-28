//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                           // hydrogen // runtime // commands
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Command types matching Hydrogen's binary format specification.
//!
//! See `docs/BINARY_FORMAT.md` for the complete specification.

use bytemuck::{Pod, Zeroable};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                    // constants
// ═══════════════════════════════════════════════════════════════════════════════

/// Magic number: "HYDG" in little-endian ASCII
pub const MAGIC: u32 = 0x48594447;

/// Current format version
pub const VERSION: u32 = 1;

/// Header size in bytes
pub const HEADER_SIZE: usize = 16;

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // header
// ═══════════════════════════════════════════════════════════════════════════════

/// Command buffer header.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Header {
    pub magic: u32,
    pub version: u32,
    pub count: u32,
    pub flags: u32,
}

impl Header {
    /// Validate the header.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.magic != MAGIC {
            return Err("Invalid magic number");
        }
        if self.version != VERSION {
            return Err("Unsupported version");
        }
        if self.flags != 0 {
            return Err("Unknown flags");
        }
        Ok(())
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                // command types
// ═══════════════════════════════════════════════════════════════════════════════

/// Command type discriminant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CommandType {
    // v1 commands
    Noop = 0x00,
    DrawRect = 0x01,
    DrawQuad = 0x02,
    DrawGlyph = 0x03,
    DrawPath = 0x04,
    DrawParticle = 0x05,
    PushClip = 0x10,
    PopClip = 0x11,
    // v2 typography as geometry
    DrawGlyphPath = 0x20,
    DrawGlyphInstance = 0x21,
    DrawWord = 0x22,
    DefinePathData = 0x23,
    UpdateAnimationState = 0x24,
}

impl TryFrom<u8> for CommandType {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x00 => Ok(CommandType::Noop),
            0x01 => Ok(CommandType::DrawRect),
            0x02 => Ok(CommandType::DrawQuad),
            0x03 => Ok(CommandType::DrawGlyph),
            0x04 => Ok(CommandType::DrawPath),
            0x05 => Ok(CommandType::DrawParticle),
            0x10 => Ok(CommandType::PushClip),
            0x11 => Ok(CommandType::PopClip),
            0x20 => Ok(CommandType::DrawGlyphPath),
            0x21 => Ok(CommandType::DrawGlyphInstance),
            0x22 => Ok(CommandType::DrawWord),
            0x23 => Ok(CommandType::DefinePathData),
            0x24 => Ok(CommandType::UpdateAnimationState),
            _ => Err("Unknown command type"),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // payloads
// ═══════════════════════════════════════════════════════════════════════════════

/// RGBA color in unit interval [0.0, 1.0].
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Color4 {
    pub r: f32,
    pub g: f32,
    pub b: f32,
    pub a: f32,
}

/// 2D point.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Point2D {
    pub x: f32,
    pub y: f32,
}

/// Corner radii.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Radii4 {
    pub top_left: f32,
    pub top_right: f32,
    pub bottom_right: f32,
    pub bottom_left: f32,
}

/// DrawRect payload (56 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct RectPayload {
    pub x: f32,
    pub y: f32,
    pub width: f32,
    pub height: f32,
    pub color: Color4,
    pub radii: Radii4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawQuad payload (52 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct QuadPayload {
    pub v0: Point2D,
    pub v1: Point2D,
    pub v2: Point2D,
    pub v3: Point2D,
    pub color: Color4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawGlyph payload (40 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct GlyphPayload {
    pub x: f32,
    pub y: f32,
    pub glyph_index: u32,
    pub font_id: u32,
    pub font_size: f32,
    pub color: Color4,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawParticle payload (32 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct ParticlePayload {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub size: f32,
    pub color: Color4,
    pub pick_id: u32,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                        // v2 typography enums
// ═══════════════════════════════════════════════════════════════════════════════

/// Stagger direction for word animations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum StaggerDirection {
    LeftToRight = 0,
    RightToLeft = 1,
    CenterOut = 2,
    EdgesIn = 3,
    Random = 4,
    TopToBottom = 5,
    BottomToTop = 6,
}

impl TryFrom<u8> for StaggerDirection {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(StaggerDirection::LeftToRight),
            1 => Ok(StaggerDirection::RightToLeft),
            2 => Ok(StaggerDirection::CenterOut),
            3 => Ok(StaggerDirection::EdgesIn),
            4 => Ok(StaggerDirection::Random),
            5 => Ok(StaggerDirection::TopToBottom),
            6 => Ok(StaggerDirection::BottomToTop),
            _ => Err("Unknown stagger direction"),
        }
    }
}

/// Easing function for animations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum EasingFunction {
    Linear = 0,
    EaseInQuad = 1,
    EaseOutQuad = 2,
    EaseInOutQuad = 3,
    EaseInCubic = 4,
    EaseOutCubic = 5,
    EaseInOutCubic = 6,
    EaseInElastic = 7,
    EaseOutElastic = 8,
    EaseInOutElastic = 9,
    EaseInBounce = 10,
    EaseOutBounce = 11,
    EaseSpring = 12,
}

impl TryFrom<u8> for EasingFunction {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(EasingFunction::Linear),
            1 => Ok(EasingFunction::EaseInQuad),
            2 => Ok(EasingFunction::EaseOutQuad),
            3 => Ok(EasingFunction::EaseInOutQuad),
            4 => Ok(EasingFunction::EaseInCubic),
            5 => Ok(EasingFunction::EaseOutCubic),
            6 => Ok(EasingFunction::EaseInOutCubic),
            7 => Ok(EasingFunction::EaseInElastic),
            8 => Ok(EasingFunction::EaseOutElastic),
            9 => Ok(EasingFunction::EaseInOutElastic),
            10 => Ok(EasingFunction::EaseInBounce),
            11 => Ok(EasingFunction::EaseOutBounce),
            12 => Ok(EasingFunction::EaseSpring),
            _ => Err("Unknown easing function"),
        }
    }
}

/// Update mode for animation state changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum UpdateMode {
    Replace = 0,
    Additive = 1,
    Blend = 2,
}

impl TryFrom<u8> for UpdateMode {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(UpdateMode::Replace),
            1 => Ok(UpdateMode::Additive),
            2 => Ok(UpdateMode::Blend),
            _ => Err("Unknown update mode"),
        }
    }
}

/// Target type for animation updates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum AnimationTargetType {
    GlyphInstance = 0,
    Word = 1,
    PathData = 2,
    ControlPoint = 3,
}

impl TryFrom<u8> for AnimationTargetType {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(AnimationTargetType::GlyphInstance),
            1 => Ok(AnimationTargetType::Word),
            2 => Ok(AnimationTargetType::PathData),
            3 => Ok(AnimationTargetType::ControlPoint),
            _ => Err("Unknown animation target type"),
        }
    }
}

/// Path command type for bezier paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum PathCommandType {
    MoveTo = 0x01,
    LineTo = 0x02,
    QuadTo = 0x03,
    CubicTo = 0x04,
    Close = 0x05,
}

impl TryFrom<u8> for PathCommandType {
    type Error = &'static str;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0x01 => Ok(PathCommandType::MoveTo),
            0x02 => Ok(PathCommandType::LineTo),
            0x03 => Ok(PathCommandType::QuadTo),
            0x04 => Ok(PathCommandType::CubicTo),
            0x05 => Ok(PathCommandType::Close),
            _ => Err("Unknown path command type"),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                     // v2 typography payloads
// ═══════════════════════════════════════════════════════════════════════════════

/// 3D point.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Point3D {
    pub x: f32,
    pub y: f32,
    pub z: f32,
}

/// 3D bounding box.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct BoundingBox3D {
    pub min_x: f32,
    pub min_y: f32,
    pub min_z: f32,
    pub max_x: f32,
    pub max_y: f32,
    pub max_z: f32,
}

/// RGBA color as bytes (0-255).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct Color4u8 {
    pub r: u8,
    pub g: u8,
    pub b: u8,
    pub a: u8,
}

/// Spring physics state.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct SpringState {
    pub velocity: f32,
    pub displacement: f32,
    pub tension: f32,
    pub damping: f32,
    pub mass: f32,
}

/// DrawGlyphPath header (48 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct GlyphPathHeader {
    pub glyph_id: u32,
    pub font_id: u32,
    pub contour_count: u16,
    pub padding: u16,
    pub bounds: BoundingBox3D,
    pub advance_width: f32,
    pub depth: f32,
    pub pick_id: u32,
}

/// Per-contour header (4 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct ContourHeader {
    pub command_count: u16,
    pub is_outer: u8,
    pub padding: u8,
}

/// A path command with its data.
#[derive(Debug, Clone)]
pub enum PathCommand {
    MoveTo {
        x: f32,
        y: f32,
    },
    LineTo {
        x: f32,
        y: f32,
    },
    QuadTo {
        cx: f32,
        cy: f32,
        x: f32,
        y: f32,
    },
    CubicTo {
        c1x: f32,
        c1y: f32,
        c2x: f32,
        c2y: f32,
        x: f32,
        y: f32,
    },
    Close,
}

/// A contour (closed path) in a glyph.
#[derive(Debug, Clone)]
pub struct Contour {
    pub is_outer: bool,
    pub commands: Vec<PathCommand>,
}

/// DrawGlyphInstance payload (76 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct GlyphInstancePayload {
    pub path_data_id: u32,
    pub pos_x: f32,
    pub pos_y: f32,
    pub pos_z: f32,
    pub rot_x: f32,
    pub rot_y: f32,
    pub rot_z: f32,
    pub scale_x: f32,
    pub scale_y: f32,
    pub scale_z: f32,
    pub color: Color4u8,
    pub anim_phase: f32,
    pub spring: SpringState,
    pub depth: f32,
    pub pick_id: u32,
}

/// DrawWord header (40 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct WordHeader {
    pub word_id: u32,
    pub glyph_count: u16,
    pub stagger_dir: u8,
    pub easing: u8,
    pub origin_x: f32,
    pub origin_y: f32,
    pub origin_z: f32,
    pub stagger_delay: f32,
    pub stagger_seed: u32,
    pub color: Color4u8,
    pub depth: f32,
    pub pick_id: u32,
}

/// DefinePathData header (32 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct PathDataHeader {
    pub path_data_id: u32,
    pub command_count: u32,
    pub bounds: BoundingBox3D,
}

/// UpdateAnimationState header (8 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct AnimationStateHeader {
    pub target_count: u16,
    pub mode: u8,
    pub padding: u8,
    pub frame_time: f32,
}

/// Color delta as signed bytes.
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct ColorDelta {
    pub r: i8,
    pub g: i8,
    pub b: i8,
    pub a: i8,
}

/// Per-target animation update (52 bytes).
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
#[repr(C)]
pub struct AnimationTarget {
    pub target_id: u32,
    pub target_type: u8,
    pub padding: [u8; 3],
    pub delta_pos: Point3D,
    pub delta_rot: Point3D,
    pub delta_scale: Point3D,
    pub delta_color: ColorDelta,
    pub phase_advance: f32,
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                     // commands
// ═══════════════════════════════════════════════════════════════════════════════

/// A parsed draw command.
#[derive(Debug, Clone)]
pub enum DrawCommand {
    // v1 commands
    Noop,
    Rect(RectPayload),
    Quad(QuadPayload),
    Glyph(GlyphPayload),
    Particle(ParticlePayload),
    PushClipRect {
        x: f32,
        y: f32,
        width: f32,
        height: f32,
        radii: Radii4,
    },
    PopClip,
    // v2 typography as geometry
    GlyphPath {
        header: GlyphPathHeader,
        contours: Vec<Contour>,
    },
    GlyphInstance(GlyphInstancePayload),
    Word {
        header: WordHeader,
        path_data_ids: Vec<u32>,
        positions: Vec<Point3D>,
    },
    PathData {
        header: PathDataHeader,
        commands: Vec<PathCommand>,
    },
    AnimationState {
        header: AnimationStateHeader,
        targets: Vec<AnimationTarget>,
    },
}

impl DrawCommand {
    /// Get the depth of this command for sorting.
    pub fn depth(&self) -> f32 {
        match self {
            // v1 commands
            DrawCommand::Noop => 0.0,
            DrawCommand::Rect(p) => p.depth,
            DrawCommand::Quad(p) => p.depth,
            DrawCommand::Glyph(p) => p.depth,
            DrawCommand::Particle(p) => p.z,
            DrawCommand::PushClipRect { .. } => 0.0,
            DrawCommand::PopClip => 0.0,
            // v2 typography commands
            DrawCommand::GlyphPath { header, .. } => header.depth,
            DrawCommand::GlyphInstance(p) => p.depth,
            DrawCommand::Word { header, .. } => header.depth,
            DrawCommand::PathData { .. } => 0.0,
            DrawCommand::AnimationState { .. } => 0.0,
        }
    }

    /// Get the pick ID if this command is interactive.
    pub fn pick_id(&self) -> Option<u32> {
        let id = match self {
            // v1 commands
            DrawCommand::Noop => 0,
            DrawCommand::Rect(p) => p.pick_id,
            DrawCommand::Quad(p) => p.pick_id,
            DrawCommand::Glyph(p) => p.pick_id,
            DrawCommand::Particle(p) => p.pick_id,
            DrawCommand::PushClipRect { .. } => 0,
            DrawCommand::PopClip => 0,
            // v2 typography commands
            DrawCommand::GlyphPath { header, .. } => header.pick_id,
            DrawCommand::GlyphInstance(p) => p.pick_id,
            DrawCommand::Word { header, .. } => header.pick_id,
            DrawCommand::PathData { .. } => 0,
            DrawCommand::AnimationState { .. } => 0,
        };
        if id == 0 {
            None
        } else {
            Some(id)
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                              // command buffer
// ═══════════════════════════════════════════════════════════════════════════════

/// A parsed command buffer ready for rendering.
#[derive(Debug)]
pub struct CommandBuffer {
    pub header: Header,
    pub commands: Vec<DrawCommand>,
}

impl CommandBuffer {
    /// Create an empty command buffer.
    pub fn empty() -> Self {
        CommandBuffer {
            header: Header {
                magic: MAGIC,
                version: VERSION,
                count: 0,
                flags: 0,
            },
            commands: Vec::new(),
        }
    }

    /// Sort commands by depth for painter's algorithm.
    pub fn sort_by_depth(&mut self) {
        self.commands.sort_by(|a, b| {
            a.depth()
                .partial_cmp(&b.depth())
                .unwrap_or(std::cmp::Ordering::Equal)
        });
    }
}
