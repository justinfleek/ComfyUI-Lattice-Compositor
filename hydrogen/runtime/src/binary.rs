//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!                                             // hydrogen // runtime // binary
//! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//!
//! Binary format parser matching Hydrogen's specification.
//!
//! See `docs/BINARY_FORMAT.md` for the complete specification.

use bytemuck::from_bytes;

use crate::commands::{
    AnimationStateHeader, AnimationTarget, CommandBuffer, CommandType, Contour, ContourHeader,
    DrawCommand, GlyphInstancePayload, GlyphPathHeader, GlyphPayload, Header, ParticlePayload,
    PathCommand, PathCommandType, PathDataHeader, Point3D, QuadPayload, Radii4, RectPayload,
    WordHeader, HEADER_SIZE,
};

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                      // parser
// ═══════════════════════════════════════════════════════════════════════════════

/// Parse a command buffer from raw bytes.
///
/// This implements the Hydrogen binary format specification.
pub fn parse_command_buffer(bytes: &[u8]) -> Result<CommandBuffer, &'static str> {
    if bytes.len() < HEADER_SIZE {
        return Err("Buffer too small for header");
    }

    // Parse header
    let header: Header = *from_bytes(&bytes[0..HEADER_SIZE]);
    header.validate()?;

    // Parse commands
    let mut commands = Vec::with_capacity(header.count as usize);
    let mut offset = HEADER_SIZE;

    for _ in 0..header.count {
        if offset >= bytes.len() {
            return Err("Unexpected end of buffer");
        }

        let (cmd, size) = parse_command(&bytes[offset..])?;
        commands.push(cmd);
        offset += size;
    }

    Ok(CommandBuffer { header, commands })
}

/// Parse a single command from bytes.
///
/// Returns the command and the number of bytes consumed.
fn parse_command(bytes: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    if bytes.len() < 4 {
        return Err("Buffer too small for command header");
    }

    let cmd_type = CommandType::try_from(bytes[0])?;

    // Skip 3 bytes of padding
    let payload = &bytes[4..];

    match cmd_type {
        CommandType::Noop => Ok((DrawCommand::Noop, 4)),

        CommandType::DrawRect => {
            const PAYLOAD_SIZE: usize = 56;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawRect payload");
            }
            let rect: RectPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Rect(rect), 4 + PAYLOAD_SIZE))
        }

        CommandType::DrawQuad => {
            const PAYLOAD_SIZE: usize = 52;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawQuad payload");
            }
            let quad: QuadPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Quad(quad), 4 + PAYLOAD_SIZE))
        }

        CommandType::DrawGlyph => {
            const PAYLOAD_SIZE: usize = 40;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawGlyph payload");
            }
            let glyph: GlyphPayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Glyph(glyph), 4 + PAYLOAD_SIZE))
        }

        CommandType::DrawPath => {
            // Path is variable-length, skip for now
            Ok((DrawCommand::Noop, 4))
        }

        CommandType::DrawParticle => {
            const PAYLOAD_SIZE: usize = 32;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawParticle payload");
            }
            let particle: ParticlePayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::Particle(particle), 4 + PAYLOAD_SIZE))
        }

        CommandType::PushClip => {
            // Rect clip subtype
            if payload.is_empty() {
                return Err("Buffer too small for PushClip");
            }

            let subtype = payload[0];
            if subtype == 0x00 {
                // Rect clip: 36 bytes
                const CLIP_SIZE: usize = 36;
                if payload.len() < 4 + CLIP_SIZE {
                    return Err("Buffer too small for clip rect");
                }

                let clip_data = &payload[4..4 + CLIP_SIZE];
                let x =
                    f32::from_le_bytes([clip_data[0], clip_data[1], clip_data[2], clip_data[3]]);
                let y =
                    f32::from_le_bytes([clip_data[4], clip_data[5], clip_data[6], clip_data[7]]);
                let width =
                    f32::from_le_bytes([clip_data[8], clip_data[9], clip_data[10], clip_data[11]]);
                let height = f32::from_le_bytes([
                    clip_data[12],
                    clip_data[13],
                    clip_data[14],
                    clip_data[15],
                ]);
                let radii: Radii4 = *from_bytes(&clip_data[16..32]);

                Ok((
                    DrawCommand::PushClipRect {
                        x,
                        y,
                        width,
                        height,
                        radii,
                    },
                    4 + 4 + CLIP_SIZE,
                ))
            } else {
                // Unknown clip subtype
                Ok((DrawCommand::Noop, 4))
            }
        }

        CommandType::PopClip => Ok((DrawCommand::PopClip, 4)),

        // v2 typography as geometry
        CommandType::DrawGlyphPath => parse_glyph_path(payload),

        CommandType::DrawGlyphInstance => {
            const PAYLOAD_SIZE: usize = 76;
            if payload.len() < PAYLOAD_SIZE {
                return Err("Buffer too small for DrawGlyphInstance payload");
            }
            let instance: GlyphInstancePayload = *from_bytes(&payload[..PAYLOAD_SIZE]);
            Ok((DrawCommand::GlyphInstance(instance), 4 + PAYLOAD_SIZE))
        }

        CommandType::DrawWord => parse_word(payload),

        CommandType::DefinePathData => parse_path_data(payload),

        CommandType::UpdateAnimationState => parse_animation_state(payload),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                           // v2 parsing helpers
// ═══════════════════════════════════════════════════════════════════════════════

/// Parse a DrawGlyphPath command (variable length).
fn parse_glyph_path(payload: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    const HEADER_SIZE: usize = 48;
    if payload.len() < HEADER_SIZE {
        return Err("Buffer too small for GlyphPath header");
    }

    let header: GlyphPathHeader = *from_bytes(&payload[..HEADER_SIZE]);
    let mut offset = HEADER_SIZE;
    let mut contours = Vec::with_capacity(header.contour_count as usize);

    for _ in 0..header.contour_count {
        let (contour, size) = parse_contour(&payload[offset..])?;
        contours.push(contour);
        offset += size;
    }

    Ok((
        DrawCommand::GlyphPath { header, contours },
        4 + offset, // +4 for command header
    ))
}

/// Parse a contour (closed path) within a glyph.
fn parse_contour(payload: &[u8]) -> Result<(Contour, usize), &'static str> {
    const CONTOUR_HEADER_SIZE: usize = 4;
    if payload.len() < CONTOUR_HEADER_SIZE {
        return Err("Buffer too small for contour header");
    }

    let header: ContourHeader = *from_bytes(&payload[..CONTOUR_HEADER_SIZE]);
    let mut offset = CONTOUR_HEADER_SIZE;
    let mut commands = Vec::with_capacity(header.command_count as usize);

    for _ in 0..header.command_count {
        let (cmd, size) = parse_path_command(&payload[offset..])?;
        commands.push(cmd);
        offset += size;
    }

    Ok((
        Contour {
            is_outer: header.is_outer != 0,
            commands,
        },
        offset,
    ))
}

/// Parse a single path command.
fn parse_path_command(payload: &[u8]) -> Result<(PathCommand, usize), &'static str> {
    if payload.len() < 4 {
        return Err("Buffer too small for path command header");
    }

    let cmd_type = PathCommandType::try_from(payload[0])?;
    let data = &payload[4..]; // Skip command byte + 3 padding bytes

    match cmd_type {
        PathCommandType::MoveTo => {
            if data.len() < 8 {
                return Err("Buffer too small for MoveTo");
            }
            let x = f32::from_le_bytes([data[0], data[1], data[2], data[3]]);
            let y = f32::from_le_bytes([data[4], data[5], data[6], data[7]]);
            Ok((PathCommand::MoveTo { x, y }, 12))
        }
        PathCommandType::LineTo => {
            if data.len() < 8 {
                return Err("Buffer too small for LineTo");
            }
            let x = f32::from_le_bytes([data[0], data[1], data[2], data[3]]);
            let y = f32::from_le_bytes([data[4], data[5], data[6], data[7]]);
            Ok((PathCommand::LineTo { x, y }, 12))
        }
        PathCommandType::QuadTo => {
            if data.len() < 16 {
                return Err("Buffer too small for QuadTo");
            }
            let cx = f32::from_le_bytes([data[0], data[1], data[2], data[3]]);
            let cy = f32::from_le_bytes([data[4], data[5], data[6], data[7]]);
            let x = f32::from_le_bytes([data[8], data[9], data[10], data[11]]);
            let y = f32::from_le_bytes([data[12], data[13], data[14], data[15]]);
            Ok((PathCommand::QuadTo { cx, cy, x, y }, 20))
        }
        PathCommandType::CubicTo => {
            if data.len() < 24 {
                return Err("Buffer too small for CubicTo");
            }
            let c1x = f32::from_le_bytes([data[0], data[1], data[2], data[3]]);
            let c1y = f32::from_le_bytes([data[4], data[5], data[6], data[7]]);
            let c2x = f32::from_le_bytes([data[8], data[9], data[10], data[11]]);
            let c2y = f32::from_le_bytes([data[12], data[13], data[14], data[15]]);
            let x = f32::from_le_bytes([data[16], data[17], data[18], data[19]]);
            let y = f32::from_le_bytes([data[20], data[21], data[22], data[23]]);
            Ok((
                PathCommand::CubicTo {
                    c1x,
                    c1y,
                    c2x,
                    c2y,
                    x,
                    y,
                },
                28,
            ))
        }
        PathCommandType::Close => Ok((PathCommand::Close, 4)),
    }
}

/// Parse a DrawWord command (variable length).
fn parse_word(payload: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    const HEADER_SIZE: usize = 40;
    if payload.len() < HEADER_SIZE {
        return Err("Buffer too small for Word header");
    }

    let header: WordHeader = *from_bytes(&payload[..HEADER_SIZE]);
    let glyph_count = header.glyph_count as usize;

    // Calculate required size: header + (glyph_count * 4 for IDs) + (glyph_count * 12 for positions)
    let ids_size = glyph_count * 4;
    let positions_size = glyph_count * 12;
    let total_size = HEADER_SIZE + ids_size + positions_size;

    if payload.len() < total_size {
        return Err("Buffer too small for Word data");
    }

    // Parse path data IDs
    let ids_start = HEADER_SIZE;
    let mut path_data_ids = Vec::with_capacity(glyph_count);
    for i in 0..glyph_count {
        let offset = ids_start + i * 4;
        let id = u32::from_le_bytes([
            payload[offset],
            payload[offset + 1],
            payload[offset + 2],
            payload[offset + 3],
        ]);
        path_data_ids.push(id);
    }

    // Parse positions
    let positions_start = ids_start + ids_size;
    let mut positions = Vec::with_capacity(glyph_count);
    for i in 0..glyph_count {
        let offset = positions_start + i * 12;
        let point: Point3D = *from_bytes(&payload[offset..offset + 12]);
        positions.push(point);
    }

    Ok((
        DrawCommand::Word {
            header,
            path_data_ids,
            positions,
        },
        4 + total_size, // +4 for command header
    ))
}

/// Parse a DefinePathData command (variable length).
fn parse_path_data(payload: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    const HEADER_SIZE: usize = 32;
    if payload.len() < HEADER_SIZE {
        return Err("Buffer too small for PathData header");
    }

    let header: PathDataHeader = *from_bytes(&payload[..HEADER_SIZE]);
    let mut offset = HEADER_SIZE;
    let mut commands = Vec::with_capacity(header.command_count as usize);

    for _ in 0..header.command_count {
        let (cmd, size) = parse_path_command(&payload[offset..])?;
        commands.push(cmd);
        offset += size;
    }

    Ok((
        DrawCommand::PathData { header, commands },
        4 + offset, // +4 for command header
    ))
}

/// Parse an UpdateAnimationState command (variable length).
fn parse_animation_state(payload: &[u8]) -> Result<(DrawCommand, usize), &'static str> {
    const HEADER_SIZE: usize = 8;
    if payload.len() < HEADER_SIZE {
        return Err("Buffer too small for AnimationState header");
    }

    let header: AnimationStateHeader = *from_bytes(&payload[..HEADER_SIZE]);
    let target_count = header.target_count as usize;

    const TARGET_SIZE: usize = 52;
    let targets_size = target_count * TARGET_SIZE;
    let total_size = HEADER_SIZE + targets_size;

    if payload.len() < total_size {
        return Err("Buffer too small for AnimationState targets");
    }

    let mut targets = Vec::with_capacity(target_count);
    for i in 0..target_count {
        let offset = HEADER_SIZE + i * TARGET_SIZE;
        let target: AnimationTarget = *from_bytes(&payload[offset..offset + TARGET_SIZE]);
        targets.push(target);
    }

    Ok((
        DrawCommand::AnimationState { header, targets },
        4 + total_size, // +4 for command header
    ))
}

// ═══════════════════════════════════════════════════════════════════════════════
//                                                                       // tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::MAGIC;

    #[test]
    fn test_parse_empty_buffer() {
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic: HYDG
            0x01, 0x00, 0x00, 0x00, // version: 1
            0x00, 0x00, 0x00, 0x00, // count: 0
            0x00, 0x00, 0x00, 0x00, // flags: 0
        ];

        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.header.magic, MAGIC);
        assert_eq!(buffer.header.count, 0);
        assert!(buffer.commands.is_empty());
    }

    #[test]
    fn test_parse_noop() {
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic
            0x01, 0x00, 0x00, 0x00, // version
            0x01, 0x00, 0x00, 0x00, // count: 1
            0x00, 0x00, 0x00, 0x00, // flags
            // Noop command
            0x00, 0x00, 0x00, 0x00, // type + padding
        ];

        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.commands.len(), 1);
        assert!(matches!(buffer.commands[0], DrawCommand::Noop));
    }

    #[test]
    fn test_invalid_magic() {
        let bytes = [
            0x00, 0x00, 0x00, 0x00, // wrong magic
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        let result = parse_command_buffer(&bytes);
        assert!(result.is_err());
    }

    // ═══════════════════════════════════════════════════════════════════════════
    //                                                             // v2 tests
    // ═══════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_parse_glyph_instance() {
        #[rustfmt::skip]
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic
            0x01, 0x00, 0x00, 0x00, // version
            0x01, 0x00, 0x00, 0x00, // count: 1
            0x00, 0x00, 0x00, 0x00, // flags
            // DrawGlyphInstance command (0x21)
            0x21, 0x00, 0x00, 0x00, // type + padding
            // Payload (76 bytes)
            0x01, 0x00, 0x00, 0x00, // pathDataId: 1
            0x00, 0x00, 0xC8, 0x42, // posX: 100.0
            0x00, 0x00, 0x48, 0x42, // posY: 50.0
            0x00, 0x00, 0x00, 0x00, // posZ: 0.0
            0x00, 0x00, 0x00, 0x00, // rotX: 0.0
            0x00, 0x00, 0x00, 0x00, // rotY: 0.0
            0x00, 0x00, 0x00, 0x00, // rotZ: 0.0
            0x00, 0x00, 0x80, 0x3F, // scaleX: 1.0
            0x00, 0x00, 0x80, 0x3F, // scaleY: 1.0
            0x00, 0x00, 0x80, 0x3F, // scaleZ: 1.0
            0xFF, 0x00, 0x00, 0xFF, // color: red (RGBA u8)
            0x00, 0x00, 0x00, 0x00, // animPhase: 0.0
            0x00, 0x00, 0x00, 0x00, // springVel: 0.0
            0x00, 0x00, 0x00, 0x00, // springDisp: 0.0
            0x00, 0x00, 0x00, 0x3F, // springTension: 0.5
            0x00, 0x00, 0x00, 0x3F, // springDamping: 0.5
            0x00, 0x00, 0x80, 0x3F, // springMass: 1.0
            0x00, 0x00, 0x00, 0x00, // depth: 0.0
            0x05, 0x00, 0x00, 0x00, // pickId: 5
        ];

        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.commands.len(), 1);

        if let DrawCommand::GlyphInstance(payload) = &buffer.commands[0] {
            assert_eq!(payload.path_data_id, 1);
            assert_eq!(payload.pos_x, 100.0);
            assert_eq!(payload.pos_y, 50.0);
            assert_eq!(payload.scale_x, 1.0);
            assert_eq!(payload.color.r, 255);
            assert_eq!(payload.color.g, 0);
            assert_eq!(payload.color.b, 0);
            assert_eq!(payload.color.a, 255);
            assert_eq!(payload.pick_id, 5);
        } else {
            panic!("Expected GlyphInstance command");
        }
    }

    #[test]
    fn test_parse_path_command_types() {
        // Test MoveTo
        let move_bytes = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x3F, 0x00, 0x00, 0x00, 0x40,
        ];
        let (cmd, size) = parse_path_command(&move_bytes).unwrap();
        assert_eq!(size, 12);
        if let PathCommand::MoveTo { x, y } = cmd {
            assert_eq!(x, 1.0);
            assert_eq!(y, 2.0);
        } else {
            panic!("Expected MoveTo");
        }

        // Test LineTo
        let line_bytes = [
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x40, 0x00, 0x00, 0x80, 0x40,
        ];
        let (cmd, size) = parse_path_command(&line_bytes).unwrap();
        assert_eq!(size, 12);
        if let PathCommand::LineTo { x, y } = cmd {
            assert_eq!(x, 3.0);
            assert_eq!(y, 4.0);
        } else {
            panic!("Expected LineTo");
        }

        // Test Close
        let close_bytes = [0x05, 0x00, 0x00, 0x00];
        let (cmd, size) = parse_path_command(&close_bytes).unwrap();
        assert_eq!(size, 4);
        assert!(matches!(cmd, PathCommand::Close));
    }

    #[test]
    fn test_parse_animation_state() {
        #[rustfmt::skip]
        let bytes = [
            // Header
            0x47, 0x44, 0x59, 0x48, // magic
            0x01, 0x00, 0x00, 0x00, // version
            0x01, 0x00, 0x00, 0x00, // count: 1
            0x00, 0x00, 0x00, 0x00, // flags
            // UpdateAnimationState command (0x24)
            0x24, 0x00, 0x00, 0x00, // type + padding
            // AnimationState header (8 bytes)
            0x01, 0x00,             // targetCount: 1
            0x01,                   // mode: Additive
            0x00,                   // padding
            0x00, 0x00, 0x80, 0x42, // frameTime: 64.0 (ms)
            // AnimationTarget (52 bytes)
            0x07, 0x00, 0x00, 0x00, // targetId: 7
            0x00,                   // targetType: GlyphInstance
            0x00, 0x00, 0x00,       // padding
            0x00, 0x00, 0x80, 0x3F, // deltaPosX: 1.0
            0x00, 0x00, 0x00, 0x00, // deltaPosY: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaPosZ: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaRotX: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaRotY: 0.0
            0x00, 0x00, 0xB4, 0x42, // deltaRotZ: 90.0
            0x00, 0x00, 0x00, 0x00, // deltaScaleX: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaScaleY: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaScaleZ: 0.0
            0x00, 0x00, 0x00, 0x00, // deltaColor: (0, 0, 0, 0)
            0xCD, 0xCC, 0xCC, 0x3D, // phaseAdvance: 0.1
        ];

        let buffer = parse_command_buffer(&bytes).unwrap();
        assert_eq!(buffer.commands.len(), 1);

        if let DrawCommand::AnimationState { header, targets } = &buffer.commands[0] {
            assert_eq!(header.target_count, 1);
            assert_eq!(header.mode, 1); // Additive
            assert_eq!(header.frame_time, 64.0);
            assert_eq!(targets.len(), 1);
            assert_eq!(targets[0].target_id, 7);
            assert_eq!(targets[0].target_type, 0); // GlyphInstance
            assert_eq!(targets[0].delta_pos.x, 1.0);
            assert_eq!(targets[0].delta_rot.z, 90.0);
        } else {
            panic!("Expected AnimationState command");
        }
    }
}
