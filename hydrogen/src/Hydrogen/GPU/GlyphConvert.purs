-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // glyph-convert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GlyphConvert — Bridge between Schema Typography and GPU DrawCommands.
-- |
-- | ## Purpose
-- |
-- | The Schema.Typography.GlyphGeometry module defines glyphs as pure geometric
-- | data with 3D coordinates, winding direction, and semantic metadata. The
-- | GPU.DrawCommand module defines the wire format for GPU dispatch.
-- |
-- | This module provides the conversion functions between these representations.
-- |
-- | ## Architecture
-- |
-- | ```
-- | GlyphPath (Schema)  ────────────►  DrawGlyphPath (GPU)
-- |      │                                    │
-- |      │                                    ▼
-- |      ▼                             PathDataParams
-- | Contour + PathCommand3D  ─────►  ContourData + PathSegment
-- | ```
-- |
-- | ## Coordinate Handling
-- |
-- | GlyphGeometry uses 3D coordinates (x, y, z). DrawCommand PathSegments are 2D.
-- | During conversion:
-- | - X, Y coordinates pass through directly
-- | - Z is preserved in the glyph's BoundingBox3D for depth sorting
-- | - Per-instance Z transforms are applied via GlyphInstanceParams
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Typography.GlyphGeometry
-- | - Hydrogen.GPU.DrawCommand
-- | - Hydrogen.Schema.Dimension.Device (Pixel)

module Hydrogen.GPU.GlyphConvert
  ( -- * GlyphPath Conversion
    glyphPathToDrawCommand
  , glyphPathToPathData
  
  -- * Contour Conversion
  , contourToContourData
  , pathCommand3DToSegment
  
  -- * Bounds Conversion
  , glyphBoundsToBoundingBox3D
  
  -- * Batch Conversion
  , convertGlyphPaths
  , createPathDataRegistry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (+)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Typography.GlyphGeometry as GG
import Hydrogen.GPU.DrawCommand as DC

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // glyphpath conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a GlyphPath from Schema to GlyphPathParams for DrawGlyphPath command.
-- |
-- | Parameters:
-- | - glyphId: Unicode codepoint or internal glyph index
-- | - fontId: Font registry index
-- | - glyph: The GlyphPath to convert
-- |
-- | Returns a GlyphPathParams suitable for creating a DrawGlyphPath command.
glyphPathToDrawCommand
  :: forall msg
   . Int           -- glyphId (Unicode codepoint)
  -> Int           -- fontId (font registry index)
  -> GG.GlyphPath  -- source glyph
  -> DC.GlyphPathParams msg
glyphPathToDrawCommand glyphId fontId glyph =
  { glyphId
  , fontId
  , contours: map contourToContourData glyph.contours
  , bounds: glyphBoundsToBoundingBox3D glyph.bounds
  , advanceWidth: glyph.advanceWidth
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- | Convert a GlyphPath to PathDataParams for instanced rendering.
-- |
-- | PathData is shared geometry referenced by multiple GlyphInstance commands.
-- | This enables efficient font rendering where each unique character's geometry
-- | is stored once and instanced many times.
-- |
-- | Parameters:
-- | - pathDataId: Unique identifier for referencing this path data
-- | - glyph: The GlyphPath to convert
glyphPathToPathData :: Int -> GG.GlyphPath -> DC.PathDataParams
glyphPathToPathData pathDataId glyph =
  { pathDataId
  , commands: extractAllSegments glyph
  , bounds: glyphBoundsToBoundingBox3D glyph.bounds
  }

-- | Extract all path segments from a glyph (flattening contours).
extractAllSegments :: GG.GlyphPath -> Array DC.PathSegment
extractAllSegments glyph =
  Array.concatMap extractContourSegments glyph.contours
  where
    extractContourSegments :: GG.Contour -> Array DC.PathSegment
    extractContourSegments c = map pathCommand3DToSegment c.commands

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // contour conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert a Schema Contour to GPU ContourData.
-- |
-- | Preserves winding direction as isOuter flag:
-- | - WindingClockwise → isOuter = true
-- | - WindingCounterClockwise → isOuter = false
contourToContourData :: GG.Contour -> DC.ContourData
contourToContourData c =
  { commands: map pathCommand3DToSegment c.commands
  , isOuter: c.winding `isClockwise` true
  }
  where
    isClockwise :: GG.ContourWinding -> Boolean -> Boolean
    isClockwise GG.WindingClockwise _ = true
    isClockwise GG.WindingCounterClockwise _ = false

-- | Convert a 3D PathCommand to a 2D PathSegment.
-- |
-- | Z coordinate is discarded — depth is handled at the instance level via
-- | GlyphInstanceParams.position.z, not in the path geometry itself.
-- |
-- | This matches how font rendering works: glyph outlines are 2D shapes,
-- | and 3D positioning is applied as a transform during instancing.
pathCommand3DToSegment :: GG.PathCommand3D -> DC.PathSegment
pathCommand3DToSegment = case _ of
  GG.MoveTo3D pt -> 
    DC.MoveTo (point3Dto2D pt)
  
  GG.LineTo3D pt -> 
    DC.LineTo (point3Dto2D pt)
  
  GG.QuadraticTo3D ctrl end -> 
    DC.QuadraticTo (point3Dto2D ctrl) (point3Dto2D end)
  
  GG.CubicTo3D c1 c2 end -> 
    DC.CubicTo (point3Dto2D c1) (point3Dto2D c2) (point3Dto2D end)
  
  GG.ClosePath3D -> 
    DC.ClosePath

-- | Convert 3D control point to 2D point (discarding Z).
point3Dto2D :: GG.ControlPoint3D -> DC.Point2D
point3Dto2D pt = { x: pt.x, y: pt.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // bounds conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Schema GlyphBounds to GPU BoundingBox3D.
-- |
-- | Both use the same coordinate system (Pixel), but with different field naming.
-- | Schema uses minX/maxX, GPU uses minX/maxX but in a different record structure.
glyphBoundsToBoundingBox3D :: GG.GlyphBounds -> DC.BoundingBox3D
glyphBoundsToBoundingBox3D b =
  { minX: b.minX
  , minY: b.minY
  , minZ: b.minZ
  , maxX: b.maxX
  , maxY: b.maxY
  , maxZ: b.maxZ
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // batch conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert multiple GlyphPaths to DrawCommands.
-- |
-- | For rendering a string, convert all unique glyphs to DrawGlyphPath commands.
-- | Each glyph gets a sequential glyphId starting from the provided base.
-- |
-- | Parameters:
-- | - fontId: Font registry index (shared by all glyphs)
-- | - baseGlyphId: Starting glyph ID
-- | - glyphs: Array of (Unicode codepoint, GlyphPath) pairs
convertGlyphPaths
  :: forall msg
   . Int                              -- fontId
  -> Array (Tuple Int GG.GlyphPath)   -- (codepoint, glyph) pairs
  -> Array (DC.DrawCommand msg)
convertGlyphPaths fontId glyphs =
  map toCommand glyphs
  where
    toCommand :: Tuple Int GG.GlyphPath -> DC.DrawCommand msg
    toCommand (Tuple codepoint glyph) =
      DC.DrawGlyphPath (glyphPathToDrawCommand codepoint fontId glyph)

-- | Create a PathData registry from glyphs for instanced rendering.
-- |
-- | Returns an array of (pathDataId, DefinePathData command) pairs.
-- | The pathDataId can be used in GlyphInstance commands to reference the geometry.
-- |
-- | This is the first step in the instancing workflow:
-- | 1. Create PathData for each unique glyph shape
-- | 2. Create GlyphInstance commands referencing PathData by ID
-- | 3. Group instances into Word commands for stagger animation
createPathDataRegistry
  :: forall msg
   . Int                              -- basePathDataId (starting ID)
  -> Array GG.GlyphPath               -- unique glyph shapes
  -> Array (Tuple Int (DC.DrawCommand msg))  -- (pathDataId, DefinePathData)
createPathDataRegistry baseId glyphs =
  Array.mapWithIndex createEntry glyphs
  where
    createEntry :: Int -> GG.GlyphPath -> Tuple Int (DC.DrawCommand msg)
    createEntry idx glyph =
      let pathDataId = baseId + idx
          pathData = glyphPathToPathData pathDataId glyph
      in Tuple pathDataId (DC.DefinePathData pathData)
