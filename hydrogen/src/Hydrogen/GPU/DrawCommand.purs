-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // gpu // draw
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand — The GPU Primitive Vocabulary
-- |
-- | This module defines the complete set of GPU drawing operations. Every
-- | visual element in Hydrogen ultimately reduces to an array of DrawCommands.
-- |
-- | ## Design Principles
-- |
-- | 1. **Flat, not nested**: Arrays of commands, not trees. Trees require
-- |    traversal; arrays can be concatenated and batched.
-- |
-- | 2. **Immediate mode**: Each frame is a complete description. No retained
-- |    state, no diffing, no "what changed since last frame."
-- |
-- | 3. **Schema atoms only**: All parameters use bounded Schema types.
-- |    No strings, no CSS, no unbounded values.
-- |
-- | 4. **GPU-native**: Commands map directly to GPU operations. The interpreter
-- |    batches by material/texture and dispatches draw calls.
-- |
-- | 5. **Pick buffer ready**: Every interactive command carries an ID for
-- |    GPU-based hit testing via pick buffer.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Agent → Element → flatten → Array DrawCommand → interpret → WebGPU
-- |                                                          ↓
-- |                                               Array msg ← pick buffer
-- | ```
-- |
-- | At billion-agent scale, each agent emits its commands. The interpreter
-- | concatenates, sorts by material, and dispatches to GPU. No per-agent
-- | state synchronization required.
-- |
-- | ## Usage
-- |
-- | Components don't create DrawCommands directly — they create Element values.
-- | The flattener converts Element trees to DrawCommand arrays. This module
-- | is for the interpreter and advanced use cases.
-- |
-- | ```purescript
-- | import Hydrogen.GPU.DrawCommand as DC
-- |
-- | -- The interpreter receives these
-- | commands :: Array (DC.DrawCommand msg)
-- | commands =
-- |   [ DC.drawRect rectParams
-- |   , DC.drawGlyph glyphParams
-- |   ]
-- | ```

module Hydrogen.GPU.DrawCommand
  ( -- * Core Types
    DrawCommand
      ( DrawRect
      , DrawQuad
      , DrawGlyph
      , DrawPath
      , DrawParticle
      , PushClip
      , PopClip
      , Noop
      , DrawGlyphPath
      , DrawGlyphInstance
      , DrawWord
      , DefinePathData
      , UpdateAnimationState
      )
  , CommandBuffer
  , PickId
  , pickId
  , unwrapPickId
  
  -- * Rect Parameters
  , RectParams
  , rectParams
  
  -- * Quad Parameters (arbitrary 4-point)
  , Point2D
  , Point3D
  , QuadParams
  , quadParams
  
  -- * Glyph Parameters (SDF text)
  , GlyphParams
  , glyphParams
  
  -- * Path Parameters (vector paths)
  , PathParams
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ClosePath)
  , pathParams
  
  -- * Particle Parameters (billion-agent viz)
  , ParticleParams
  , particleParams
  
  -- * Clip Operations
  , ClipRegion(ClipRect, ClipPath)
  
  -- * Typography as Geometry (v2 commands)
  , GlyphPathParams
  , glyphPathParams
  , ContourData
  , BoundingBox3D
  , GlyphInstanceParams
  , glyphInstanceParams
  , Rotation3D
  , Scale3D
  , SpringState
  , WordParams
  , wordParams
  , StaggerConfig
  , StaggerDirection
  , EasingFunction
  , PathDataParams
  , pathDataParams
  , AnimationStateParams
  , animationStateParams
  , AnimationUpdateMode(AnimationReplace, AnimationAdditive, AnimationBlend)
  , AnimationTarget
  , TargetType(TargetGlyphInstance, TargetWord, TargetPathData, TargetControlPoint)
  , ColorDelta
  
  -- * Command Constructors
  , drawRect
  , drawQuad
  , drawGlyph
  , drawPath
  , drawParticle
  , pushClip
  , popClip
  , noop
  -- v2 constructors
  , drawGlyphPath
  , drawGlyphInstance
  , drawWord
  , definePathData
  , updateAnimationState
  
  -- * CommandBuffer Operations
  , emptyBuffer
  , singleton
  , append
  , concat
  , withPickId
  
  -- * Sorting & Batching (for interpreter)
  , sortByDepth
  , batchByMaterial
  , compareDepth
  , validateBuffer

  -- * Backward-Compatible Constructors
  , staggerLeftToRight
  , staggerRightToLeft
  , staggerCenterOut
  , staggerEdgesIn
  , staggerTopToBottom
  , staggerBottomToTop
  , staggerRandom
  , easeLinear
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  , easeInBounce
  , easeOutBounce
  , easeSpring
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , Unit
  , compare
  , map
  , show
  , unit
  , (<>)
  , (==)
  )

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(Nothing, Just))
import Data.Ord (comparing)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Animation.Types as AnimTypes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for pick buffer hit testing.
-- | When an interaction occurs, the pick buffer pixel value maps back to this ID.
-- | The interpreter maintains a Map PickId msg for dispatching.
newtype PickId = PickId Int

derive instance eqPickId :: Eq PickId
derive instance ordPickId :: Ord PickId

instance showPickId :: Show PickId where
  show (PickId n) = "PickId(" <> show n <> ")"

-- | Create a PickId from an Int.
pickId :: Int -> PickId
pickId = PickId

-- | Unwrap a PickId to its Int value.
unwrapPickId :: PickId -> Int
unwrapPickId (PickId n) = n

-- | A draw command — single GPU primitive operation.
-- |
-- | The `msg` type parameter carries the message to dispatch when this
-- | element is interacted with (via pick buffer).
-- |
-- | ## Command Categories
-- |
-- | **v1 Primitives (0x00-0x11):**
-- | - DrawRect, DrawQuad, DrawGlyph (SDF), DrawPath, DrawParticle, Clip ops
-- |
-- | **v2 Typography as Geometry (0x20-0x24):**
-- | - DrawGlyphPath: Character as vector bezier paths
-- | - DrawGlyphInstance: Animated glyph with per-character transform
-- | - DrawWord: Collection of glyphs with shared animation state
-- | - DefinePathData: Shared/deduplicated path data for instancing
-- | - UpdateAnimationState: Per-frame animation deltas
data DrawCommand msg
  = DrawRect (RectParams msg)
  | DrawQuad (QuadParams msg)
  | DrawGlyph (GlyphParams msg)
  | DrawPath (PathParams msg)
  | DrawParticle (ParticleParams msg)
  | PushClip ClipRegion
  | PopClip
  | Noop
  -- v2: Typography as Geometry
  | DrawGlyphPath (GlyphPathParams msg)
  | DrawGlyphInstance (GlyphInstanceParams msg)
  | DrawWord (WordParams msg)
  | DefinePathData PathDataParams
  | UpdateAnimationState AnimationStateParams

-- | A command buffer — array of commands ready for GPU dispatch.
-- | This is the unit of work passed to the interpreter.
type CommandBuffer msg = Array (DrawCommand msg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rect parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a rectangle.
-- |
-- | Rectangles are the most common primitive. Rounded corners are handled
-- | via SDF in the shader — no extra geometry needed.
type RectParams msg =
  { x :: Device.Pixel           -- Left edge
  , y :: Device.Pixel           -- Top edge
  , width :: Device.Pixel       -- Width
  , height :: Device.Pixel      -- Height
  , fill :: RGB.RGBA            -- Fill color with alpha
  , cornerRadius :: Radius.Corners  -- Per-corner radius
  , depth :: Number             -- Z-order (higher = on top)
  , pickId :: Maybe PickId      -- For hit testing (Nothing = not interactive)
  , onClick :: Maybe msg        -- Message on click
  }

-- | Create rectangle parameters with defaults.
rectParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- width
  -> Device.Pixel       -- height
  -> RGB.RGBA           -- fill
  -> RectParams msg
rectParams x y width height fill =
  { x
  , y
  , width
  , height
  , fill
  , cornerRadius: Radius.cornersAll Radius.none
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // quad parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D point for quad vertices.
type Point2D =
  { x :: Device.Pixel
  , y :: Device.Pixel
  }

-- | A 3D point for typography geometry.
type Point3D =
  { x :: Device.Pixel
  , y :: Device.Pixel
  , z :: Device.Pixel
  }

-- | Parameters for drawing an arbitrary quadrilateral.
-- |
-- | Four vertices in clockwise order. More flexible than rect but
-- | requires 4 points. Used for skewed/transformed shapes.
type QuadParams msg =
  { v0 :: Point2D               -- Top-left
  , v1 :: Point2D               -- Top-right
  , v2 :: Point2D               -- Bottom-right
  , v3 :: Point2D               -- Bottom-left
  , fill :: RGB.RGBA
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create quad parameters.
quadParams
  :: forall msg
   . Point2D -> Point2D -> Point2D -> Point2D
  -> RGB.RGBA
  -> QuadParams msg
quadParams v0 v1 v2 v3 fill =
  { v0, v1, v2, v3
  , fill
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // glyph parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a single glyph using SDF rendering.
-- |
-- | Text is rendered as a sequence of glyph quads. Each glyph references
-- | a position in the font atlas and has its own transform.
-- |
-- | The font atlas and SDF textures are managed by the interpreter.
type GlyphParams msg =
  { x :: Device.Pixel           -- Glyph origin X
  , y :: Device.Pixel           -- Glyph origin Y (baseline)
  , glyphIndex :: Int           -- Index into font atlas
  , fontId :: Int               -- Which font (interpreter manages font registry)
  , fontSize :: Device.Pixel    -- Rendered size
  , color :: RGB.RGBA           -- Text color
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create glyph parameters.
glyphParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Int                -- glyphIndex
  -> Int                -- fontId
  -> Device.Pixel       -- fontSize
  -> RGB.RGBA           -- color
  -> GlyphParams msg
glyphParams x y glyphIndex fontId fontSize color =
  { x, y, glyphIndex, fontId, fontSize, color
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Path segment types for vector graphics.
data PathSegment
  = MoveTo Point2D
  | LineTo Point2D
  | QuadraticTo Point2D Point2D           -- control, end
  | CubicTo Point2D Point2D Point2D       -- c1, c2, end
  | ClosePath

derive instance eqPathSegment :: Eq PathSegment

-- | Parameters for drawing a vector path.
-- |
-- | Paths are tessellated to triangles by the interpreter. Complex paths
-- | may have significant vertex counts.
type PathParams msg =
  { segments :: Array PathSegment
  , fill :: Maybe RGB.RGBA      -- Fill color (Nothing = no fill)
  , stroke :: Maybe RGB.RGBA    -- Stroke color (Nothing = no stroke)
  , strokeWidth :: Device.Pixel
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create path parameters.
pathParams
  :: forall msg
   . Array PathSegment
  -> PathParams msg
pathParams segments =
  { segments
  , fill: Nothing
  , stroke: Nothing
  , strokeWidth: Device.px 1.0
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // particle parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a particle.
-- |
-- | Particles are instanced — the GPU draws thousands with a single call.
-- | This is the primitive for billion-agent visualization.
-- |
-- | Each particle is a point sprite rendered as a quad facing the camera.
type ParticleParams msg =
  { x :: Device.Pixel
  , y :: Device.Pixel
  , z :: Number                 -- Depth (for 3D particle fields)
  , size :: Device.Pixel        -- Point size
  , color :: RGB.RGBA
  , pickId :: Maybe PickId      -- Can make individual particles interactive
  , onClick :: Maybe msg
  }

-- | Create particle parameters.
particleParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- size
  -> RGB.RGBA           -- color
  -> ParticleParams msg
particleParams x y size color =
  { x, y
  , z: 0.0
  , size
  , color
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // clip operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clip region for masking.
-- |
-- | Push a clip, draw commands, pop the clip. Uses stencil buffer.
data ClipRegion
  = ClipRect
      { x :: Device.Pixel
      , y :: Device.Pixel
      , width :: Device.Pixel
      , height :: Device.Pixel
      , cornerRadius :: Radius.Corners
      }
  | ClipPath (Array PathSegment)

derive instance eqClipRegion :: Eq ClipRegion

-- ═════════════════════════════════════════════════════════════════════════════
--                                       // v2 typography as geometry parameters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opcode 0x20: GlyphPathParams — Single character as vector bezier paths.
-- |
-- | This is the core typography-as-geometry primitive. Each glyph is a collection
-- | of bezier contours (outer paths and counter paths for holes like in 'O', 'A').
-- | The same tessellation pipeline handles glyphs and all other vector shapes.
-- |
-- | ## Wire Format (variable length)
-- | - glyphId: u32 (Unicode codepoint or internal glyph ID)
-- | - fontId: u16 (font registry index)
-- | - contourCount: u16 (number of contours)
-- | - [contours]: per-contour command arrays
-- | - boundingBox: 6 × f32 (minX, minY, minZ, maxX, maxY, maxZ)
-- | - advanceWidth: f32 (horizontal advance after glyph)
type GlyphPathParams msg =
  { glyphId :: Int              -- Unicode codepoint or internal glyph index
  , fontId :: Int               -- Font registry index
  , contours :: Array ContourData  -- Path data for each contour
  , bounds :: BoundingBox3D     -- 3D bounding box
  , advanceWidth :: Device.Pixel   -- Horizontal advance
  , depth :: Number             -- Z-order
  , pickId :: Maybe PickId      -- For hit testing
  , onClick :: Maybe msg        -- Message on click
  }

-- | Contour data for glyph paths.
-- |
-- | Each contour is a closed path. Outer contours are clockwise,
-- | counter/hole contours are counter-clockwise (winding rule).
type ContourData =
  { commands :: Array PathSegment   -- Bezier commands
  , isOuter :: Boolean              -- true = outer, false = hole
  }

-- | 3D bounding box for glyph geometry.
type BoundingBox3D =
  { minX :: Device.Pixel
  , minY :: Device.Pixel
  , minZ :: Device.Pixel
  , maxX :: Device.Pixel
  , maxY :: Device.Pixel
  , maxZ :: Device.Pixel
  }

-- | Create glyph path parameters with defaults.
glyphPathParams
  :: forall msg
   . Int                    -- glyphId
  -> Int                    -- fontId
  -> Array ContourData      -- contours
  -> Device.Pixel           -- advanceWidth
  -> GlyphPathParams msg
glyphPathParams gId fId contours advance =
  { glyphId: gId
  , fontId: fId
  , contours
  , bounds: defaultBounds
  , advanceWidth: advance
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }
  where
    defaultBounds =
      { minX: Device.px 0.0, minY: Device.px 0.0, minZ: Device.px 0.0
      , maxX: Device.px 0.0, maxY: Device.px 0.0, maxZ: Device.px 0.0
      }

-- | Opcode 0x21: GlyphInstanceParams — Animated glyph with per-character transform.
-- |
-- | References a GlyphPath by ID and adds per-instance animation state.
-- | This enables instanced rendering where the same glyph geometry is shared
-- | across multiple characters (e.g., all 'e' letters share one GlyphPath).
-- |
-- | ## Wire Format (52 bytes fixed)
-- | - pathDataId: u32 (reference to DefinePathData)
-- | - transform: 9 × f32 (3×3 matrix: position, rotation, scale)
-- | - color: 4 × u8 (RGBA)
-- | - animationPhase: f32 (0.0-1.0 normalized time)
-- | - springState: 3 × f32 (velocity, displacement, tension)
type GlyphInstanceParams msg =
  { pathDataId :: Int           -- Reference to shared path data
  , position :: Point3D         -- Position in 3D space
  , rotation :: Rotation3D      -- Euler rotation (degrees)
  , scale :: Scale3D            -- Non-uniform scale
  , color :: RGB.RGBA           -- Fill color
  , animationPhase :: Number    -- 0.0-1.0 normalized time
  , spring :: SpringState       -- Spring physics state
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | 3D rotation in degrees (Euler angles).
type Rotation3D =
  { x :: Number   -- Pitch
  , y :: Number   -- Yaw
  , z :: Number   -- Roll
  }

-- | Non-uniform 3D scale.
type Scale3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Spring physics state for animations.
-- |
-- | Springs provide organic motion with velocity, displacement, and tension.
-- | The runtime evaluates spring differential equations at 60fps.
-- |
-- | Hooke's Law: F = -tension * displacement - damping * velocity
-- | Acceleration: a = F / mass
-- | Without damping, springs oscillate forever. Without mass, frequency is undefined.
type SpringState =
  { velocity :: Number      -- Current velocity (can be negative)
  , displacement :: Number  -- Offset from rest position (can be negative)
  , tension :: Number       -- Spring stiffness (0.0-1.0, maps to k constant)
  , damping :: Number       -- Friction coefficient (0.0-1.0, prevents infinite oscillation)
  , mass :: Number          -- Mass (0.1-10.0, affects oscillation period)
  }

-- | Create glyph instance parameters with defaults.
glyphInstanceParams
  :: forall msg
   . Int          -- pathDataId
  -> Point3D      -- position
  -> RGB.RGBA     -- color
  -> GlyphInstanceParams msg
glyphInstanceParams pathId pos color =
  { pathDataId: pathId
  , position: pos
  , rotation: { x: 0.0, y: 0.0, z: 0.0 }
  , scale: { x: 1.0, y: 1.0, z: 1.0 }
  , color
  , animationPhase: 0.0
  , spring: { velocity: 0.0, displacement: 0.0, tension: 0.5, damping: 0.3, mass: 1.0 }
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- | Opcode 0x22: WordParams — Collection of glyphs forming a word.
-- |
-- | Words are the natural unit for stagger animations. A word references
-- | multiple GlyphInstances and carries shared animation state.
-- |
-- | ## Wire Format (variable length)
-- | - wordId: u32 (unique identifier)
-- | - glyphCount: u16 (number of glyphs in word)
-- | - glyphInstanceIds: [u32] (references to GlyphInstance commands)
-- | - staggerPattern: u8 (enum for stagger direction)
-- | - staggerDelay: f32 (ms between characters)
-- | - sharedTransform: 9 × f32 (word-level transform)
type WordParams msg =
  { wordId :: Int                   -- Unique identifier
  , glyphInstances :: Array Int     -- References to GlyphInstance pathDataIds
  , positions :: Array Point3D      -- Per-glyph positions relative to word origin
  , origin :: Point3D               -- Word origin in 3D space
  , stagger :: StaggerConfig        -- Stagger animation config
  , color :: RGB.RGBA               -- Shared color (can be overridden per-glyph)
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Stagger animation configuration.
type StaggerConfig =
  { direction :: StaggerDirection   -- Direction pattern
  , delayMs :: Number               -- Milliseconds between elements
  , easing :: EasingFunction        -- Easing curve
  }

-- | Stagger direction patterns.
-- |
-- | Re-exported from Hydrogen.Animation.Types for backward compatibility.
-- | New code should import from Animation.Types directly.
-- |
-- | Variants:
-- | - StaggerLeftToRight, StaggerRightToLeft
-- | - StaggerCenterOut, StaggerEdgesIn
-- | - StaggerTopToBottom, StaggerBottomToTop
-- | - StaggerRandom Int (seed for determinism)
type StaggerDirection = AnimTypes.StaggerDirection

-- | Re-exported StaggerDirection constructors for backward compatibility.
-- | Consumers can use: DC.StaggerLeftToRight, DC.StaggerRightToLeft, etc.
staggerLeftToRight :: StaggerDirection
staggerLeftToRight = AnimTypes.StaggerLeftToRight

staggerRightToLeft :: StaggerDirection
staggerRightToLeft = AnimTypes.StaggerRightToLeft

staggerCenterOut :: StaggerDirection
staggerCenterOut = AnimTypes.StaggerCenterOut

staggerEdgesIn :: StaggerDirection
staggerEdgesIn = AnimTypes.StaggerEdgesIn

staggerTopToBottom :: StaggerDirection
staggerTopToBottom = AnimTypes.StaggerTopToBottom

staggerBottomToTop :: StaggerDirection
staggerBottomToTop = AnimTypes.StaggerBottomToTop

staggerRandom :: Int -> StaggerDirection
staggerRandom = AnimTypes.StaggerRandom

-- | Easing function enumeration.
-- |
-- | Re-exported from Hydrogen.Animation.Types for backward compatibility.
-- | This is a type alias to EasingId, the wire-format subset.
-- | New code should import EasingId from Animation.Types directly.
type EasingFunction = AnimTypes.EasingId

-- | Re-exported EasingFunction constructors for backward compatibility.
-- | Consumers can use: DC.EasingIdLinear, DC.EasingIdInQuad, etc.
easingIdLinear :: EasingFunction
easingIdLinear = AnimTypes.EasingIdLinear

easingIdInQuad :: EasingFunction
easingIdInQuad = AnimTypes.EasingIdInQuad

easingIdOutQuad :: EasingFunction
easingIdOutQuad = AnimTypes.EasingIdOutQuad

easingIdInOutQuad :: EasingFunction
easingIdInOutQuad = AnimTypes.EasingIdInOutQuad

easingIdInCubic :: EasingFunction
easingIdInCubic = AnimTypes.EasingIdInCubic

easingIdOutCubic :: EasingFunction
easingIdOutCubic = AnimTypes.EasingIdOutCubic

easingIdInOutCubic :: EasingFunction
easingIdInOutCubic = AnimTypes.EasingIdInOutCubic

easingIdInElastic :: EasingFunction
easingIdInElastic = AnimTypes.EasingIdInElastic

easingIdOutElastic :: EasingFunction
easingIdOutElastic = AnimTypes.EasingIdOutElastic

easingIdInOutElastic :: EasingFunction
easingIdInOutElastic = AnimTypes.EasingIdInOutElastic

easingIdInBounce :: EasingFunction
easingIdInBounce = AnimTypes.EasingIdInBounce

easingIdOutBounce :: EasingFunction
easingIdOutBounce = AnimTypes.EasingIdOutBounce

easingIdSpring :: EasingFunction
easingIdSpring = AnimTypes.EasingIdSpring

-- | Backward compatible aliases (old Ease* names)
easeLinear :: EasingFunction
easeLinear = easingIdLinear

easeInQuad :: EasingFunction
easeInQuad = easingIdInQuad

easeOutQuad :: EasingFunction
easeOutQuad = easingIdOutQuad

easeInOutQuad :: EasingFunction
easeInOutQuad = easingIdInOutQuad

easeInCubic :: EasingFunction
easeInCubic = easingIdInCubic

easeOutCubic :: EasingFunction
easeOutCubic = easingIdOutCubic

easeInOutCubic :: EasingFunction
easeInOutCubic = easingIdInOutCubic

easeInElastic :: EasingFunction
easeInElastic = easingIdInElastic

easeOutElastic :: EasingFunction
easeOutElastic = easingIdOutElastic

easeInOutElastic :: EasingFunction
easeInOutElastic = easingIdInOutElastic

easeInBounce :: EasingFunction
easeInBounce = easingIdInBounce

easeOutBounce :: EasingFunction
easeOutBounce = easingIdOutBounce

easeSpring :: EasingFunction
easeSpring = easingIdSpring

-- | Create word parameters with defaults.
wordParams
  :: forall msg
   . Int                -- wordId
  -> Array Int          -- glyphInstances
  -> Array Point3D      -- positions
  -> Point3D            -- origin
  -> WordParams msg
wordParams wId glyphs positions origin =
  { wordId: wId
  , glyphInstances: glyphs
  , positions
  , origin
  , stagger: 
      { direction: staggerLeftToRight
      , delayMs: 50.0
      , easing: easeOutCubic
      }
  , color: RGB.rgba 255 255 255 255
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- | Opcode 0x23: PathDataParams — Shared/deduplicated path data for instancing.
-- |
-- | Define path data once, reference many times. This is how fonts work:
-- | the letter 'e' appears many times in text but its geometry is stored once.
-- |
-- | ## Wire Format (variable length)
-- | - pathDataId: u32 (unique identifier for referencing)
-- | - commandCount: u32 (number of path commands)
-- | - [commands]: serialized PathSegment array
-- | - bounds: 6 × f32 (bounding box)
type PathDataParams =
  { pathDataId :: Int           -- Unique identifier
  , commands :: Array PathSegment  -- The actual path data
  , bounds :: BoundingBox3D     -- Precomputed bounds
  }

-- | Create path data parameters.
pathDataParams
  :: Int                    -- pathDataId
  -> Array PathSegment      -- commands
  -> PathDataParams
pathDataParams pId commands =
  { pathDataId: pId
  , commands
  , bounds:
      { minX: Device.px 0.0, minY: Device.px 0.0, minZ: Device.px 0.0
      , maxX: Device.px 0.0, maxY: Device.px 0.0, maxZ: Device.px 0.0
      }
  }

-- | Opcode 0x24: AnimationStateParams — Per-frame animation deltas.
-- |
-- | Instead of recomputing all transforms every frame, send deltas.
-- | The runtime accumulates state efficiently.
-- |
-- | ## Wire Format (variable length)
-- | - targetCount: u16 (number of targets)
-- | - [targets]: array of AnimationTarget
type AnimationStateParams =
  { targets :: Array AnimationTarget  -- What to animate this frame
  , mode :: AnimationUpdateMode       -- How to apply
  , frameTime :: Number               -- Delta time in ms
  }

-- | Individual animation target.
type AnimationTarget =
  { targetId :: Int           -- Which element to animate
  , targetType :: TargetType  -- What kind of element
  , deltaPosition :: Point3D  -- Position delta
  , deltaRotation :: Rotation3D  -- Rotation delta
  , deltaScale :: Scale3D     -- Scale delta
  , deltaColor :: ColorDelta  -- Color change
  , phaseAdvance :: Number    -- Animation phase advancement
  }

-- | Target type for animation routing.
data TargetType
  = TargetGlyphInstance
  | TargetWord
  | TargetPathData
  | TargetControlPoint

derive instance eqTargetType :: Eq TargetType

instance showTargetType :: Show TargetType where
  show TargetGlyphInstance = "TargetGlyphInstance"
  show TargetWord = "TargetWord"
  show TargetPathData = "TargetPathData"
  show TargetControlPoint = "TargetControlPoint"

-- | Color delta for animation (additive).
type ColorDelta =
  { r :: Int   -- -255 to 255
  , g :: Int
  , b :: Int
  , a :: Int
  }

-- | How animation updates are applied.
data AnimationUpdateMode
  = AnimationReplace    -- Replace current state
  | AnimationAdditive   -- Add to current state
  | AnimationBlend Number  -- Blend with factor (0.0-1.0)

derive instance eqAnimationUpdateMode :: Eq AnimationUpdateMode

instance showAnimationUpdateMode :: Show AnimationUpdateMode where
  show AnimationReplace = "AnimationReplace"
  show AnimationAdditive = "AnimationAdditive"
  show (AnimationBlend factor) = "AnimationBlend(" <> show factor <> ")"

-- | Create animation state parameters with defaults.
animationStateParams
  :: Array AnimationTarget
  -> AnimationStateParams
animationStateParams targets =
  { targets
  , mode: AnimationAdditive
  , frameTime: 16.666  -- 60fps default
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // command constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Draw a rectangle.
drawRect :: forall msg. RectParams msg -> DrawCommand msg
drawRect = DrawRect

-- | Draw a quadrilateral.
drawQuad :: forall msg. QuadParams msg -> DrawCommand msg
drawQuad = DrawQuad

-- | Draw a text glyph.
drawGlyph :: forall msg. GlyphParams msg -> DrawCommand msg
drawGlyph = DrawGlyph

-- | Draw a vector path.
drawPath :: forall msg. PathParams msg -> DrawCommand msg
drawPath = DrawPath

-- | Draw a particle.
drawParticle :: forall msg. ParticleParams msg -> DrawCommand msg
drawParticle = DrawParticle

-- | Push a clipping region onto the clip stack.
pushClip :: forall msg. ClipRegion -> DrawCommand msg
pushClip = PushClip

-- | Pop the current clipping region.
popClip :: forall msg. DrawCommand msg
popClip = PopClip

-- | No operation. Useful as identity element.
noop :: forall msg. DrawCommand msg
noop = Noop

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                    // v2 command constructors
-- ─────────────────────────────────────────────────────────────────────────────────

-- | Draw a glyph as vector bezier paths (typography as geometry).
drawGlyphPath :: forall msg. GlyphPathParams msg -> DrawCommand msg
drawGlyphPath = DrawGlyphPath

-- | Draw an animated glyph instance referencing shared path data.
drawGlyphInstance :: forall msg. GlyphInstanceParams msg -> DrawCommand msg
drawGlyphInstance = DrawGlyphInstance

-- | Draw a word (collection of glyphs with shared animation state).
drawWord :: forall msg. WordParams msg -> DrawCommand msg
drawWord = DrawWord

-- | Define shared path data for instancing.
definePathData :: forall msg. PathDataParams -> DrawCommand msg
definePathData = DefinePathData

-- | Update animation state for targets.
updateAnimationState :: forall msg. AnimationStateParams -> DrawCommand msg
updateAnimationState = UpdateAnimationState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // command buffer ops
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty command buffer.
emptyBuffer :: forall msg. CommandBuffer msg
emptyBuffer = []

-- | Single-command buffer.
singleton :: forall msg. DrawCommand msg -> CommandBuffer msg
singleton cmd = [cmd]

-- | Append a command to a buffer.
append :: forall msg. DrawCommand msg -> CommandBuffer msg -> CommandBuffer msg
append cmd buf = Array.snoc buf cmd

-- | Concatenate command buffers.
concat :: forall msg. Array (CommandBuffer msg) -> CommandBuffer msg
concat = Array.concat

-- | Add a pick ID to a command for hit testing.
withPickId :: forall msg. PickId -> DrawCommand msg -> DrawCommand msg
withPickId pid cmd = case cmd of
  DrawRect p -> DrawRect (p { pickId = Just pid })
  DrawQuad p -> DrawQuad (p { pickId = Just pid })
  DrawGlyph p -> DrawGlyph (p { pickId = Just pid })
  DrawPath p -> DrawPath (p { pickId = Just pid })
  DrawParticle p -> DrawParticle (p { pickId = Just pid })
  -- v2 typography commands
  DrawGlyphPath p -> DrawGlyphPath (p { pickId = Just pid })
  DrawGlyphInstance p -> DrawGlyphInstance (p { pickId = Just pid })
  DrawWord p -> DrawWord (p { pickId = Just pid })
  -- Non-interactive commands pass through unchanged
  DefinePathData pd -> DefinePathData pd
  UpdateAnimationState as -> UpdateAnimationState as
  PushClip c -> PushClip c
  PopClip -> PopClip
  Noop -> Noop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // sorting and batching
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract depth from a command for sorting.
getDepth :: forall msg. DrawCommand msg -> Number
getDepth = case _ of
  DrawRect p -> p.depth
  DrawQuad p -> p.depth
  DrawGlyph p -> p.depth
  DrawPath p -> p.depth
  DrawParticle p -> p.z
  PushClip _ -> 0.0
  PopClip -> 0.0
  Noop -> 0.0
  -- v2 typography commands
  DrawGlyphPath p -> p.depth
  DrawGlyphInstance p -> p.depth
  DrawWord p -> p.depth
  DefinePathData _ -> 0.0      -- Definition command, no depth
  UpdateAnimationState _ -> 0.0  -- Update command, no depth

-- | Sort commands by depth (painter's algorithm for 2D).
-- |
-- | Lower depth draws first (is behind). For WebGPU with depth buffer,
-- | sorting is optional but helps reduce overdraw.
sortByDepth :: forall msg. CommandBuffer msg -> CommandBuffer msg
sortByDepth = Array.sortBy (comparing getDepth)

-- | Material key for batching.
-- |
-- | Commands with the same material can be drawn together.
-- | Currently simplified — real batching would consider texture atlas pages,
-- | blend modes, etc.
data MaterialKey
  = MaterialSolid
  | MaterialTextured Int  -- texture/atlas ID
  | MaterialClip
  | MaterialTypography Int  -- fontId for v2 typography geometry
  | MaterialMeta           -- Non-rendering commands (define, update)

derive instance eqMaterialKey :: Eq MaterialKey
derive instance ordMaterialKey :: Ord MaterialKey

-- | Get material key from command.
getMaterial :: forall msg. DrawCommand msg -> MaterialKey
getMaterial = case _ of
  DrawRect _ -> MaterialSolid
  DrawQuad _ -> MaterialSolid
  DrawGlyph p -> MaterialTextured p.fontId
  DrawPath _ -> MaterialSolid
  DrawParticle _ -> MaterialSolid
  PushClip _ -> MaterialClip
  PopClip -> MaterialClip
  Noop -> MaterialSolid
  -- v2 typography commands
  DrawGlyphPath p -> MaterialTypography p.fontId
  DrawGlyphInstance _ -> MaterialSolid  -- Instanced, batches with solids
  DrawWord _ -> MaterialSolid           -- Composed of instances
  DefinePathData _ -> MaterialMeta      -- Non-rendering
  UpdateAnimationState _ -> MaterialMeta  -- Non-rendering

-- | Group commands by material for batched rendering.
-- |
-- | Returns array of batches, each batch can be drawn with a single
-- | state change. Order within batches preserves original depth order.
batchByMaterial :: forall msg. CommandBuffer msg -> Array (CommandBuffer msg)
batchByMaterial buf =
  let sorted = sortByDepth buf
      grouped = Array.groupBy (\a b -> getMaterial a == getMaterial b) sorted
  in map NEA.toArray grouped

-- | Compare two commands by their depth values.
-- |
-- | Returns Ordering (LT, EQ, GT) based on depth comparison.
-- | Useful for custom sorting strategies or priority queues.
compareDepth :: forall msg. DrawCommand msg -> DrawCommand msg -> Ordering
compareDepth a b = compare (getDepth a) (getDepth b)

-- | Validate a command buffer, returning Unit.
-- |
-- | Currently performs no-op validation (all buffers are valid by construction
-- | due to the type system). This function exists for:
-- | 1. Future invariant checking (e.g., clip push/pop balance)
-- | 2. Integration with effect pipelines that expect Unit
-- | 3. Explicit documentation that validation was considered
validateBuffer :: forall msg. CommandBuffer msg -> Unit
validateBuffer _buf = unit
