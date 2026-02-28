-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // gpu // scene3d // gizmo // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gizmo Geometry — Visual representation of transform handles.
-- |
-- | ## Design
-- | Generates the 3D geometry for translate/rotate/scale gizmos.
-- | Each axis is a separate piece for independent hit testing.
-- |
-- | ## Color Convention (Three.js/Blender standard)
-- | - X axis: Red   (RGB 1, 0, 0)
-- | - Y axis: Green (RGB 0, 1, 0)
-- | - Z axis: Blue  (RGB 0, 0, 1)
-- |
-- | ## Geometry Types
-- | - Translate: Arrow (cone + cylinder) per axis, plane squares
-- | - Rotate: Torus ring per axis
-- | - Scale: Cube handle per axis, center cube for uniform

module Hydrogen.GPU.Scene3D.GizmoGeometry
  ( -- * Gizmo Part Identifier
    GizmoPart
      ( TranslateArrowX
      , TranslateArrowY
      , TranslateArrowZ
      , TranslatePlaneXY
      , TranslatePlaneXZ
      , TranslatePlaneYZ
      , RotateRingX
      , RotateRingY
      , RotateRingZ
      , ScaleHandleX
      , ScaleHandleY
      , ScaleHandleZ
      , ScaleHandleCenter
      )
  
  -- * Hit Test Geometry
  , GizmoHitBox
  , translateGizmoHitBoxes
  , rotateGizmoHitBoxes
  , scaleGizmoHitBoxes
  
  -- * Axis to Part Conversion
  , axisToTranslatePart
  , axisToRotatePart
  , axisToScalePart
  , partToAxis
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Gizmo (GizmoAxis(AxisX, AxisY, AxisZ, PlaneXY, PlaneXZ, PlaneYZ, AxisAll, AxisNone))
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // gizmo part
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identifier for individual gizmo geometry pieces.
-- |
-- | Each piece can be hit-tested independently to determine which
-- | axis the user is interacting with.
data GizmoPart
  -- Translate gizmo parts
  = TranslateArrowX       -- Arrow along +X
  | TranslateArrowY       -- Arrow along +Y
  | TranslateArrowZ       -- Arrow along +Z
  | TranslatePlaneXY      -- Square in XY plane (for XY movement)
  | TranslatePlaneXZ      -- Square in XZ plane
  | TranslatePlaneYZ      -- Square in YZ plane
  -- Rotate gizmo parts
  | RotateRingX           -- Ring around X axis (rotates YZ)
  | RotateRingY           -- Ring around Y axis (rotates XZ)
  | RotateRingZ           -- Ring around Z axis (rotates XY)
  -- Scale gizmo parts
  | ScaleHandleX          -- Cube handle on +X
  | ScaleHandleY          -- Cube handle on +Y
  | ScaleHandleZ          -- Cube handle on +Z
  | ScaleHandleCenter     -- Center cube for uniform scale

derive instance eqGizmoPart :: Eq GizmoPart

instance showGizmoPart :: Show GizmoPart where
  show TranslateArrowX = "TranslateArrowX"
  show TranslateArrowY = "TranslateArrowY"
  show TranslateArrowZ = "TranslateArrowZ"
  show TranslatePlaneXY = "TranslatePlaneXY"
  show TranslatePlaneXZ = "TranslatePlaneXZ"
  show TranslatePlaneYZ = "TranslatePlaneYZ"
  show RotateRingX = "RotateRingX"
  show RotateRingY = "RotateRingY"
  show RotateRingZ = "RotateRingZ"
  show ScaleHandleX = "ScaleHandleX"
  show ScaleHandleY = "ScaleHandleY"
  show ScaleHandleZ = "ScaleHandleZ"
  show ScaleHandleCenter = "ScaleHandleCenter"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // axis mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert GizmoAxis to the corresponding translate gizmo part.
axisToTranslatePart :: GizmoAxis -> Maybe GizmoPart
axisToTranslatePart AxisX = Just TranslateArrowX
axisToTranslatePart AxisY = Just TranslateArrowY
axisToTranslatePart AxisZ = Just TranslateArrowZ
axisToTranslatePart PlaneXY = Just TranslatePlaneXY
axisToTranslatePart PlaneXZ = Just TranslatePlaneXZ
axisToTranslatePart PlaneYZ = Just TranslatePlaneYZ
axisToTranslatePart AxisAll = Nothing  -- Translate has no "all" handle
axisToTranslatePart AxisNone = Nothing

-- | Convert GizmoAxis to the corresponding rotate gizmo part.
axisToRotatePart :: GizmoAxis -> Maybe GizmoPart
axisToRotatePart AxisX = Just RotateRingX
axisToRotatePart AxisY = Just RotateRingY
axisToRotatePart AxisZ = Just RotateRingZ
axisToRotatePart _ = Nothing  -- Planes don't apply to rotation

-- | Convert GizmoAxis to the corresponding scale gizmo part.
axisToScalePart :: GizmoAxis -> Maybe GizmoPart
axisToScalePart AxisX = Just ScaleHandleX
axisToScalePart AxisY = Just ScaleHandleY
axisToScalePart AxisZ = Just ScaleHandleZ
axisToScalePart AxisAll = Just ScaleHandleCenter
axisToScalePart _ = Nothing  -- Planes don't apply to scale

-- | Convert a gizmo part back to its corresponding axis.
partToAxis :: GizmoPart -> GizmoAxis
partToAxis TranslateArrowX = AxisX
partToAxis TranslateArrowY = AxisY
partToAxis TranslateArrowZ = AxisZ
partToAxis TranslatePlaneXY = PlaneXY
partToAxis TranslatePlaneXZ = PlaneXZ
partToAxis TranslatePlaneYZ = PlaneYZ
partToAxis RotateRingX = AxisX
partToAxis RotateRingY = AxisY
partToAxis RotateRingZ = AxisZ
partToAxis ScaleHandleX = AxisX
partToAxis ScaleHandleY = AxisY
partToAxis ScaleHandleZ = AxisZ
partToAxis ScaleHandleCenter = AxisAll

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // hit test boxes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned bounding box for gizmo hit testing.
-- |
-- | Simple AABB representation used for quick ray intersection
-- | before more precise geometry tests.
type GizmoHitBox =
  { part :: GizmoPart
  , min :: Vec3 Number
  , max :: Vec3 Number
  }

-- | Gizmo size constants (in gizmo-local units).
-- | These are scaled by gizmoScale in the state for screen-space sizing.
arrowLength :: Number
arrowLength = 1.0

arrowRadius :: Number
arrowRadius = 0.05

planeSize :: Number
planeSize = 0.3

planeOffset :: Number
planeOffset = 0.4

handleSize :: Number
handleSize = 0.1

ringRadius :: Number
ringRadius = 1.0

ringTube :: Number
ringTube = 0.03

-- | Hit boxes for translate gizmo arrows and planes.
-- |
-- | Returns array of AABBs positioned at origin.
-- | Apply gizmo position/scale transform before hit testing.
translateGizmoHitBoxes :: Array GizmoHitBox
translateGizmoHitBoxes =
  [ -- X arrow: extends along +X
    { part: TranslateArrowX
    , min: vec3 0.0 (negate arrowRadius) (negate arrowRadius)
    , max: vec3 arrowLength arrowRadius arrowRadius
    }
  -- Y arrow: extends along +Y
  , { part: TranslateArrowY
    , min: vec3 (negate arrowRadius) 0.0 (negate arrowRadius)
    , max: vec3 arrowRadius arrowLength arrowRadius
    }
  -- Z arrow: extends along +Z
  , { part: TranslateArrowZ
    , min: vec3 (negate arrowRadius) (negate arrowRadius) 0.0
    , max: vec3 arrowRadius arrowRadius arrowLength
    }
  -- XY plane: small square offset from origin
  , { part: TranslatePlaneXY
    , min: vec3 planeOffset planeOffset 0.0
    , max: vec3 (planeOffset + planeSize) (planeOffset + planeSize) arrowRadius
    }
  -- XZ plane
  , { part: TranslatePlaneXZ
    , min: vec3 planeOffset 0.0 planeOffset
    , max: vec3 (planeOffset + planeSize) arrowRadius (planeOffset + planeSize)
    }
  -- YZ plane
  , { part: TranslatePlaneYZ
    , min: vec3 0.0 planeOffset planeOffset
    , max: vec3 arrowRadius (planeOffset + planeSize) (planeOffset + planeSize)
    }
  ]

-- | Hit boxes for rotate gizmo rings.
-- |
-- | Rings are approximated as thick torus AABBs for quick rejection.
-- | Precise hit testing would use torus-ray intersection.
rotateGizmoHitBoxes :: Array GizmoHitBox
rotateGizmoHitBoxes =
  [ -- X ring: circle in YZ plane
    { part: RotateRingX
    , min: vec3 (negate ringTube) (negate ringRadius - ringTube) (negate ringRadius - ringTube)
    , max: vec3 ringTube (ringRadius + ringTube) (ringRadius + ringTube)
    }
  -- Y ring: circle in XZ plane
  , { part: RotateRingY
    , min: vec3 (negate ringRadius - ringTube) (negate ringTube) (negate ringRadius - ringTube)
    , max: vec3 (ringRadius + ringTube) ringTube (ringRadius + ringTube)
    }
  -- Z ring: circle in XY plane
  , { part: RotateRingZ
    , min: vec3 (negate ringRadius - ringTube) (negate ringRadius - ringTube) (negate ringTube)
    , max: vec3 (ringRadius + ringTube) (ringRadius + ringTube) ringTube
    }
  ]

-- | Hit boxes for scale gizmo handles.
-- |
-- | Cubes at the end of each axis plus a center cube.
scaleGizmoHitBoxes :: Array GizmoHitBox
scaleGizmoHitBoxes =
  [ -- X handle: cube at end of +X axis
    { part: ScaleHandleX
    , min: vec3 (arrowLength - handleSize) (negate handleSize / 2.0) (negate handleSize / 2.0)
    , max: vec3 arrowLength (handleSize / 2.0) (handleSize / 2.0)
    }
  -- Y handle: cube at end of +Y axis
  , { part: ScaleHandleY
    , min: vec3 (negate handleSize / 2.0) (arrowLength - handleSize) (negate handleSize / 2.0)
    , max: vec3 (handleSize / 2.0) arrowLength (handleSize / 2.0)
    }
  -- Z handle: cube at end of +Z axis
  , { part: ScaleHandleZ
    , min: vec3 (negate handleSize / 2.0) (negate handleSize / 2.0) (arrowLength - handleSize)
    , max: vec3 (handleSize / 2.0) (handleSize / 2.0) arrowLength
    }
  -- Center handle: cube at origin for uniform scale
  , { part: ScaleHandleCenter
    , min: vec3 (negate handleSize) (negate handleSize) (negate handleSize)
    , max: vec3 handleSize handleSize handleSize
    }
  ]
