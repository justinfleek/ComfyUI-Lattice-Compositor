-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // motion // effects // perspective
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Perspective Effects — 3D perspective and depth effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Perspective effect category:
-- |
-- | - **Drop Shadow**: Classic shadow behind layer
-- | - **Bevel Alpha**: Beveled edges using alpha channel
-- | - **Bevel Edges**: Beveled edges on layer bounds
-- | - **3D Glasses**: Stereoscopic 3D view generation
-- | - **CC Cylinder**: Cylindrical 3D wrap
-- | - **CC Sphere**: Spherical 3D wrap
-- | - **CC Environment**: Environment mapping
-- |
-- | ## GPU Rendering
-- |
-- | Perspective effects typically require 3D rendering context
-- | or multi-pass compositing for shadows.
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Perspective
  ( -- * Drop Shadow
    DropShadowEffect
  , defaultDropShadow
  , dropShadowWithOffset
  , dropShadowWithColor
  
  -- * Bevel Alpha
  , BevelAlphaEffect
  , BevelEdgeStyle(..)
  , defaultBevelAlpha
  , bevelAlphaWithDepth
  
  -- * Bevel Edges
  , BevelEdgesEffect
  , defaultBevelEdges
  , bevelEdgesWithDepth
  
  -- * 3D Glasses
  , Glasses3DEffect
  , Glasses3DView(..)
  , ConvergenceMode(..)
  , default3DGlasses
  , glasses3DWithDepth
  
  -- * CC Cylinder
  , CylinderEffect
  , CylinderRenderMode(..)
  , defaultCylinder
  , cylinderWithRotation
  
  -- * CC Sphere
  , SphereEffect
  , SphereRenderMode(..)
  , defaultSphere
  , sphereWithRotation
  
  -- * CC Environment
  , EnvironmentEffect
  , EnvironmentMapType(..)
  , defaultEnvironment
  , environmentWithReflection
  
  -- * Serialization
  , bevelEdgeStyleToString
  , glasses3DViewToString
  , convergenceModeToString
  , cylinderRenderModeToString
  , sphereRenderModeToString
  , environmentMapTypeToString
  
  -- * Effect Names
  , dropShadowEffectName
  , bevelAlphaEffectName
  , bevelEdgesEffectName
  , glasses3DEffectName
  , cylinderEffectName
  , sphereEffectName
  , environmentEffectName
  
  -- * Effect Descriptions
  , describeDropShadow
  , describeBevelAlpha
  , describe3DGlasses
  , describeCylinder
  , describeSphere
  
  -- * Queries
  , isShadowVisible
  , hasBevelLight
  , is3DGlassesAnaglyph
  , isCylinderFull
  , isSphereFull
  , hasEnvironmentReflection
  , hasEnvironmentRefraction
  , isBevelThick
  , isShadowSoft
  , isShadowHard
  , isDropShadowEffective
  , hasBevelFullLighting
  
  -- * Value Clamping
  , clampDropShadowValues
  , clampBevelAlphaValues
  
  -- * Descriptions
  , shadowDirectionToString
  , describeDropShadowFull
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (<)
  , (>)
  , (>=)
  , (&&)
  , (||)
  , negate
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drop // shadow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop Shadow Effect — classic shadow behind layer.
-- |
-- | ## AE Properties
-- |
-- | - Shadow Color: Shadow color (default black)
-- | - Opacity: Shadow opacity (0-100%)
-- | - Direction: Angle of shadow (0-360 degrees)
-- | - Distance: Shadow offset distance (0-1000 pixels)
-- | - Softness: Shadow blur amount (0-1000 pixels)
-- | - Shadow Only: Render only shadow, hide layer
type DropShadowEffect =
  { shadowColor :: RGB           -- ^ Shadow color
  , opacity :: Number            -- ^ Shadow opacity (0-100)
  , direction :: Number          -- ^ Direction angle (0-360)
  , distance :: Number           -- ^ Offset distance (0-1000)
  , softness :: Number           -- ^ Blur softness (0-1000)
  , shadowOnly :: Boolean        -- ^ Render shadow only
  }

-- | Default drop shadow: black, 75% opacity, 135 degrees.
defaultDropShadow :: DropShadowEffect
defaultDropShadow =
  { shadowColor: rgb 0 0 0
  , opacity: 75.0
  , direction: 135.0
  , distance: 5.0
  , softness: 5.0
  , shadowOnly: false
  }

-- | Create drop shadow with specific offset.
dropShadowWithOffset :: Number -> Number -> Number -> DropShadowEffect
dropShadowWithOffset dir dist soft =
  { shadowColor: rgb 0 0 0
  , opacity: 75.0
  , direction: clampNumber 0.0 360.0 dir
  , distance: clampNumber 0.0 1000.0 dist
  , softness: clampNumber 0.0 1000.0 soft
  , shadowOnly: false
  }

-- | Create drop shadow with specific color.
dropShadowWithColor :: RGB -> Number -> DropShadowEffect
dropShadowWithColor col opac =
  { shadowColor: col
  , opacity: clampNumber 0.0 100.0 opac
  , direction: 135.0
  , distance: 5.0
  , softness: 5.0
  , shadowOnly: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bevel // alpha
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bevel edge style — lighting style.
data BevelEdgeStyle
  = BESSmooth          -- ^ Smooth rounded bevel
  | BESChisel          -- ^ Hard chisel bevel
  | BESRound           -- ^ Fully rounded
  | BESFlat            -- ^ Flat with hard edges

derive instance eqBevelEdgeStyle :: Eq BevelEdgeStyle
derive instance ordBevelEdgeStyle :: Ord BevelEdgeStyle

instance showBevelEdgeStyle :: Show BevelEdgeStyle where
  show BESSmooth = "smooth"
  show BESChisel = "chisel"
  show BESRound = "round"
  show BESFlat = "flat"

-- | Bevel Alpha Effect — beveled edges using alpha channel.
-- |
-- | ## AE Properties
-- |
-- | Creates 3D-looking beveled edges based on layer alpha.
type BevelAlphaEffect =
  { edgeThickness :: Number      -- ^ Bevel depth (0-100)
  , lightAngle :: Number         -- ^ Light direction (0-360)
  , lightColor :: RGB            -- ^ Highlight color
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , shadowColor :: RGB           -- ^ Shadow color
  , shadowIntensity :: Number    -- ^ Shadow intensity (0-200)
  , edgeStyle :: BevelEdgeStyle  -- ^ Edge treatment
  }

-- | Default bevel alpha.
defaultBevelAlpha :: BevelAlphaEffect
defaultBevelAlpha =
  { edgeThickness: 5.0
  , lightAngle: 135.0
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  , edgeStyle: BESSmooth
  }

-- | Create bevel alpha with specific depth.
bevelAlphaWithDepth :: Number -> Number -> BevelAlphaEffect
bevelAlphaWithDepth thickness angle =
  { edgeThickness: clampNumber 0.0 100.0 thickness
  , lightAngle: clampNumber 0.0 360.0 angle
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  , edgeStyle: BESSmooth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // bevel // edges
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bevel Edges Effect — beveled edges on layer bounds.
-- |
-- | Similar to Bevel Alpha but uses layer boundaries instead of alpha.
type BevelEdgesEffect =
  { edgeThickness :: Number      -- ^ Bevel depth (0-100)
  , lightAngle :: Number         -- ^ Light direction (0-360)
  , lightColor :: RGB            -- ^ Highlight color
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , shadowColor :: RGB           -- ^ Shadow color
  , shadowIntensity :: Number    -- ^ Shadow intensity (0-200)
  }

-- | Default bevel edges.
defaultBevelEdges :: BevelEdgesEffect
defaultBevelEdges =
  { edgeThickness: 5.0
  , lightAngle: 135.0
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  }

-- | Create bevel edges with specific depth.
bevelEdgesWithDepth :: Number -> Number -> BevelEdgesEffect
bevelEdgesWithDepth thickness angle =
  { edgeThickness: clampNumber 0.0 100.0 thickness
  , lightAngle: clampNumber 0.0 360.0 angle
  , lightColor: rgb 255 255 255
  , lightIntensity: 100.0
  , shadowColor: rgb 0 0 0
  , shadowIntensity: 75.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // glasses
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Glasses view mode — stereoscopic output format.
data Glasses3DView
  = G3DAnaglyph        -- ^ Red/cyan anaglyph
  | G3DInterlaced      -- ^ Row/column interlaced
  | G3DSideBySide      -- ^ Side-by-side stereo
  | G3DOverUnder       -- ^ Over/under stereo
  | G3DBalanced        -- ^ Color-balanced anaglyph
  | G3DRedCyan         -- ^ Red/cyan specific
  | G3DGreenMagenta    -- ^ Green/magenta
  | G3DYellowBlue      -- ^ Yellow/blue

derive instance eqGlasses3DView :: Eq Glasses3DView
derive instance ordGlasses3DView :: Ord Glasses3DView

instance showGlasses3DView :: Show Glasses3DView where
  show G3DAnaglyph = "anaglyph"
  show G3DInterlaced = "interlaced"
  show G3DSideBySide = "side-by-side"
  show G3DOverUnder = "over-under"
  show G3DBalanced = "balanced"
  show G3DRedCyan = "red-cyan"
  show G3DGreenMagenta = "green-magenta"
  show G3DYellowBlue = "yellow-blue"

-- | Convergence mode — how to compute stereo convergence.
data ConvergenceMode
  = CMOffset           -- ^ Fixed offset
  | CMConverge         -- ^ Converge to point
  | CMRotate           -- ^ Rotate views
  | CMPreset           -- ^ Use preset convergence

derive instance eqConvergenceMode :: Eq ConvergenceMode
derive instance ordConvergenceMode :: Ord ConvergenceMode

instance showConvergenceMode :: Show ConvergenceMode where
  show CMOffset = "offset"
  show CMConverge = "converge"
  show CMRotate = "rotate"
  show CMPreset = "preset"

-- | 3D Glasses Effect — stereoscopic view generation.
-- |
-- | ## AE Properties
-- |
-- | Creates stereoscopic 3D from two source views.
type Glasses3DEffect =
  { leftViewLayer :: Int         -- ^ Left eye source layer index
  , rightViewLayer :: Int        -- ^ Right eye source layer index
  , viewMode :: Glasses3DView    -- ^ Output format
  , convergence :: Number        -- ^ Convergence offset (-100 to 100)
  , convergenceMode :: ConvergenceMode
  , balance :: Number            -- ^ Left/right balance (-100 to 100)
  , swapLeftRight :: Boolean     -- ^ Swap eye views
  }

-- | Default 3D glasses.
default3DGlasses :: Glasses3DEffect
default3DGlasses =
  { leftViewLayer: 0
  , rightViewLayer: 0
  , viewMode: G3DAnaglyph
  , convergence: 0.0
  , convergenceMode: CMOffset
  , balance: 0.0
  , swapLeftRight: false
  }

-- | Create 3D glasses with specific depth.
glasses3DWithDepth :: Int -> Int -> Number -> Glasses3DEffect
glasses3DWithDepth leftIdx rightIdx conv =
  { leftViewLayer: leftIdx
  , rightViewLayer: rightIdx
  , viewMode: G3DAnaglyph
  , convergence: clampNumber (-100.0) 100.0 conv
  , convergenceMode: CMOffset
  , balance: 0.0
  , swapLeftRight: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cc // cylinder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cylinder render mode — what to render.
data CylinderRenderMode
  = CRMFull            -- ^ Full cylinder
  | CRMOutside         -- ^ Outside surface only
  | CRMInside          -- ^ Inside surface only

derive instance eqCylinderRenderMode :: Eq CylinderRenderMode
derive instance ordCylinderRenderMode :: Ord CylinderRenderMode

instance showCylinderRenderMode :: Show CylinderRenderMode where
  show CRMFull = "full"
  show CRMOutside = "outside"
  show CRMInside = "inside"

-- | CC Cylinder Effect — wrap layer on 3D cylinder.
-- |
-- | ## AE Properties
-- |
-- | Wraps layer around a cylindrical surface.
type CylinderEffect =
  { renderMode :: CylinderRenderMode
  , rotation :: Vec3 Number      -- ^ X/Y/Z rotation
  , position :: Vec3 Number      -- ^ X/Y/Z position
  , radius :: Number             -- ^ Cylinder radius (0-1000)
  , fov :: Number                -- ^ Field of view (1-180)
  , ambientLight :: Number       -- ^ Ambient lighting (0-100)
  , diffuseReflection :: Number  -- ^ Diffuse reflection (0-100)
  , specularReflection :: Number -- ^ Specular reflection (0-100)
  , specularShininess :: Number  -- ^ Shininess (0-100)
  , lightPosition :: Vec3 Number -- ^ Light position
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , lightColor :: RGB            -- ^ Light color
  }

-- | Default cylinder.
defaultCylinder :: CylinderEffect
defaultCylinder =
  { renderMode: CRMFull
  , rotation: vec3 0.0 0.0 0.0
  , position: vec3 0.0 0.0 0.0
  , radius: 100.0
  , fov: 55.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (-100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- | Create cylinder with specific rotation.
cylinderWithRotation :: Number -> Number -> Number -> CylinderEffect
cylinderWithRotation rx ry rz =
  { renderMode: CRMFull
  , rotation: vec3 (clampNumber (-360.0) 360.0 rx) (clampNumber (-360.0) 360.0 ry) (clampNumber (-360.0) 360.0 rz)
  , position: vec3 0.0 0.0 0.0
  , radius: 100.0
  , fov: 55.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (-100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // cc // sphere
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sphere render mode — what to render.
data SphereRenderMode
  = SRMFull            -- ^ Full sphere
  | SRMOutside         -- ^ Outside surface only
  | SRMInside          -- ^ Inside surface only

derive instance eqSphereRenderMode :: Eq SphereRenderMode
derive instance ordSphereRenderMode :: Ord SphereRenderMode

instance showSphereRenderMode :: Show SphereRenderMode where
  show SRMFull = "full"
  show SRMOutside = "outside"
  show SRMInside = "inside"

-- | CC Sphere Effect — wrap layer on 3D sphere.
-- |
-- | ## AE Properties
-- |
-- | Wraps layer around a spherical surface.
type SphereEffect =
  { renderMode :: SphereRenderMode
  , rotation :: Vec3 Number      -- ^ X/Y/Z rotation
  , radius :: Number             -- ^ Sphere radius (0-1000)
  , offset :: Point2D            -- ^ Texture offset
  , ambientLight :: Number       -- ^ Ambient lighting (0-100)
  , diffuseReflection :: Number  -- ^ Diffuse reflection (0-100)
  , specularReflection :: Number -- ^ Specular reflection (0-100)
  , specularShininess :: Number  -- ^ Shininess (0-100)
  , lightPosition :: Vec3 Number -- ^ Light position
  , lightIntensity :: Number     -- ^ Light intensity (0-200)
  , lightColor :: RGB            -- ^ Light color
  }

-- | Default sphere.
defaultSphere :: SphereEffect
defaultSphere =
  { renderMode: SRMFull
  , rotation: vec3 0.0 0.0 0.0
  , radius: 100.0
  , offset: point2D 0.0 0.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (-100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- | Create sphere with specific rotation.
sphereWithRotation :: Number -> Number -> Number -> SphereEffect
sphereWithRotation rx ry rz =
  { renderMode: SRMFull
  , rotation: vec3 (clampNumber (-360.0) 360.0 rx) (clampNumber (-360.0) 360.0 ry) (clampNumber (-360.0) 360.0 rz)
  , radius: 100.0
  , offset: point2D 0.0 0.0
  , ambientLight: 30.0
  , diffuseReflection: 70.0
  , specularReflection: 30.0
  , specularShininess: 50.0
  , lightPosition: vec3 0.0 0.0 (-100.0)
  , lightIntensity: 100.0
  , lightColor: rgb 255 255 255
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cc // environment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Environment map type — reflection style.
data EnvironmentMapType
  = EMTReflection      -- ^ Standard reflection
  | EMTRefraction      -- ^ Refraction through surface
  | EMTGlass           -- ^ Glass-like (reflection + refraction)
  | EMTMetal           -- ^ Metallic reflection

derive instance eqEnvironmentMapType :: Eq EnvironmentMapType
derive instance ordEnvironmentMapType :: Ord EnvironmentMapType

instance showEnvironmentMapType :: Show EnvironmentMapType where
  show EMTReflection = "reflection"
  show EMTRefraction = "refraction"
  show EMTGlass = "glass"
  show EMTMetal = "metal"

-- | CC Environment Effect — environment/reflection mapping.
-- |
-- | ## AE Properties
-- |
-- | Applies environment map for reflections/refractions.
type EnvironmentEffect =
  { environmentLayer :: Int      -- ^ Source environment layer
  , mapType :: EnvironmentMapType
  , reflectionStrength :: Number -- ^ Reflection amount (0-100)
  , refractionStrength :: Number -- ^ Refraction amount (0-100)
  , blur :: Number               -- ^ Environment blur (0-100)
  , position :: Point2D          -- ^ Map position offset
  , scale :: Number              -- ^ Map scale (0-500)
  , rotation :: Number           -- ^ Map rotation (0-360)
  }

-- | Default environment.
defaultEnvironment :: EnvironmentEffect
defaultEnvironment =
  { environmentLayer: 0
  , mapType: EMTReflection
  , reflectionStrength: 50.0
  , refractionStrength: 0.0
  , blur: 0.0
  , position: point2D 0.0 0.0
  , scale: 100.0
  , rotation: 0.0
  }

-- | Create environment with specific reflection.
environmentWithReflection :: Int -> Number -> EnvironmentEffect
environmentWithReflection layer strength =
  { environmentLayer: layer
  , mapType: EMTReflection
  , reflectionStrength: clampNumber 0.0 100.0 strength
  , refractionStrength: 0.0
  , blur: 0.0
  , position: point2D 0.0 0.0
  , scale: 100.0
  , rotation: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert BevelEdgeStyle to string.
bevelEdgeStyleToString :: BevelEdgeStyle -> String
bevelEdgeStyleToString = show

-- | Convert Glasses3DView to string.
glasses3DViewToString :: Glasses3DView -> String
glasses3DViewToString = show

-- | Convert ConvergenceMode to string.
convergenceModeToString :: ConvergenceMode -> String
convergenceModeToString = show

-- | Convert CylinderRenderMode to string.
cylinderRenderModeToString :: CylinderRenderMode -> String
cylinderRenderModeToString = show

-- | Convert SphereRenderMode to string.
sphereRenderModeToString :: SphereRenderMode -> String
sphereRenderModeToString = show

-- | Convert EnvironmentMapType to string.
environmentMapTypeToString :: EnvironmentMapType -> String
environmentMapTypeToString = show

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Drop Shadow.
dropShadowEffectName :: DropShadowEffect -> String
dropShadowEffectName _ = "Drop Shadow"

-- | Effect name for Bevel Alpha.
bevelAlphaEffectName :: BevelAlphaEffect -> String
bevelAlphaEffectName _ = "Bevel Alpha"

-- | Effect name for Bevel Edges.
bevelEdgesEffectName :: BevelEdgesEffect -> String
bevelEdgesEffectName _ = "Bevel Edges"

-- | Effect name for 3D Glasses.
glasses3DEffectName :: Glasses3DEffect -> String
glasses3DEffectName _ = "3D Glasses"

-- | Effect name for CC Cylinder.
cylinderEffectName :: CylinderEffect -> String
cylinderEffectName _ = "CC Cylinder"

-- | Effect name for CC Sphere.
sphereEffectName :: SphereEffect -> String
sphereEffectName _ = "CC Sphere"

-- | Effect name for CC Environment.
environmentEffectName :: EnvironmentEffect -> String
environmentEffectName _ = "CC Environment"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Describe drop shadow effect.
describeDropShadow :: DropShadowEffect -> String
describeDropShadow e =
  "DropShadow(opacity: " <> show e.opacity <> "%, distance: " <> show e.distance <> "px)"

-- | Describe bevel alpha effect.
describeBevelAlpha :: BevelAlphaEffect -> String
describeBevelAlpha e =
  "BevelAlpha(" <> show e.edgeStyle <> ", depth: " <> show e.edgeThickness <> ")"

-- | Describe 3D glasses effect.
describe3DGlasses :: Glasses3DEffect -> String
describe3DGlasses e =
  "3DGlasses(" <> show e.viewMode <> ", convergence: " <> show e.convergence <> ")"

-- | Describe cylinder effect.
describeCylinder :: CylinderEffect -> String
describeCylinder e =
  "Cylinder(radius: " <> show e.radius <> ", fov: " <> show e.fov <> ")"

-- | Describe sphere effect.
describeSphere :: SphereEffect -> String
describeSphere e =
  "Sphere(radius: " <> show e.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if shadow is visible (opacity > 0).
isShadowVisible :: DropShadowEffect -> Boolean
isShadowVisible e = e.opacity > 0.0

-- | Check if bevel has lighting enabled.
hasBevelLight :: BevelAlphaEffect -> Boolean
hasBevelLight e = e.lightIntensity > 0.0 || e.shadowIntensity > 0.0

-- | Check if 3D glasses uses anaglyph mode.
is3DGlassesAnaglyph :: Glasses3DEffect -> Boolean
is3DGlassesAnaglyph e = case e.viewMode of
  G3DAnaglyph -> true
  G3DRedCyan -> true
  G3DGreenMagenta -> true
  G3DYellowBlue -> true
  G3DBalanced -> true
  _ -> false

-- | Check if cylinder uses full render mode.
isCylinderFull :: CylinderEffect -> Boolean
isCylinderFull e = case e.renderMode of
  CRMFull -> true
  _ -> false

-- | Check if sphere uses full render mode.
isSphereFull :: SphereEffect -> Boolean
isSphereFull e = case e.renderMode of
  SRMFull -> true
  _ -> false

-- | Check if environment has reflection.
hasEnvironmentReflection :: EnvironmentEffect -> Boolean
hasEnvironmentReflection e = e.reflectionStrength > 0.0

-- | Check if environment has refraction.
hasEnvironmentRefraction :: EnvironmentEffect -> Boolean
hasEnvironmentRefraction e = e.refractionStrength > 0.0

-- | Check if bevel edge is thick (>= 10).
isBevelThick :: BevelAlphaEffect -> Boolean
isBevelThick e = e.edgeThickness >= 10.0

-- | Check if shadow is soft (softness > distance).
isShadowSoft :: DropShadowEffect -> Boolean
isShadowSoft e = e.softness > e.distance

-- | Check if shadow is hard (no softness).
isShadowHard :: DropShadowEffect -> Boolean
isShadowHard e = e.softness < 1.0

-- | Check if drop shadow has both visible shadow and non-zero distance.
isDropShadowEffective :: DropShadowEffect -> Boolean
isDropShadowEffective e = e.opacity > 0.0 && e.distance > 0.0

-- | Check if bevel has full lighting (both highlight and shadow).
hasBevelFullLighting :: BevelAlphaEffect -> Boolean
hasBevelFullLighting e = e.lightIntensity > 0.0 && e.shadowIntensity > 0.0

-- | Clamp shadow values to valid ranges.
clampDropShadowValues :: DropShadowEffect -> DropShadowEffect
clampDropShadowValues e =
  { shadowColor: e.shadowColor
  , opacity: clampNumber 0.0 100.0 e.opacity
  , direction: clampNumber 0.0 360.0 e.direction
  , distance: clampNumber 0.0 1000.0 e.distance
  , softness: clampNumber 0.0 1000.0 e.softness
  , shadowOnly: e.shadowOnly
  }

-- | Clamp bevel values to valid ranges.
clampBevelAlphaValues :: BevelAlphaEffect -> BevelAlphaEffect
clampBevelAlphaValues e =
  { edgeThickness: clampNumber 0.0 100.0 e.edgeThickness
  , lightAngle: clampNumber 0.0 360.0 e.lightAngle
  , lightColor: e.lightColor
  , lightIntensity: clampNumber 0.0 200.0 e.lightIntensity
  , shadowColor: e.shadowColor
  , shadowIntensity: clampNumber 0.0 200.0 e.shadowIntensity
  , edgeStyle: e.edgeStyle
  }

-- | Get shadow direction as readable string.
shadowDirectionToString :: DropShadowEffect -> String
shadowDirectionToString e
  | e.direction < 45.0 = "bottom-right"
  | e.direction < 90.0 = "bottom"
  | e.direction < 135.0 = "bottom-left"
  | e.direction < 180.0 = "left"
  | e.direction < 225.0 = "top-left"
  | e.direction < 270.0 = "top"
  | e.direction < 315.0 = "top-right"
  | otherwise = "right"

-- | Create a complete description of a drop shadow effect.
-- | Uses $ for clean function application in complex compositions.
describeDropShadowFull :: DropShadowEffect -> String
describeDropShadowFull e =
  let
    effectiveStr = show $ isDropShadowEffective e
    softStr = show $ isShadowSoft e
  in
    "DropShadow(" 
      <> "color: " <> show e.shadowColor
      <> ", opacity: " <> show e.opacity <> "%"
      <> ", direction: " <> shadowDirectionToString e
      <> " (" <> show e.direction <> "°)"
      <> ", distance: " <> show e.distance <> "px"
      <> ", softness: " <> show e.softness <> "px"
      <> ", shadowOnly: " <> show e.shadowOnly
      <> ", effective: " <> effectiveStr
      <> ", soft: " <> softStr
      <> ")"
