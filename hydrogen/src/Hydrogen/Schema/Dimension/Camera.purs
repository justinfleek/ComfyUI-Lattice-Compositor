-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // dimension // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera and cinematography vocabulary.
-- |
-- | Professional terminology for camera positioning, movement, and optics.
-- | These types describe intent - renderers translate to specific implementations.
-- |
-- | ## Movement Terminology
-- |
-- | - **Dolly**: Move camera forward/backward along view axis
-- | - **Truck**: Move camera left/right perpendicular to view axis
-- | - **Pedestal**: Move camera up/down (crane)
-- | - **Pan**: Rotate camera horizontally (yaw)
-- | - **Tilt**: Rotate camera vertically (pitch)
-- | - **Roll**: Rotate camera around view axis (dutch angle)
-- | - **Zoom**: Change focal length (not physical movement)
-- | - **Rack Focus**: Shift focus plane
-- | - **Orbit**: Rotate camera around a target point
-- | - **Arc**: Curved camera path
-- |
-- | ## Lens/Optics
-- |
-- | - **FOV**: Field of view (vertical or horizontal)
-- | - **Focal Length**: Physical lens property (affects FOV, compression)
-- | - **Aperture**: f-stop, affects depth of field
-- | - **Focus Distance**: Distance to focal plane
-- | - **Sensor Size**: Affects crop factor, depth of field

module Hydrogen.Schema.Dimension.Camera
  ( -- * Camera Pose
    CameraPose
  , cameraPose
  , defaultCameraPose
  
  -- * Camera Movement Types
  , CameraMove
      ( MoveDolly
      , MoveTruck
      , MovePedestal
      , MovePan
      , MoveTilt
      , MoveRoll
      , MoveZoom
      , MoveOrbit
      , MoveArc
      )
  , Dolly(Dolly)
  , Truck(Truck)
  , Pedestal(Pedestal)
  , Pan(Pan)
  , Tilt(Tilt)
  , Roll(Roll)
  , Zoom(Zoom)
  , Orbit
  , Arc
  
  -- * Movement Constructors
  , dollyIn
  , dollyOut
  , truckLeft
  , truckRight
  , pedestalUp
  , pedestalDown
  , panLeft
  , panRight
  , tiltUp
  , tiltDown
  , rollClockwise
  , rollCounterClockwise
  , zoomIn
  , zoomOut
  , orbitAround
  , arcMove
  
  -- * Lens Properties
  , FocalLength(FocalLength)
  , Aperture(Aperture)
  , FocusDistance(FocusDistance)
  , SensorSize(SensorSize)
  , FieldOfView(FieldOfView)
  
  -- * Lens Constructors
  , focalLength
  , aperture
  , focusDistance
  , fov
  
  -- * Common Focal Lengths
  , ultraWide
  , wideAngle
  , normal
  , portrait
  , telephoto
  , superTelephoto
  
  -- * Common Apertures
  , f1_4
  , f2
  , f2_8
  , f4
  , f5_6
  , f8
  , f11
  , f16
  , f22
  
  -- * Sensor Sizes
  , fullFrame
  , apsc
  , microFourThirds
  , oneInch
  , superThirtyFive
  , imax
  
  -- * FOV Calculations
  , focalLengthToFov
  , fovToFocalLength
  , cropFactor
  , equivalentFocalLength
  
  -- * Depth of Field
  , DepthOfField
  , calculateDof
  , hyperfocalDistance
  , circleOfConfusion
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , identity
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<>)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Physical (Meter(Meter), Millimeter(Millimeter))
import Hydrogen.Schema.Dimension.Angular (Degrees(Degrees))
import Hydrogen.Schema.Dimension.Vector (Vec3(Vec3))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // camera pose
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete camera pose in 3D space
-- | Position is in world units (meters), rotation in world coordinates
type CameraPose =
  { position :: Vec3 Meter          -- ^ Camera location in world space
  , target :: Vec3 Meter            -- ^ Look-at target point
  , up :: Vec3 Number               -- ^ Up vector (typically (0,1,0))
  , fov :: FieldOfView              -- ^ Vertical field of view
  , nearPlane :: Meter              -- ^ Near clipping plane
  , farPlane :: Meter               -- ^ Far clipping plane
  }

-- | Create a camera pose
cameraPose
  :: { position :: Vec3 Meter
     , target :: Vec3 Meter
     , up :: Vec3 Number
     , fov :: FieldOfView
     , nearPlane :: Meter
     , farPlane :: Meter
     }
  -> CameraPose
cameraPose = identity

-- | Default camera pose (5m back, looking at origin)
defaultCameraPose :: CameraPose
defaultCameraPose =
  { position: Vec3 (Meter 0.0) (Meter 1.5) (Meter 5.0)
  , target: Vec3 (Meter 0.0) (Meter 0.0) (Meter 0.0)
  , up: Vec3 0.0 1.0 0.0
  , fov: FieldOfView (Degrees 60.0)
  , nearPlane: Meter 0.1
  , farPlane: Meter 1000.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // camera movements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Abstract camera movement - renderer interprets direction
data CameraMove
  = MoveDolly Dolly
  | MoveTruck Truck
  | MovePedestal Pedestal
  | MovePan Pan
  | MoveTilt Tilt
  | MoveRoll Roll
  | MoveZoom Zoom
  | MoveOrbit Orbit
  | MoveArc Arc

derive instance eqCameraMove :: Eq CameraMove

-- | Dolly: Forward/backward along view axis
newtype Dolly = Dolly Meter

derive instance eqDolly :: Eq Dolly
derive instance ordDolly :: Ord Dolly

instance showDolly :: Show Dolly where
  show (Dolly (Meter d)) = "Dolly " <> show d <> "m"

-- | Truck: Left/right perpendicular to view axis
newtype Truck = Truck Meter

derive instance eqTruck :: Eq Truck
derive instance ordTruck :: Ord Truck

instance showTruck :: Show Truck where
  show (Truck (Meter t)) = "Truck " <> show t <> "m"

-- | Pedestal: Up/down movement (crane)
newtype Pedestal = Pedestal Meter

derive instance eqPedestal :: Eq Pedestal
derive instance ordPedestal :: Ord Pedestal

instance showPedestal :: Show Pedestal where
  show (Pedestal (Meter p)) = "Pedestal " <> show p <> "m"

-- | Pan: Horizontal rotation (yaw)
newtype Pan = Pan Degrees

derive instance eqPan :: Eq Pan
derive instance ordPan :: Ord Pan

instance showPan :: Show Pan where
  show (Pan (Degrees d)) = "Pan " <> show d <> "°"

-- | Tilt: Vertical rotation (pitch)
newtype Tilt = Tilt Degrees

derive instance eqTilt :: Eq Tilt
derive instance ordTilt :: Ord Tilt

instance showTilt :: Show Tilt where
  show (Tilt (Degrees d)) = "Tilt " <> show d <> "°"

-- | Roll: Rotation around view axis (dutch angle)
newtype Roll = Roll Degrees

derive instance eqRoll :: Eq Roll
derive instance ordRoll :: Ord Roll

instance showRoll :: Show Roll where
  show (Roll (Degrees d)) = "Roll " <> show d <> "°"

-- | Zoom: Change focal length (not physical movement)
newtype Zoom = Zoom Number  -- Factor: >1 = zoom in, <1 = zoom out

derive instance eqZoom :: Eq Zoom
derive instance ordZoom :: Ord Zoom

instance showZoom :: Show Zoom where
  show (Zoom z) = "Zoom " <> show z <> "x"

-- | Orbit: Rotate around a target point
type Orbit =
  { center :: Vec3 Meter    -- ^ Point to orbit around
  , azimuth :: Degrees      -- ^ Horizontal angle change
  , elevation :: Degrees    -- ^ Vertical angle change
  }

-- | Arc: Curved camera path
type Arc =
  { startAngle :: Degrees
  , endAngle :: Degrees
  , radius :: Meter
  , center :: Vec3 Meter
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // movement constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Move camera toward subject
dollyIn :: Meter -> CameraMove
dollyIn d = MoveDolly (Dolly d)

-- | Move camera away from subject
dollyOut :: Meter -> CameraMove
dollyOut (Meter d) = MoveDolly (Dolly (Meter (negate d)))

-- | Move camera left
truckLeft :: Meter -> CameraMove
truckLeft (Meter t) = MoveTruck (Truck (Meter (negate t)))

-- | Move camera right
truckRight :: Meter -> CameraMove
truckRight t = MoveTruck (Truck t)

-- | Raise camera
pedestalUp :: Meter -> CameraMove
pedestalUp p = MovePedestal (Pedestal p)

-- | Lower camera
pedestalDown :: Meter -> CameraMove
pedestalDown (Meter p) = MovePedestal (Pedestal (Meter (negate p)))

-- | Rotate camera left (looking left)
panLeft :: Degrees -> CameraMove
panLeft d = MovePan (Pan d)

-- | Rotate camera right (looking right)
panRight :: Degrees -> CameraMove
panRight (Degrees d) = MovePan (Pan (Degrees (negate d)))

-- | Rotate camera up (looking up)
tiltUp :: Degrees -> CameraMove
tiltUp d = MoveTilt (Tilt d)

-- | Rotate camera down (looking down)
tiltDown :: Degrees -> CameraMove
tiltDown (Degrees d) = MoveTilt (Tilt (Degrees (negate d)))

-- | Roll camera clockwise
rollClockwise :: Degrees -> CameraMove
rollClockwise d = MoveRoll (Roll d)

-- | Roll camera counter-clockwise
rollCounterClockwise :: Degrees -> CameraMove
rollCounterClockwise (Degrees d) = MoveRoll (Roll (Degrees (negate d)))

-- | Zoom in (increase focal length)
zoomIn :: Number -> CameraMove
zoomIn factor = MoveZoom (Zoom factor)

-- | Zoom out (decrease focal length)
zoomOut :: Number -> CameraMove
zoomOut factor = MoveZoom (Zoom (1.0 / factor))

-- | Orbit around a point
orbitAround :: Vec3 Meter -> Degrees -> Degrees -> CameraMove
orbitAround center azimuth elevation = MoveOrbit { center, azimuth, elevation }

-- | Arc movement
arcMove :: Vec3 Meter -> Meter -> Degrees -> Degrees -> CameraMove
arcMove center radius startAngle endAngle = MoveArc { center, radius, startAngle, endAngle }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lens properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focal length in millimeters
newtype FocalLength = FocalLength Millimeter

derive instance eqFocalLength :: Eq FocalLength
derive instance ordFocalLength :: Ord FocalLength

instance showFocalLength :: Show FocalLength where
  show (FocalLength (Millimeter mm)) = show mm <> "mm"

-- | Aperture (f-stop)
newtype Aperture = Aperture Number

derive instance eqAperture :: Eq Aperture
derive instance ordAperture :: Ord Aperture

instance showAperture :: Show Aperture where
  show (Aperture f) = "f/" <> show f

-- | Focus distance (distance to focal plane)
newtype FocusDistance = FocusDistance Meter

derive instance eqFocusDistance :: Eq FocusDistance
derive instance ordFocusDistance :: Ord FocusDistance

instance showFocusDistance :: Show FocusDistance where
  show (FocusDistance (Meter m)) = show m <> "m focus"

-- | Sensor/film gate size (diagonal)
newtype SensorSize = SensorSize Millimeter

derive instance eqSensorSize :: Eq SensorSize
derive instance ordSensorSize :: Ord SensorSize

instance showSensorSize :: Show SensorSize where
  show (SensorSize (Millimeter mm)) = show mm <> "mm sensor"

-- | Field of view (vertical unless specified)
newtype FieldOfView = FieldOfView Degrees

derive instance eqFieldOfView :: Eq FieldOfView
derive instance ordFieldOfView :: Ord FieldOfView

instance showFieldOfView :: Show FieldOfView where
  show (FieldOfView (Degrees d)) = show d <> "° FOV"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // lens constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create focal length in mm
focalLength :: Number -> FocalLength
focalLength mm = FocalLength (Millimeter mm)

-- | Create aperture f-stop
aperture :: Number -> Aperture
aperture = Aperture

-- | Create focus distance in meters
focusDistance :: Number -> FocusDistance
focusDistance m = FocusDistance (Meter m)

-- | Create field of view in degrees
fov :: Number -> FieldOfView
fov d = FieldOfView (Degrees d)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // common focal lengths
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ultra wide angle (14mm full frame equivalent)
ultraWide :: FocalLength
ultraWide = FocalLength (Millimeter 14.0)

-- | Wide angle (24mm)
wideAngle :: FocalLength
wideAngle = FocalLength (Millimeter 24.0)

-- | Normal lens (50mm, matches human eye perspective)
normal :: FocalLength
normal = FocalLength (Millimeter 50.0)

-- | Portrait lens (85mm)
portrait :: FocalLength
portrait = FocalLength (Millimeter 85.0)

-- | Telephoto (200mm)
telephoto :: FocalLength
telephoto = FocalLength (Millimeter 200.0)

-- | Super telephoto (400mm+)
superTelephoto :: FocalLength
superTelephoto = FocalLength (Millimeter 400.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common apertures
-- ═════════════════════════════════════════════════════════════════════════════

f1_4 :: Aperture
f1_4 = Aperture 1.4

f2 :: Aperture
f2 = Aperture 2.0

f2_8 :: Aperture
f2_8 = Aperture 2.8

f4 :: Aperture
f4 = Aperture 4.0

f5_6 :: Aperture
f5_6 = Aperture 5.6

f8 :: Aperture
f8 = Aperture 8.0

f11 :: Aperture
f11 = Aperture 11.0

f16 :: Aperture
f16 = Aperture 16.0

f22 :: Aperture
f22 = Aperture 22.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sensor sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full frame (35mm film equivalent, 43.3mm diagonal)
fullFrame :: SensorSize
fullFrame = SensorSize (Millimeter 43.3)

-- | APS-C (crop sensor, ~28mm diagonal, 1.5x crop)
apsc :: SensorSize
apsc = SensorSize (Millimeter 28.4)

-- | Micro Four Thirds (~21.6mm diagonal, 2x crop)
microFourThirds :: SensorSize
microFourThirds = SensorSize (Millimeter 21.6)

-- | 1-inch sensor (~15.9mm diagonal)
oneInch :: SensorSize
oneInch = SensorSize (Millimeter 15.9)

-- | Super 35mm (motion picture, ~28mm diagonal)
superThirtyFive :: SensorSize
superThirtyFive = SensorSize (Millimeter 28.0)

-- | IMAX (70mm film, ~87mm diagonal)
imax :: SensorSize
imax = SensorSize (Millimeter 87.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // fov calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate vertical FOV from focal length and sensor height
-- | fov = 2 * atan(sensorHeight / (2 * focalLength))
focalLengthToFov :: FocalLength -> SensorSize -> FieldOfView
focalLengthToFov (FocalLength (Millimeter fl)) (SensorSize (Millimeter sensor)) =
  let 
    -- Approximate sensor height as 2/3 of diagonal (4:3 aspect)
    sensorHeight = sensor * 0.6
    fovRad = 2.0 * Math.atan (sensorHeight / (2.0 * fl))
    fovDeg = fovRad * 180.0 / Math.pi
  in FieldOfView (Degrees fovDeg)

-- | Calculate focal length from FOV and sensor size
fovToFocalLength :: FieldOfView -> SensorSize -> FocalLength
fovToFocalLength (FieldOfView (Degrees fovDeg)) (SensorSize (Millimeter sensor)) =
  let
    sensorHeight = sensor * 0.6
    fovRad = fovDeg * Math.pi / 180.0
    fl = sensorHeight / (2.0 * Math.tan (fovRad / 2.0))
  in FocalLength (Millimeter fl)

-- | Calculate crop factor relative to full frame
cropFactor :: SensorSize -> Number
cropFactor (SensorSize (Millimeter sensor)) =
  let SensorSize (Millimeter ff) = fullFrame
  in ff / sensor

-- | Calculate full-frame equivalent focal length
equivalentFocalLength :: FocalLength -> SensorSize -> FocalLength
equivalentFocalLength (FocalLength (Millimeter fl)) sensor =
  FocalLength (Millimeter (fl * cropFactor sensor))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // depth of field
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth of field results
type DepthOfField =
  { nearLimit :: Meter    -- ^ Closest in-focus distance
  , farLimit :: Meter     -- ^ Farthest in-focus distance (can be infinity)
  , totalDepth :: Meter   -- ^ Total depth of field
  , frontDepth :: Meter   -- ^ Depth in front of focus plane
  , rearDepth :: Meter    -- ^ Depth behind focus plane
  }

-- | Calculate depth of field
-- | Simplified formula, assumes standard circle of confusion
calculateDof :: FocalLength -> Aperture -> FocusDistance -> SensorSize -> DepthOfField
calculateDof 
  (FocalLength (Millimeter fl)) 
  (Aperture fStop) 
  (FocusDistance (Meter dist))
  sensor =
  let
    coc = circleOfConfusion sensor
    hyperfocal = hyperfocalDistanceNum fl fStop coc
    
    -- Near and far limits
    nearDist = (dist * (hyperfocal - fl / 1000.0)) / (hyperfocal + dist - 2.0 * fl / 1000.0)
    farDist = if dist >= hyperfocal 
              then 10000.0  -- Effectively infinity
              else (dist * (hyperfocal - fl / 1000.0)) / (hyperfocal - dist)
    
    nearLimit = Meter (Math.max 0.0 nearDist)
    farLimit = Meter farDist
    frontDepth = Meter (dist - nearDist)
    rearDepth = Meter (farDist - dist)
    totalDepth = Meter (farDist - nearDist)
  in
    { nearLimit, farLimit, totalDepth, frontDepth, rearDepth }

-- | Calculate hyperfocal distance
hyperfocalDistance :: FocalLength -> Aperture -> SensorSize -> Meter
hyperfocalDistance (FocalLength (Millimeter fl)) (Aperture fStop) sensor =
  Meter (hyperfocalDistanceNum fl fStop (circleOfConfusion sensor))

-- Internal helper
hyperfocalDistanceNum :: Number -> Number -> Number -> Number
hyperfocalDistanceNum fl fStop coc =
  (fl * fl) / (fStop * coc * 1000.0) + fl / 1000.0

-- | Standard circle of confusion for a sensor size
-- | Approximately diagonal / 1500
circleOfConfusion :: SensorSize -> Number
circleOfConfusion (SensorSize (Millimeter diag)) = diag / 1500.0
