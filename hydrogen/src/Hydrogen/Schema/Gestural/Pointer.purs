-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // gestural // pointer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pointer - low-level pointer input atoms for mouse, touch, and pen.
-- |
-- | Models the W3C Pointer Events specification with bounded types.
-- | All pointer metrics are normalized to [0,1] or bounded ranges.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, Semiring, Ring)
-- |
-- | ## Dependents
-- | - Gestural.Touch (uses PointerPosition, Pressure)
-- | - Gestural.Gesture (uses PointerState)
-- | - Component.* (interactive components)

module Hydrogen.Schema.Gestural.Pointer
  ( -- * Pointer Device Type
    PointerType(PointerMouse, PointerTouch, PointerPen, PointerUnknown)
  , isMouse
  , isTouch
  , isPen
  , isUnknownPointer
  , pointerTypeFromString
    -- * Pointer Position
  , PointerPosition
  , pointerPosition
  , clientX
  , clientY
  , pageX
  , pageY
  , screenX
  , screenY
  , offsetX
  , offsetY
    -- * Pressure (Force)
  , Pressure(Pressure)
  , pressure
  , noPressure
  , fullPressure
  , unwrapPressure
  , hasPressure
    -- * Pen Tilt
  , TiltX(TiltX)
  , TiltY(TiltY)
  , tiltX
  , tiltY
  , noTilt
  , unwrapTiltX
  , unwrapTiltY
    -- * Pen Twist
  , Twist(Twist)
  , twist
  , noTwist
  , unwrapTwist
    -- * Pointer Dimensions
  , PointerSize
  , pointerSize
  , pointPointer
  , pointerWidth
  , pointerHeight
  , pointerRadius
    -- * Pointer State (Molecule)
  , PointerState
  , pointerState
  , defaultPointerState
  , mousePointerState
  , touchPointerState
  , penPointerState
  
  -- * Bounds
  , pressureBounds
  , tiltXBounds
  , tiltYBounds
  , twistBounds
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // pointer device type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of pointing device per W3C Pointer Events spec
-- | 
-- | Used to distinguish input modality for appropriate feedback:
-- | - Mouse: hover states, cursor changes, right-click
-- | - Touch: larger hit targets, no hover, gestures
-- | - Pen: pressure sensitivity, tilt, barrel button
data PointerType
  = PointerMouse     -- ^ Mouse or trackpad
  | PointerTouch     -- ^ Finger touch
  | PointerPen       -- ^ Stylus or pen
  | PointerUnknown   -- ^ Unknown device type

derive instance eqPointerType :: Eq PointerType
derive instance ordPointerType :: Ord PointerType

instance showPointerType :: Show PointerType where
  show PointerMouse = "mouse"
  show PointerTouch = "touch"
  show PointerPen = "pen"
  show PointerUnknown = "unknown"

-- | Is this a mouse pointer?
isMouse :: PointerType -> Boolean
isMouse PointerMouse = true
isMouse _ = false

-- | Is this a touch pointer?
isTouch :: PointerType -> Boolean
isTouch PointerTouch = true
isTouch _ = false

-- | Is this a pen pointer?
isPen :: PointerType -> Boolean
isPen PointerPen = true
isPen _ = false

-- | Is this an unknown pointer type?
isUnknownPointer :: PointerType -> Boolean
isUnknownPointer PointerUnknown = true
isUnknownPointer _ = false

-- | Parse pointer type from W3C pointerType string
pointerTypeFromString :: String -> PointerType
pointerTypeFromString "mouse" = PointerMouse
pointerTypeFromString "touch" = PointerTouch
pointerTypeFromString "pen" = PointerPen
pointerTypeFromString _ = PointerUnknown

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // pointer position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete pointer position in multiple coordinate systems
-- |
-- | Per W3C Pointer Events, position is expressed relative to:
-- | - client: viewport (visible area)
-- | - page: document (including scroll)
-- | - screen: physical display
-- | - offset: target element
type PointerPosition =
  { clientX :: Number    -- ^ X relative to viewport
  , clientY :: Number    -- ^ Y relative to viewport
  , pageX :: Number      -- ^ X relative to document
  , pageY :: Number      -- ^ Y relative to document
  , screenX :: Number    -- ^ X relative to screen
  , screenY :: Number    -- ^ Y relative to screen
  , offsetX :: Number    -- ^ X relative to target element
  , offsetY :: Number    -- ^ Y relative to target element
  }

-- | Create pointer position from client coordinates
-- | Page and screen default to client values (caller can override)
pointerPosition :: Number -> Number -> PointerPosition
pointerPosition x y =
  { clientX: x
  , clientY: y
  , pageX: x
  , pageY: y
  , screenX: x
  , screenY: y
  , offsetX: 0.0
  , offsetY: 0.0
  }

-- | Get client X coordinate
clientX :: PointerPosition -> Number
clientX pos = pos.clientX

-- | Get client Y coordinate
clientY :: PointerPosition -> Number
clientY pos = pos.clientY

-- | Get page X coordinate
pageX :: PointerPosition -> Number
pageX pos = pos.pageX

-- | Get page Y coordinate
pageY :: PointerPosition -> Number
pageY pos = pos.pageY

-- | Get screen X coordinate
screenX :: PointerPosition -> Number
screenX pos = pos.screenX

-- | Get screen Y coordinate
screenY :: PointerPosition -> Number
screenY pos = pos.screenY

-- | Get offset X coordinate (relative to target)
offsetX :: PointerPosition -> Number
offsetX pos = pos.offsetX

-- | Get offset Y coordinate (relative to target)
offsetY :: PointerPosition -> Number
offsetY pos = pos.offsetY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // pressure (force)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pressure/force applied by pointer, normalized to [0, 1]
-- |
-- | - 0.0: no pressure (hovering or not supported)
-- | - 0.5: normal touch pressure
-- | - 1.0: maximum pressure
-- |
-- | Mouse always reports 0.5 when button is pressed, 0 otherwise.
-- | Touch and pen report actual pressure if hardware supports it.
newtype Pressure = Pressure Number

derive instance eqPressure :: Eq Pressure
derive instance ordPressure :: Ord Pressure

instance showPressure :: Show Pressure where
  show (Pressure p) = show p <> " pressure"

-- | Create pressure value (clamps to [0, 1])
pressure :: Number -> Pressure
pressure p = Pressure (max 0.0 (min 1.0 p))

-- | No pressure (hovering)
noPressure :: Pressure
noPressure = Pressure 0.0

-- | Full pressure
fullPressure :: Pressure
fullPressure = Pressure 1.0

-- | Extract raw pressure value
unwrapPressure :: Pressure -> Number
unwrapPressure (Pressure p) = p

-- | Is there any pressure applied?
hasPressure :: Pressure -> Boolean
hasPressure (Pressure p) = p > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // pen tilt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pen tilt along X axis in degrees [-90, 90]
-- |
-- | - 0: perpendicular to surface
-- | - Negative: tilted left
-- | - Positive: tilted right
newtype TiltX = TiltX Number

derive instance eqTiltX :: Eq TiltX
derive instance ordTiltX :: Ord TiltX

instance showTiltX :: Show TiltX where
  show (TiltX t) = show t <> "° tiltX"

-- | Pen tilt along Y axis in degrees [-90, 90]
-- |
-- | - 0: perpendicular to surface
-- | - Negative: tilted toward user
-- | - Positive: tilted away from user
newtype TiltY = TiltY Number

derive instance eqTiltY :: Eq TiltY
derive instance ordTiltY :: Ord TiltY

instance showTiltY :: Show TiltY where
  show (TiltY t) = show t <> "° tiltY"

-- | Create tilt X value (clamps to [-90, 90])
tiltX :: Number -> TiltX
tiltX t = TiltX (max (-90.0) (min 90.0 t))

-- | Create tilt Y value (clamps to [-90, 90])
tiltY :: Number -> TiltY
tiltY t = TiltY (max (-90.0) (min 90.0 t))

-- | No tilt (perpendicular)
noTilt :: { x :: TiltX, y :: TiltY }
noTilt = { x: TiltX 0.0, y: TiltY 0.0 }

-- | Extract raw tilt X value
unwrapTiltX :: TiltX -> Number
unwrapTiltX (TiltX t) = t

-- | Extract raw tilt Y value
unwrapTiltY :: TiltY -> Number
unwrapTiltY (TiltY t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // pen twist
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pen rotation/twist around its axis in degrees [0, 360)
-- |
-- | Also known as "barrel rotation" on some devices.
-- | Wraps at 360 degrees.
newtype Twist = Twist Number

derive instance eqTwist :: Eq Twist
derive instance ordTwist :: Ord Twist

instance showTwist :: Show Twist where
  show (Twist t) = show t <> "° twist"

-- | Create twist value (wraps to [0, 360))
twist :: Number -> Twist
twist t = 
  let normalized = t - floor (t / 360.0) * 360.0
  in Twist (if normalized < 0.0 then normalized + 360.0 else normalized)
  where
  floor :: Number -> Number
  floor n = if n >= 0.0 
    then n - (n `mod'` 1.0)
    else n - (n `mod'` 1.0) - (if n `mod'` 1.0 == 0.0 then 0.0 else 1.0)
  mod' :: Number -> Number -> Number
  mod' a b = a - b * (floor (a / b))

-- | No twist
noTwist :: Twist
noTwist = Twist 0.0

-- | Extract raw twist value
unwrapTwist :: Twist -> Number
unwrapTwist (Twist t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // pointer dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size of pointer contact area in CSS pixels
-- |
-- | For mouse: always 1x1 (point)
-- | For touch: contact ellipse dimensions
-- | For pen: tip contact area
type PointerSize =
  { width :: Number     -- ^ Contact width in CSS pixels
  , height :: Number    -- ^ Contact height in CSS pixels
  }

-- | Create pointer size (clamps to non-negative)
pointerSize :: Number -> Number -> PointerSize
pointerSize w h =
  { width: max 1.0 w
  , height: max 1.0 h
  }

-- | Point pointer (1x1, typical for mouse)
pointPointer :: PointerSize
pointPointer = pointerSize 1.0 1.0

-- | Get contact width
pointerWidth :: PointerSize -> Number
pointerWidth ps = ps.width

-- | Get contact height
pointerHeight :: PointerSize -> Number
pointerHeight ps = ps.height

-- | Get approximate contact radius (average of width/height / 2)
pointerRadius :: PointerSize -> Number
pointerRadius ps = (ps.width + ps.height) / 4.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pointer state (molecule)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete pointer state combining all pointer attributes
-- |
-- | This is the molecule that combines all pointer atoms into
-- | a single coherent state object for event handling.
type PointerState =
  { pointerId :: Int             -- ^ Unique pointer identifier
  , pointerType :: PointerType   -- ^ Device type (mouse/touch/pen)
  , position :: PointerPosition  -- ^ Position in all coordinate systems
  , pressure :: Pressure         -- ^ Applied pressure
  , tiltX :: TiltX               -- ^ Pen tilt X
  , tiltY :: TiltY               -- ^ Pen tilt Y
  , twist :: Twist               -- ^ Pen twist/rotation
  , size :: PointerSize          -- ^ Contact area size
  , isPrimary :: Boolean         -- ^ Is primary pointer in multi-touch
  , buttons :: Int               -- ^ Bitmask of pressed buttons
  , timestamp :: Maybe Number    -- ^ Event timestamp (ms since epoch)
  }

-- | Create pointer state
pointerState 
  :: Int 
  -> PointerType 
  -> PointerPosition 
  -> Pressure 
  -> PointerState
pointerState id ptype pos pres =
  { pointerId: id
  , pointerType: ptype
  , position: pos
  , pressure: pres
  , tiltX: TiltX 0.0
  , tiltY: TiltY 0.0
  , twist: Twist 0.0
  , size: pointPointer
  , isPrimary: true
  , buttons: 0
  , timestamp: Nothing
  }

-- | Default pointer state (mouse at origin)
defaultPointerState :: PointerState
defaultPointerState = pointerState 1 PointerMouse (pointerPosition 0.0 0.0) noPressure

-- | Create mouse pointer state
mousePointerState :: Int -> PointerPosition -> Int -> PointerState
mousePointerState id pos buttons =
  let pres = if buttons > 0 then pressure 0.5 else noPressure
  in (pointerState id PointerMouse pos pres)
    { buttons = buttons }

-- | Create touch pointer state
touchPointerState :: Int -> PointerPosition -> Pressure -> PointerSize -> PointerState
touchPointerState id pos pres size =
  (pointerState id PointerTouch pos pres)
    { size = size }

-- | Create pen pointer state
penPointerState 
  :: Int 
  -> PointerPosition 
  -> Pressure 
  -> TiltX 
  -> TiltY 
  -> Twist 
  -> PointerState
penPointerState id pos pres tx ty tw =
  (pointerState id PointerPen pos pres)
    { tiltX = tx
    , tiltY = ty
    , twist = tw
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Pressure
-- |
-- | Min: 0.0 (no pressure/hovering)
-- | Max: 1.0 (maximum pressure)
pressureBounds :: Bounded.NumberBounds
pressureBounds = Bounded.numberBounds 0.0 1.0 "pressure" "Pointer pressure (0-1)"

-- | Bounds for TiltX
-- |
-- | Min: -90.0 (tilted fully left)
-- | Max: 90.0 (tilted fully right)
tiltXBounds :: Bounded.NumberBounds
tiltXBounds = Bounded.numberBounds (-90.0) 90.0 "tiltX" "Pen tilt X in degrees (-90 to 90)"

-- | Bounds for TiltY
-- |
-- | Min: -90.0 (tilted fully away)
-- | Max: 90.0 (tilted fully toward)
tiltYBounds :: Bounded.NumberBounds
tiltYBounds = Bounded.numberBounds (-90.0) 90.0 "tiltY" "Pen tilt Y in degrees (-90 to 90)"

-- | Bounds for Twist
-- |
-- | Min: 0.0
-- | Max: 359.0 (cyclic rotation)
twistBounds :: Bounded.NumberBounds
twistBounds = Bounded.numberBounds 0.0 359.0 "twist" "Pen twist in degrees (0-359)"
