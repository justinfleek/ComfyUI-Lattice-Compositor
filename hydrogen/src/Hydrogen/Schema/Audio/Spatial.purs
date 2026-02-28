-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // audio // spatial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stereo and spatial audio positioning atoms.
-- |
-- | ## Stereo Positioning
-- | Pan and Balance control left/right placement in the stereo field.
-- | Pan: -1.0 = full left, 0.0 = center, 1.0 = full right.
-- |
-- | ## Stereo Width
-- | Width controls the stereo spread of a signal.
-- | 0.0 = mono, 1.0 = normal stereo, 2.0 = extra wide.
-- |
-- | ## 3D Spatial Audio
-- | Azimuth and Elevation position sounds in 3D space around the listener.
-- | Distance affects volume attenuation with proximity.

module Hydrogen.Schema.Audio.Spatial
  ( -- * Types
    Pan(..)
  , Balance(..)
  , StereoWidth(..)
  , Azimuth(..)
  , Elevation(..)
  , AudioDistance(..)
  
  -- * Constructors
  , pan
  , balance
  , stereoWidth
  , azimuth
  , elevation
  , audioDistance
  
  -- * Accessors
  , unwrapPan
  , unwrapBalance
  , unwrapStereoWidth
  , unwrapAzimuth
  , unwrapElevation
  , unwrapAudioDistance
  
  -- * Predefined Positions
  , panLeft
  , panCenter
  , panRight
  , panHardLeft
  , panHardRight
  
  -- * Predefined 3D Positions
  , azimuthFront
  , azimuthLeft
  , azimuthRight
  , azimuthBehind
  , elevationLevel
  , elevationAbove
  , elevationBelow
  
  -- * Conversions
  , panToBalance
  , balanceToPan
  , panToAngle
  , angleToPan
  
  -- * Operations
  , invertPan
  , blendPan
  
  -- * Bounds
  , panBounds
  , balanceBounds
  , stereoWidthBounds
  , azimuthBounds
  , elevationBounds
  , audioDistanceBounds
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // pan
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan - stereo position (-1.0 = left, 0.0 = center, 1.0 = right).
-- | Uses constant-power panning for perceptually even volume.
newtype Pan = Pan Number

derive instance eqPan :: Eq Pan
derive instance ordPan :: Ord Pan

instance showPan :: Show Pan where
  show (Pan n)
    | n < (-0.01) = show n <> " (left)"
    | n > 0.01 = show n <> " (right)"
    | otherwise = "center"

-- | Create a Pan value (clamped to -1.0 to 1.0)
pan :: Number -> Pan
pan n
  | n < (-1.0) = Pan (-1.0)
  | n > 1.0 = Pan 1.0
  | otherwise = Pan n

unwrapPan :: Pan -> Number
unwrapPan (Pan n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // balance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Balance - stereo balance adjustment in percent.
-- | -100 = full left, 0 = center, 100 = full right.
-- | Similar to Pan but expressed as percentage.
newtype Balance = Balance Number

derive instance eqBalance :: Eq Balance
derive instance ordBalance :: Ord Balance

instance showBalance :: Show Balance where
  show (Balance n) = show n <> "% balance"

-- | Create a Balance value (clamped to -100 to 100)
balance :: Number -> Balance
balance n
  | n < (-100.0) = Balance (-100.0)
  | n > 100.0 = Balance 100.0
  | otherwise = Balance n

unwrapBalance :: Balance -> Number
unwrapBalance (Balance n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // stereo width
-- ═════════════════════════════════════════════════════════════════════════════

-- | StereoWidth - stereo field width factor.
-- | 0.0 = mono (summed), 1.0 = normal stereo, 2.0 = extra wide.
-- | Values above 1.0 may cause phase issues.
newtype StereoWidth = StereoWidth Number

derive instance eqStereoWidth :: Eq StereoWidth
derive instance ordStereoWidth :: Ord StereoWidth

instance showStereoWidth :: Show StereoWidth where
  show (StereoWidth n) = show n <> "x width"

-- | Create a StereoWidth value (clamped to 0.0-2.0)
stereoWidth :: Number -> StereoWidth
stereoWidth n
  | n < 0.0 = StereoWidth 0.0
  | n > 2.0 = StereoWidth 2.0
  | otherwise = StereoWidth n

unwrapStereoWidth :: StereoWidth -> Number
unwrapStereoWidth (StereoWidth n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // azimuth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Azimuth - horizontal angle in 3D audio.
-- | -180 to 180 degrees, where 0 = front, 90 = right, -90 = left, ±180 = behind.
-- | Wraps at boundaries.
newtype Azimuth = Azimuth Number

derive instance eqAzimuth :: Eq Azimuth
derive instance ordAzimuth :: Ord Azimuth

instance showAzimuth :: Show Azimuth where
  show (Azimuth n) = show n <> "° azimuth"

-- | Create an Azimuth value (wraps at ±180)
azimuth :: Number -> Azimuth
azimuth n = Azimuth (wrapAngle n)
  where
    wrapAngle angle
      | angle > 180.0 = wrapAngle (angle - 360.0)
      | angle <= (-180.0) = wrapAngle (angle + 360.0)
      | otherwise = angle

unwrapAzimuth :: Azimuth -> Number
unwrapAzimuth (Azimuth n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Elevation - vertical angle in 3D audio.
-- | -90 (below) to 90 (above) degrees, where 0 = ear level.
-- | Clamped at boundaries.
newtype Elevation = Elevation Number

derive instance eqElevation :: Eq Elevation
derive instance ordElevation :: Ord Elevation

instance showElevation :: Show Elevation where
  show (Elevation n) = show n <> "° elevation"

-- | Create an Elevation value (clamped to -90 to 90)
elevation :: Number -> Elevation
elevation n
  | n < (-90.0) = Elevation (-90.0)
  | n > 90.0 = Elevation 90.0
  | otherwise = Elevation n

unwrapElevation :: Elevation -> Number
unwrapElevation (Elevation n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | AudioDistance - distance from listener in 3D audio.
-- | Measured in meters. Affects volume attenuation.
-- | 0 = at listener position, larger values = further away.
newtype AudioDistance = AudioDistance Number

derive instance eqAudioDistance :: Eq AudioDistance
derive instance ordAudioDistance :: Ord AudioDistance

instance showAudioDistance :: Show AudioDistance where
  show (AudioDistance n) = show n <> " m"

-- | Create an AudioDistance value (clamped to non-negative)
audioDistance :: Number -> AudioDistance
audioDistance n
  | n < 0.0 = AudioDistance 0.0
  | otherwise = AudioDistance n

unwrapAudioDistance :: AudioDistance -> Number
unwrapAudioDistance (AudioDistance n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // predefined positions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Moderate left pan (-0.5)
panLeft :: Pan
panLeft = Pan (-0.5)

-- | Center pan (0.0)
panCenter :: Pan
panCenter = Pan 0.0

-- | Moderate right pan (0.5)
panRight :: Pan
panRight = Pan 0.5

-- | Hard left pan (-1.0)
panHardLeft :: Pan
panHardLeft = Pan (-1.0)

-- | Hard right pan (1.0)
panHardRight :: Pan
panHardRight = Pan 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // predefined 3D positions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Front azimuth (0°)
azimuthFront :: Azimuth
azimuthFront = Azimuth 0.0

-- | Left azimuth (-90°)
azimuthLeft :: Azimuth
azimuthLeft = Azimuth (-90.0)

-- | Right azimuth (90°)
azimuthRight :: Azimuth
azimuthRight = Azimuth 90.0

-- | Behind azimuth (180°)
azimuthBehind :: Azimuth
azimuthBehind = Azimuth 180.0

-- | Level elevation (0°)
elevationLevel :: Elevation
elevationLevel = Elevation 0.0

-- | Above elevation (45°)
elevationAbove :: Elevation
elevationAbove = Elevation 45.0

-- | Below elevation (-45°)
elevationBelow :: Elevation
elevationBelow = Elevation (-45.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert pan (-1 to 1) to balance (-100 to 100)
panToBalance :: Pan -> Balance
panToBalance (Pan p) = Balance (p * 100.0)

-- | Convert balance (-100 to 100) to pan (-1 to 1)
balanceToPan :: Balance -> Pan
balanceToPan (Balance b) = pan (b / 100.0)

-- | Convert pan to angle in degrees (-90 to 90).
-- | -1.0 = -90° (left), 0.0 = 0° (center), 1.0 = 90° (right).
panToAngle :: Pan -> Number
panToAngle (Pan p) = p * 90.0

-- | Convert angle (-90 to 90 degrees) to pan.
angleToPan :: Number -> Pan
angleToPan angle = pan (angle / 90.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Invert pan (left becomes right, right becomes left)
invertPan :: Pan -> Pan
invertPan (Pan p) = Pan (negate p)

-- | Blend two pan positions with a ratio.
-- | Ratio 0.0 = first pan, 1.0 = second pan, 0.5 = midpoint.
blendPan :: Number -> Pan -> Pan -> Pan
blendPan ratio (Pan a) (Pan b) =
  let r = clampRatio ratio
      result = a * (1.0 - r) + b * r
  in pan result
  where
    clampRatio x
      | x < 0.0 = 0.0
      | x > 1.0 = 1.0
      | otherwise = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Pan
-- |
-- | Min: -1.0 (full left)
-- | Max: 1.0 (full right)
panBounds :: Bounded.NumberBounds
panBounds = Bounded.numberBounds (-1.0) 1.0 "pan" "Stereo pan (-1 L, 0 C, 1 R)"

-- | Bounds for Balance
-- |
-- | Min: -100.0 (full left)
-- | Max: 100.0 (full right)
balanceBounds :: Bounded.NumberBounds
balanceBounds = Bounded.numberBounds (-100.0) 100.0 "balance" "Stereo balance in percent (-100 to 100)"

-- | Bounds for StereoWidth
-- |
-- | Min: 0.0 (mono)
-- | Max: 2.0 (extra wide)
stereoWidthBounds :: Bounded.NumberBounds
stereoWidthBounds = Bounded.numberBounds 0.0 2.0 "stereoWidth" "Stereo width factor (0-2)"

-- | Bounds for Azimuth
-- |
-- | Min: -180.0 (behind/left)
-- | Max: 180.0 (behind/right)
azimuthBounds :: Bounded.NumberBounds
azimuthBounds = Bounded.numberBounds (-180.0) 180.0 "azimuth" "Horizontal angle in degrees (wraps)"

-- | Bounds for Elevation
-- |
-- | Min: -90.0 (below)
-- | Max: 90.0 (above)
elevationBounds :: Bounded.NumberBounds
elevationBounds = Bounded.numberBounds (-90.0) 90.0 "elevation" "Vertical angle in degrees (-90 to 90)"

-- | Bounds for AudioDistance
-- |
-- | Min: 0.0 (at listener)
-- | Max: unbounded (finite)
audioDistanceBounds :: Bounded.NumberBounds
audioDistanceBounds = Bounded.numberBounds 0.0 10000.0 "audioDistance" "Distance from listener in meters (0+)"
