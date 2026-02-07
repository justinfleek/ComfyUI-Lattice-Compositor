-- | Lattice.Services.Export.VACE.Types - VACE export types
-- |
-- | Types for VACE (Video Animation Control Engine) control video generation.
-- | Shapes following spline paths with arc-length parameterization.
-- |
-- | Source: ui/src/services/export/vaceControlExport.ts

module Lattice.Services.Export.VACE.Types
  ( -- * Shape Types
    PathFollowerShape(..)
  , PathFollowerEasing(..)
  , LoopMode(..)
  , OutputFormat(..)
    -- * Configuration Types
  , SplineControlPoint
  , PathFollowerConfig
  , VACEExportConfig
    -- * State Types
  , PathFollowerState
  , VACEFrame
  , PathStats
    -- * Defaults
  , defaultPathFollowerConfig
  , defaultVACEExportConfig
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

--------------------------------------------------------------------------------
-- Shape Types
--------------------------------------------------------------------------------

-- | Path follower shape options
data PathFollowerShape
  = ShapeCircle
  | ShapeSquare
  | ShapeTriangle
  | ShapeDiamond
  | ShapeArrow
  | ShapeCustom

derive instance Generic PathFollowerShape _
instance Show PathFollowerShape where show = genericShow
instance Eq PathFollowerShape where eq = genericEq

-- | Easing function options
data PathFollowerEasing
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseInCubic
  | EaseOutCubic

derive instance Generic PathFollowerEasing _
instance Show PathFollowerEasing where show = genericShow
instance Eq PathFollowerEasing where eq = genericEq

-- | Loop mode options
data LoopMode
  = LoopRestart
  | LoopPingPong

derive instance Generic LoopMode _
instance Show LoopMode where show = genericShow
instance Eq LoopMode where eq = genericEq

-- | Output format options
data OutputFormat
  = OutputCanvas
  | OutputWebM
  | OutputFrames

derive instance Generic OutputFormat _
instance Show OutputFormat where show = genericShow
instance Eq OutputFormat where eq = genericEq

--------------------------------------------------------------------------------
-- Configuration Types
--------------------------------------------------------------------------------

-- | Spline control point with optional 3D coordinates
type SplineControlPoint =
  { x :: Number
  , y :: Number
  , z :: Maybe Number
  , handleIn :: Maybe { x :: Number, y :: Number, z :: Maybe Number }
  , handleOut :: Maybe { x :: Number, y :: Number, z :: Maybe Number }
  }

-- | Path follower configuration
type PathFollowerConfig =
  { id :: String
  , controlPoints :: Array SplineControlPoint
  , closed :: Boolean
  , shape :: PathFollowerShape
  , size :: { width :: Number, height :: Number }
  , fillColor :: String
  , strokeColor :: Maybe String
  , strokeWidth :: Maybe Number
  , startFrame :: Int
  , duration :: Int          -- Speed = pathLength / duration
  , easing :: PathFollowerEasing
  , alignToPath :: Boolean
  , rotationOffset :: Number -- degrees
  , loop :: Boolean
  , loopMode :: LoopMode
  , scaleStart :: Number
  , scaleEnd :: Number
  , opacityStart :: Number
  , opacityEnd :: Number
  }

-- | VACE export configuration
type VACEExportConfig =
  { width :: Int
  , height :: Int
  , startFrame :: Int
  , endFrame :: Int
  , frameRate :: Int
  , backgroundColor :: String
  , pathFollowers :: Array PathFollowerConfig
  , outputFormat :: OutputFormat
  , antiAlias :: Boolean
  }

--------------------------------------------------------------------------------
-- State Types
--------------------------------------------------------------------------------

-- | Path follower state at a frame
type PathFollowerState =
  { position :: { x :: Number, y :: Number }
  , rotation :: Number    -- radians
  , scale :: Number
  , opacity :: Number
  , progress :: Number    -- 0-1 along path
  , visible :: Boolean
  }

-- | VACE frame result (opaque canvas handle in FFI)
type VACEFrame =
  { frameNumber :: Int
  , states :: Array { id :: String, state :: PathFollowerState }
  }

-- | Path statistics
type PathStats =
  { id :: String
  , length :: Number
  , speed :: Number       -- pixels per frame
  , duration :: Int
  }

--------------------------------------------------------------------------------
-- Defaults
--------------------------------------------------------------------------------

-- | Default path follower configuration
defaultPathFollowerConfig :: PathFollowerConfig
defaultPathFollowerConfig =
  { id: ""
  , controlPoints: []
  , closed: false
  , shape: ShapeCircle
  , size: { width: 20.0, height: 20.0 }
  , fillColor: "#FFFFFF"
  , strokeColor: Nothing
  , strokeWidth: Nothing
  , startFrame: 0
  , duration: 60
  , easing: EaseInOut
  , alignToPath: true
  , rotationOffset: 0.0
  , loop: false
  , loopMode: LoopRestart
  , scaleStart: 1.0
  , scaleEnd: 1.0
  , opacityStart: 1.0
  , opacityEnd: 1.0
  }

-- | Default VACE export configuration
defaultVACEExportConfig :: VACEExportConfig
defaultVACEExportConfig =
  { width: 512
  , height: 512
  , startFrame: 0
  , endFrame: 80
  , frameRate: 16
  , backgroundColor: "#000000"
  , pathFollowers: []
  , outputFormat: OutputCanvas
  , antiAlias: true
  }
