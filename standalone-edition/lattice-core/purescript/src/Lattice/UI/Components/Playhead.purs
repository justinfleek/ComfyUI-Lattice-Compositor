-- | Playhead Component
-- |
-- | Draggable playhead indicator for timeline scrubbing.
-- | Shows current frame position with visual head and line.
module Lattice.UI.Components.Playhead
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { currentFrame :: Int
  , totalFrames :: Int
  , trackOffset :: Number  -- Offset from left where tracks start (pixels)
  , trackWidth :: Number   -- Width of track area (pixels)
  }

data Output
  = Scrub Int  -- Emit frame to seek to during drag

data Query a

type Slot id = H.Slot Query Output id

type State =
  { currentFrame :: Int
  , totalFrames :: Int
  , trackOffset :: Number
  , trackWidth :: Number
  , isDragging :: Boolean
  }

data Action
  = Receive Input
  | StartDrag
  | StopDrag

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { currentFrame: input.currentFrame
  , totalFrames: input.totalFrames
  , trackOffset: input.trackOffset
  , trackWidth: input.trackWidth
  , isDragging: false
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    -- Calculate position based on current frame (totalFrames - 1 because frames are 0-indexed)
    maxFrame = if state.totalFrames > 1 then state.totalFrames - 1 else 1
    progress = Int.toNumber state.currentFrame / Int.toNumber maxFrame
    positionPx = state.trackOffset + progress * state.trackWidth
  in
  HH.div
    [ cls [ "lattice-playhead" ]
    , HP.attr (HH.AttrName "style") (playheadStyle positionPx)
    , HE.onMouseDown \_ -> StartDrag
    ]
    [ -- Playhead head (triangle/arrow at top)
      HH.div 
        [ cls [ "lattice-playhead-head" ]
        , HP.attr (HH.AttrName "style") playheadHeadStyle
        ] 
        []
    
      -- Playhead line (vertical line through tracks)
    , HH.div 
        [ cls [ "lattice-playhead-line" ]
        , HP.attr (HH.AttrName "style") playheadLineStyle
        ] 
        []
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

playheadStyle :: Number -> String
playheadStyle x =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: " <> show x <> "px; " <>
  "width: 2px; " <>
  "z-index: 10; " <>
  "cursor: ew-resize; " <>
  "transform: translateX(-1px);"

playheadHeadStyle :: String
playheadHeadStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "left: 50%; " <>
  "transform: translateX(-50%); " <>
  "width: 12px; " <>
  "height: 12px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "border-radius: 2px 2px 0 0; " <>
  "clip-path: polygon(0 0, 100% 0, 100% 50%, 50% 100%, 0 50%);"

playheadLineStyle :: String
playheadLineStyle =
  "position: absolute; " <>
  "top: 12px; " <>
  "bottom: 0; " <>
  "left: 0; " <>
  "width: 2px; " <>
  "background: var(--lattice-accent, #8B5CF6); " <>
  "box-shadow: 0 0 8px var(--lattice-accent-glow, rgba(139, 92, 246, 0.3));"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { currentFrame = input.currentFrame
      , totalFrames = input.totalFrames
      , trackOffset = input.trackOffset
      , trackWidth = input.trackWidth
      }
  
  StartDrag -> do
    H.modify_ _ { isDragging = true }
    -- Note: Actual drag handling would be done at the parent level
    -- by handling mouse events on the timeline ruler
  
  StopDrag -> do
    H.modify_ _ { isDragging = false }
