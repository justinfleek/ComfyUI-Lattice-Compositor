-- |
-- Module      : Lattice.State.Animation.WorkArea
-- Description : Work area operations for animation store
-- 
-- Migrated from ui/src/stores/animationStore/index.ts (work area section)
-- Pure functions for work area management and loop playback
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Animation.WorkArea
  ( setWorkArea
  , clearWorkArea
  , setLoopPlayback
  , hasWorkArea
  , effectiveStartFrame
  , effectiveEndFrame
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Animation.Types (AnimationState(..))
import Lattice.Types.Primitives (validateFinite, validateNonNegative)

-- ============================================================================
-- WORK AREA OPERATIONS
-- ============================================================================

-- | Set work area bounds
-- Pure function: takes animation state and start/end frames, returns new state
-- Uses explicit values with defaults - no Maybe/Nothing
setWorkArea ::
  AnimationState -> -- Current animation state
  Double -> -- Work area start frame (must be >= 0)
  Bool -> -- Explicit flag: start is set (True) or use default (False)
  Double -> -- Work area end frame (must be >= 0)
  Bool -> -- Explicit flag: end is set (True) or use default (False)
  Either Text AnimationState -- Updated animation state, or error
setWorkArea state start startSet end_ endSet =
  let
    -- Validate start frame if set
    validateStart = if startSet
      then validateFinite start && validateNonNegative start
      else True
    
    -- Validate end frame if set
    validateEnd = if endSet
      then validateFinite end_ && validateNonNegative end_
      else True
  in
    if validateStart && validateEnd
      then Right (state
        { animationStateWorkAreaStart = start
        , animationStateWorkAreaStartSet = startSet
        , animationStateWorkAreaEnd = end_
        , animationStateWorkAreaEndSet = endSet
        })
      else Left ("setWorkArea: Work area frames must be finite and non-negative if set")

-- | Clear work area
-- Pure function: takes animation state, returns new state with work area cleared
-- Uses explicit defaults - no Maybe/Nothing
clearWorkArea ::
  AnimationState -> -- Current animation state
  AnimationState -- Updated animation state with work area cleared
clearWorkArea state =
  state
    { animationStateWorkAreaStart = 0.0
    , animationStateWorkAreaStartSet = False
    , animationStateWorkAreaEnd = 0.0
    , animationStateWorkAreaEndSet = False
    }

-- | Set loop playback mode
-- Pure function: takes animation state and loop flag, returns new state
setLoopPlayback ::
  AnimationState -> -- Current animation state
  Bool -> -- Loop playback flag
  AnimationState -- Updated animation state
setLoopPlayback state loop =
  state {animationStateLoopPlayback = loop}

-- ============================================================================
-- WORK AREA QUERIES
-- ============================================================================

-- | Check if work area is defined
-- Pure function: takes animation state, returns True if work area is defined
-- Uses explicit flags - no Maybe/Nothing
hasWorkArea ::
  AnimationState -> -- Animation state
  Bool -- True if work area is defined
hasWorkArea state =
  animationStateWorkAreaStartSet state && animationStateWorkAreaEndSet state

-- | Get effective start frame (work area start or 0)
-- Pure function: takes animation state, returns effective start frame
-- Uses explicit flag - no Maybe/Nothing
effectiveStartFrame ::
  AnimationState -> -- Animation state
  Double -- Effective start frame (workAreaStart if set, otherwise 0.0)
effectiveStartFrame state =
  if animationStateWorkAreaStartSet state
  then
    let start = animationStateWorkAreaStart state
    in if validateFinite start && validateNonNegative start
      then start
      else 0.0
  else 0.0

-- | Get effective end frame (work area end or frameCount - 1)
-- Pure function: takes animation state and frame count, returns effective end frame
-- Uses explicit flag - no Maybe/Nothing
effectiveEndFrame ::
  AnimationState -> -- Animation state
  Double -> -- Composition frame count
  Double -- Effective end frame (workAreaEnd if set, otherwise frameCount - 1)
effectiveEndFrame state frameCount =
  if animationStateWorkAreaEndSet state
  then
    let end_ = animationStateWorkAreaEnd state
    in if validateFinite end_ && validateNonNegative end_
      then end_
      else if validateFinite frameCount && frameCount >= 1
        then frameCount - 1.0
        else 0.0
  else
    if validateFinite frameCount && frameCount >= 1
      then frameCount - 1.0
      else 0.0
