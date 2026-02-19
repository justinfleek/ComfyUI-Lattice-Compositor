-- |
-- Module      : Lattice.State.Audio.Queries
-- Description : Pure query functions for audio state (breaks cycle Audio <-> Beats)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Audio.Queries
  ( activeAnalysis
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Services.AudioFeatures (AudioAnalysis(..))
import Lattice.State.Audio.Types (AudioState(..), StemData(..))

-- | Get active analysis (stem or main)
activeAnalysis :: AudioState -> AudioAnalysis
activeAnalysis state =
  if not (T.null (audioStateActiveStemName state))
  then
    case HM.lookup (audioStateActiveStemName state) (audioStateStemBuffers state) of
      Just stemData -> stemDataAnalysis stemData
      Nothing -> audioStateAudioAnalysis state
  else audioStateAudioAnalysis state
