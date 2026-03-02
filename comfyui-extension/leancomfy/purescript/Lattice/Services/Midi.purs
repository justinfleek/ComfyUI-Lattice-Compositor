-- | Lattice.Services.Midi - MIDI services re-exports
-- |
-- | Web MIDI API integration for Lattice Compositor.
-- | Provides device capture, message filtering, and property mapping.
-- |
-- | Source: ui/src/services/midi/

module Lattice.Services.Midi
  ( module Types
  , module Service
  ) where

import Lattice.Services.Midi.Types as Types
import Lattice.Services.Midi.Service as Service
