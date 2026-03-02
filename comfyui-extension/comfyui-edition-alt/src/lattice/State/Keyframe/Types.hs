-- |
-- Module      : Lattice.State.Keyframe.Types
-- Description : Types for keyframe store operations
-- 
-- Migrated from ui/src/stores/keyframeStore/types.ts
-- Types for keyframe operations, velocity settings, and store state
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Keyframe.Types
  ( VelocitySettings(..)
  , KeyframeSelection(..)
  , KeyframeState(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Types.Animation (ClipboardKeyframe(..))
import Lattice.Types.Primitives (validateFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // velocity // settings
-- ════════════════════════════════════════════════════════════════════════════

-- | Velocity settings for keyframe handles
data VelocitySettings = VelocitySettings
  { velocitySettingsIncomingVelocity :: Double  -- Incoming velocity in units per second
  , velocitySettingsOutgoingVelocity :: Double  -- Outgoing velocity in units per second
  , velocitySettingsIncomingInfluence :: Double  -- Incoming influence as percentage (0-100)
  , velocitySettingsOutgoingInfluence :: Double  -- Outgoing influence as percentage (0-100)
  }
  deriving (Eq, Show, Generic)

instance ToJSON VelocitySettings where
  toJSON (VelocitySettings incoming outgoing incomingInf outgoingInf) =
    object
      [ "incomingVelocity" .= incoming
      , "outgoingVelocity" .= outgoing
      , "incomingInfluence" .= incomingInf
      , "outgoingInfluence" .= outgoingInf
      ]

instance FromJSON VelocitySettings where
  parseJSON = withObject "VelocitySettings" (\o -> do
    incoming <- o .: "incomingVelocity"
    outgoing <- o .: "outgoingVelocity"
    incomingInf <- o .: "incomingInfluence"
    outgoingInf <- o .: "outgoingInfluence"
    -- Validate: velocities must be finite, influences must be in [0, 100]
    if validateFinite incoming && validateFinite outgoing &&
       validateFinite incomingInf && validateFinite outgoingInf &&
       incomingInf >= 0 && incomingInf <= 100 &&
       outgoingInf >= 0 && outgoingInf <= 100
      then return (VelocitySettings incoming outgoing incomingInf outgoingInf)
      else fail "VelocitySettings: velocities must be finite, influences must be in [0, 100]"
    )

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // keyframe // selection
-- ════════════════════════════════════════════════════════════════════════════

-- | Keyframe selection for bulk operations
data KeyframeSelection = KeyframeSelection
  { keyframeSelectionLayerId :: Text
  , keyframeSelectionPropertyPath :: Text
  , keyframeSelectionKeyframeId :: Text
  }
  deriving (Eq, Show, Generic)

instance ToJSON KeyframeSelection where
  toJSON (KeyframeSelection layerId propertyPath keyframeId) =
    object
      [ "layerId" .= layerId
      , "propertyPath" .= propertyPath
      , "keyframeId" .= keyframeId
      ]

instance FromJSON KeyframeSelection where
  parseJSON = withObject "KeyframeSelection" (\o -> do
    layerId <- o .: "layerId"
    propertyPath <- o .: "propertyPath"
    keyframeId <- o .: "keyframeId"
    return (KeyframeSelection layerId propertyPath keyframeId)
    )

-- ════════════════════════════════════════════════════════════════════════════
--                                                // keyframe // store // state
-- ════════════════════════════════════════════════════════════════════════════

-- | Keyframe store state
-- Maintains clipboard state for keyframe copy/paste
data KeyframeState = KeyframeState
  { keyframeStateClipboard :: [ClipboardKeyframe]
  }
  deriving (Eq, Show, Generic)

instance ToJSON KeyframeState where
  toJSON (KeyframeState clipboard) =
    object
      [ "clipboard" .= object ["keyframes" .= clipboard]
      ]

instance FromJSON KeyframeState where
  parseJSON = withObject "KeyframeState" (\o -> do
    clipboardObj <- o .: "clipboard"
    keyframes <- clipboardObj .: "keyframes"
    return (KeyframeState keyframes)
    )
