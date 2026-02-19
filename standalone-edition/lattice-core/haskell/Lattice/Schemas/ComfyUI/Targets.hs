{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.ComfyUI.Targets
Description : Export targets and format types for ComfyUI integration
Copyright   : (c) Lattice, 2026
License     : MIT

Defines export targets, depth map formats, and control types
for ComfyUI workflow integration.

Source: ui/src/schemas/comfyui/targets.ts
-}

module Lattice.Schemas.ComfyUI.Targets
  ( -- * Export Target
    ExportTarget(..)
  , exportTargetFromText
  , exportTargetToText
    -- * Depth Map Format
  , DepthMapFormat(..)
  , depthMapFormatFromText
  , depthMapFormatToText
    -- * Control Type
  , ControlType(..)
  , controlTypeFromText
  , controlTypeToText
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Export Target
-- ────────────────────────────────────────────────────────────────────────────

-- | Export target for ComfyUI workflows
data ExportTarget
  = TargetComfyUI       -- ^ Standard ComfyUI workflow
  | TargetA1111         -- ^ Automatic1111 WebUI
  | TargetForge         -- ^ Forge WebUI
  | TargetInvokeAI      -- ^ InvokeAI
  | TargetCustom        -- ^ Custom target
  deriving stock (Eq, Show, Generic)

exportTargetFromText :: Text -> Maybe ExportTarget
exportTargetFromText "comfyui" = Just TargetComfyUI
exportTargetFromText "a1111"   = Just TargetA1111
exportTargetFromText "forge"   = Just TargetForge
exportTargetFromText "invokeai" = Just TargetInvokeAI
exportTargetFromText "custom"  = Just TargetCustom
exportTargetFromText _         = Nothing

exportTargetToText :: ExportTarget -> Text
exportTargetToText TargetComfyUI = "comfyui"
exportTargetToText TargetA1111   = "a1111"
exportTargetToText TargetForge   = "forge"
exportTargetToText TargetInvokeAI = "invokeai"
exportTargetToText TargetCustom  = "custom"

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Map Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth map output format
data DepthMapFormat
  = DepthMidas         -- ^ MiDaS depth estimation
  | DepthZoe           -- ^ ZoeDepth
  | DepthMarigold      -- ^ Marigold depth
  | DepthDepthAnything -- ^ Depth Anything v2
  | DepthNormalized    -- ^ Normalized 0-1 depth
  | DepthInverse       -- ^ Inverse depth (disparity)
  deriving stock (Eq, Show, Generic)

depthMapFormatFromText :: Text -> Maybe DepthMapFormat
depthMapFormatFromText "midas"          = Just DepthMidas
depthMapFormatFromText "zoe"            = Just DepthZoe
depthMapFormatFromText "marigold"       = Just DepthMarigold
depthMapFormatFromText "depth_anything" = Just DepthDepthAnything
depthMapFormatFromText "normalized"     = Just DepthNormalized
depthMapFormatFromText "inverse"        = Just DepthInverse
depthMapFormatFromText _                = Nothing

depthMapFormatToText :: DepthMapFormat -> Text
depthMapFormatToText DepthMidas         = "midas"
depthMapFormatToText DepthZoe           = "zoe"
depthMapFormatToText DepthMarigold      = "marigold"
depthMapFormatToText DepthDepthAnything = "depth_anything"
depthMapFormatToText DepthNormalized    = "normalized"
depthMapFormatToText DepthInverse       = "inverse"

-- ────────────────────────────────────────────────────────────────────────────
-- Control Type
-- ────────────────────────────────────────────────────────────────────────────

-- | ControlNet control type
data ControlType
  = ControlCanny       -- ^ Canny edge detection
  | ControlDepth       -- ^ Depth map
  | ControlNormal      -- ^ Normal map
  | ControlPose        -- ^ OpenPose skeleton
  | ControlSoftEdge    -- ^ Soft edge (HED/PIDI)
  | ControlScribble    -- ^ Scribble/sketch
  | ControlLineart     -- ^ Line art
  | ControlSeg         -- ^ Segmentation map
  | ControlTile        -- ^ Tile/texture
  | ControlInpaint     -- ^ Inpainting mask
  | ControlIPAdapter   -- ^ IP-Adapter style
  deriving stock (Eq, Show, Generic)

controlTypeFromText :: Text -> Maybe ControlType
controlTypeFromText "canny"      = Just ControlCanny
controlTypeFromText "depth"      = Just ControlDepth
controlTypeFromText "normal"     = Just ControlNormal
controlTypeFromText "pose"       = Just ControlPose
controlTypeFromText "softedge"   = Just ControlSoftEdge
controlTypeFromText "scribble"   = Just ControlScribble
controlTypeFromText "lineart"    = Just ControlLineart
controlTypeFromText "seg"        = Just ControlSeg
controlTypeFromText "tile"       = Just ControlTile
controlTypeFromText "inpaint"    = Just ControlInpaint
controlTypeFromText "ip_adapter" = Just ControlIPAdapter
controlTypeFromText _            = Nothing

controlTypeToText :: ControlType -> Text
controlTypeToText ControlCanny     = "canny"
controlTypeToText ControlDepth     = "depth"
controlTypeToText ControlNormal    = "normal"
controlTypeToText ControlPose      = "pose"
controlTypeToText ControlSoftEdge  = "softedge"
controlTypeToText ControlScribble  = "scribble"
controlTypeToText ControlLineart   = "lineart"
controlTypeToText ControlSeg       = "seg"
controlTypeToText ControlTile      = "tile"
controlTypeToText ControlInpaint   = "inpaint"
controlTypeToText ControlIPAdapter = "ip_adapter"
