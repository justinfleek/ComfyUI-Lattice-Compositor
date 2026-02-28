-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // schema // spatial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pillar 11: Spatial
-- |
-- | 3D and extended reality.
-- |
-- | ## Submodules
-- |
-- | ### Camera
-- | - `Hydrogen.Schema.Spatial.Camera`
-- | - `Hydrogen.Schema.Spatial.FOV`
-- | - `Hydrogen.Schema.Spatial.NearClip`
-- | - `Hydrogen.Schema.Spatial.FarClip`
-- | - `Hydrogen.Schema.Spatial.FocalLength`
-- | - `Hydrogen.Schema.Spatial.SensorWidth`
-- | - `Hydrogen.Schema.Spatial.Exposure`
-- |
-- | ### Light
-- | - `Hydrogen.Schema.Spatial.Light`
-- | - `Hydrogen.Schema.Spatial.LightIntensity`
-- | - `Hydrogen.Schema.Spatial.LightRange`
-- | - `Hydrogen.Schema.Spatial.SpotAngle`
-- | - `Hydrogen.Schema.Spatial.ShadowBias`
-- | - `Hydrogen.Schema.Spatial.ShadowStrength`
-- |
-- | ### PBR Material
-- | - `Hydrogen.Schema.Spatial.Metallic`
-- | - `Hydrogen.Schema.Spatial.Roughness`
-- | - `Hydrogen.Schema.Spatial.IOR`
-- | - `Hydrogen.Schema.Spatial.Transmission`
-- | - `Hydrogen.Schema.Spatial.ClearCoat`
-- | - `Hydrogen.Schema.Spatial.Sheen`
-- | - `Hydrogen.Schema.Spatial.Subsurface`
-- | - `Hydrogen.Schema.Spatial.Anisotropy`
-- |
-- | This module exists as documentation. Import submodules directly.

module Hydrogen.Schema.Spatial
  ( module Hydrogen.Schema.Spatial
  ) where

-- | Spatial pillar version for compatibility checks.
spatialVersion :: String
spatialVersion = "0.1.0"
