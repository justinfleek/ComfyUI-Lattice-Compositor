-- | Lattice.Schemas.Layers.LayerDataSchema.Media - Media layer enums
-- |
-- | Enums for Image, Video, Depth, Normal, and Generated layers.

module Lattice.Schemas.Layers.LayerDataSchema.Media
  ( -- Image Layer
    ImageFitMode(..), imageFitModeFromString, imageFitModeToString
  , ImageSourceType(..), imageSourceTypeFromString
    -- Video Layer
  , TimewarpMethod(..), timewarpMethodFromString
  , FrameBlending(..), frameBlendingFromString
    -- Depth Layer
  , DepthVisualizationMode(..), depthVisualizationModeFromString
  , DepthColorMap(..), depthColorMapFromString
    -- Normal Layer
  , NormalVisualizationMode(..), normalVisualizationModeFromString
  , NormalFormat(..), normalFormatFromString
    -- Generated Layer
  , GenerationType(..), generationTypeFromString
  , GenerationStatus(..), generationStatusFromString
    -- Generated Map
  , GeneratedMapType(..), generatedMapTypeFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Image Layer
--------------------------------------------------------------------------------

data ImageFitMode = FitNone | FitContain | FitCover | FitFill

derive instance Eq ImageFitMode
derive instance Generic ImageFitMode _
instance Show ImageFitMode where show = genericShow

imageFitModeFromString :: String -> Maybe ImageFitMode
imageFitModeFromString = case _ of
  "none" -> Just FitNone
  "contain" -> Just FitContain
  "cover" -> Just FitCover
  "fill" -> Just FitFill
  _ -> Nothing

imageFitModeToString :: ImageFitMode -> String
imageFitModeToString = case _ of
  FitNone -> "none"
  FitContain -> "contain"
  FitCover -> "cover"
  FitFill -> "fill"

data ImageSourceType = SourceFile | SourceGenerated | SourceSegmented

derive instance Eq ImageSourceType
derive instance Generic ImageSourceType _
instance Show ImageSourceType where show = genericShow

imageSourceTypeFromString :: String -> Maybe ImageSourceType
imageSourceTypeFromString = case _ of
  "file" -> Just SourceFile
  "generated" -> Just SourceGenerated
  "segmented" -> Just SourceSegmented
  _ -> Nothing

--------------------------------------------------------------------------------
-- Video Layer
--------------------------------------------------------------------------------

data TimewarpMethod = TwWholeFrames | TwFrameMix | TwPixelMotion

derive instance Eq TimewarpMethod
derive instance Generic TimewarpMethod _
instance Show TimewarpMethod where show = genericShow

timewarpMethodFromString :: String -> Maybe TimewarpMethod
timewarpMethodFromString = case _ of
  "whole-frames" -> Just TwWholeFrames
  "frame-mix" -> Just TwFrameMix
  "pixel-motion" -> Just TwPixelMotion
  _ -> Nothing

data FrameBlending = FbNone | FbFrameMix | FbPixelMotion

derive instance Eq FrameBlending
derive instance Generic FrameBlending _
instance Show FrameBlending where show = genericShow

frameBlendingFromString :: String -> Maybe FrameBlending
frameBlendingFromString = case _ of
  "none" -> Just FbNone
  "frame-mix" -> Just FbFrameMix
  "pixel-motion" -> Just FbPixelMotion
  _ -> Nothing

--------------------------------------------------------------------------------
-- Depth Layer
--------------------------------------------------------------------------------

data DepthVisualizationMode = DepthGrayscale | DepthColormap | DepthContour | DepthMesh3d

derive instance Eq DepthVisualizationMode
derive instance Generic DepthVisualizationMode _
instance Show DepthVisualizationMode where show = genericShow

depthVisualizationModeFromString :: String -> Maybe DepthVisualizationMode
depthVisualizationModeFromString = case _ of
  "grayscale" -> Just DepthGrayscale
  "colormap" -> Just DepthColormap
  "contour" -> Just DepthContour
  "3d-mesh" -> Just DepthMesh3d
  _ -> Nothing

data DepthColorMap = CmTurbo | CmViridis | CmPlasma | CmInferno | CmMagma | CmGrayscale

derive instance Eq DepthColorMap
derive instance Generic DepthColorMap _
instance Show DepthColorMap where show = genericShow

depthColorMapFromString :: String -> Maybe DepthColorMap
depthColorMapFromString = case _ of
  "turbo" -> Just CmTurbo
  "viridis" -> Just CmViridis
  "plasma" -> Just CmPlasma
  "inferno" -> Just CmInferno
  "magma" -> Just CmMagma
  "grayscale" -> Just CmGrayscale
  _ -> Nothing

--------------------------------------------------------------------------------
-- Normal Layer
--------------------------------------------------------------------------------

data NormalVisualizationMode = NormRgb | NormHemisphere | NormArrows | NormLit

derive instance Eq NormalVisualizationMode
derive instance Generic NormalVisualizationMode _
instance Show NormalVisualizationMode where show = genericShow

normalVisualizationModeFromString :: String -> Maybe NormalVisualizationMode
normalVisualizationModeFromString = case _ of
  "rgb" -> Just NormRgb
  "hemisphere" -> Just NormHemisphere
  "arrows" -> Just NormArrows
  "lit" -> Just NormLit
  _ -> Nothing

data NormalFormat = NfOpenGL | NfDirectX

derive instance Eq NormalFormat
derive instance Generic NormalFormat _
instance Show NormalFormat where show = genericShow

normalFormatFromString :: String -> Maybe NormalFormat
normalFormatFromString = case _ of
  "opengl" -> Just NfOpenGL
  "directx" -> Just NfDirectX
  _ -> Nothing

--------------------------------------------------------------------------------
-- Generated Layer
--------------------------------------------------------------------------------

data GenerationType = GenDepth | GenNormal | GenEdge | GenSegment | GenInpaint | GenCustom

derive instance Eq GenerationType
derive instance Generic GenerationType _
instance Show GenerationType where show = genericShow

generationTypeFromString :: String -> Maybe GenerationType
generationTypeFromString = case _ of
  "depth" -> Just GenDepth
  "normal" -> Just GenNormal
  "edge" -> Just GenEdge
  "segment" -> Just GenSegment
  "inpaint" -> Just GenInpaint
  "custom" -> Just GenCustom
  _ -> Nothing

data GenerationStatus = StatusPending | StatusGenerating | StatusComplete | StatusError

derive instance Eq GenerationStatus
derive instance Generic GenerationStatus _
instance Show GenerationStatus where show = genericShow

generationStatusFromString :: String -> Maybe GenerationStatus
generationStatusFromString = case _ of
  "pending" -> Just StatusPending
  "generating" -> Just StatusGenerating
  "complete" -> Just StatusComplete
  "error" -> Just StatusError
  _ -> Nothing

--------------------------------------------------------------------------------
-- Generated Map
--------------------------------------------------------------------------------

data GeneratedMapType = GmDepth | GmNormal | GmEdge | GmSegment | GmPose | GmFlow

derive instance Eq GeneratedMapType
derive instance Generic GeneratedMapType _
instance Show GeneratedMapType where show = genericShow

generatedMapTypeFromString :: String -> Maybe GeneratedMapType
generatedMapTypeFromString = case _ of
  "depth" -> Just GmDepth
  "normal" -> Just GmNormal
  "edge" -> Just GmEdge
  "segment" -> Just GmSegment
  "pose" -> Just GmPose
  "flow" -> Just GmFlow
  _ -> Nothing
