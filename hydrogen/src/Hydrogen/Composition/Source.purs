-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // composition // source
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Source Layers — What generates pixels.
-- |
-- | This is the leader module. Sources are organized by category in submodules.
-- |
-- | ANY data that can be visualized is a Source type:
-- | - A database cell → Metric widget → pixels
-- | - A point cloud → 3D render → pixels  
-- | - An audio waveform → visualization → pixels
-- | - A diffusion prompt → neural sampler → pixels

module Hydrogen.Composition.Source
  ( -- * Core Source Type
    Source(..)
  , SourceCategory(..)
  , sourceCategory
  
  -- * Re-exports
  , module ReExportMedia
  , module ReExportVector
  , module ReExportThreeD
  , module ReExportGenerative
  , module ReExportData
  , module ReExportInteractive
  
  -- * Element Bridge
  , element
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- Element.Core for pure data elements
import Hydrogen.Element.Core as Element

-- Category modules with qualified imports
import Hydrogen.Composition.Source.Media as Media
import Hydrogen.Composition.Source.Vector as Vector
import Hydrogen.Composition.Source.ThreeD as ThreeD
import Hydrogen.Composition.Source.Generative as Generative
import Hydrogen.Composition.Source.Data as Data
import Hydrogen.Composition.Source.Interactive as Interactive

-- Re-exports
import Hydrogen.Composition.Source.Media 
  ( ImageSpec, ImageFit(..), image
  , VideoSpec, video
  , AudioSpec, AudioVisualization(..), audio
  , SVGSpec, svg
  , DepthSpec, DepthVisualization(..), depth
  , NormalSpec, NormalVisualization(..), normal
  ) as ReExportMedia

import Hydrogen.Composition.Source.Vector
  ( SplineSpec, SplineFill(..), spline
  , ShapeSpec, ShapeGenerator(..), shapeRect, shapeEllipse, shapeStar, shapePolygon
  , PathSpec, path
  , TextSpec, TextAnimator(..), TextRangeSelector(..), text
  ) as ReExportVector

import Hydrogen.Composition.Source.ThreeD
  ( ModelSpec, ModelFormat(..), model
  , PointCloudSpec, PointCloudFormat(..), PointCloudColoring(..), pointCloud
  , CameraSpec, CameraType(..), camera
  , LightSpec, LightType(..), light
  , ParticleSystemSpec, EmitterShape(..), ParticleForce(..), particleSystem
  ) as ReExportThreeD

import Hydrogen.Composition.Source.Generative
  ( ProceduralSpec, ShaderRef(..), procedural
  , NoiseSpec, NoiseType(..), noise
  , DiffusionSpec, Sampler(..), Scheduler(..), ModelRef(..), PromptEmbedding(..)
  , DiffusionSize, diffusionSize, diffusion
  , ControlNetSpec, ControlNetType(..), controlNet
  , GeneratedMapSpec, GeneratedMapType(..), generatedMap
  ) as ReExportGenerative

import Hydrogen.Composition.Source.Data
  ( QueryRef(..), DataRef(..)
  , ChartSpec, ChartType(..), chart
  , TableSpec, table
  , GraphSpec, GraphLayout(..), graph
  , MapSpec, MapStyle(..), geoMap
  , MetricSpec, MetricStyle(..), metric
  , TimelineSpec, timeline
  , HeatmapSpec, HeatmapColorScale(..), heatmap
  , TreeSpec, TreeLayout(..), tree
  , SankeySpec, sankey
  , FunnelSpec, funnel
  ) as ReExportData

import Hydrogen.Composition.Source.Interactive
  ( WidgetSpec, WidgetRef(..), widget
  , FormSpec, FormField(..), form
  , CanvasSpec, canvas
  , TerminalSpec, terminal
  , CodeEditorSpec, code
  , MarkdownSpec, markdown
  , BrowserSpec, browser
  , PDFSpec, pdf
  ) as ReExportInteractive

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // source category
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Source categories — organizational grouping.
data SourceCategory
  = CategoryMedia       -- Image, Video, Audio, SVG, Depth, Normal
  | CategoryVector      -- Spline, Shape, Path, Text
  | CategoryThreeD      -- Model, PointCloud, Camera, Light, Particles
  | CategoryGenerative  -- Procedural, Noise, Diffusion, Generated
  | CategoryData        -- Chart, Table, Graph, Map, Metric, etc.
  | CategoryInteractive -- Widget, Form, Canvas, Terminal, Code, etc.
  | CategoryElement     -- Element.Core pure data shapes

derive instance eqSourceCategory :: Eq SourceCategory

instance showSourceCategory :: Show SourceCategory where
  show CategoryMedia = "media"
  show CategoryVector = "vector"
  show CategoryThreeD = "3d"
  show CategoryGenerative = "generative"
  show CategoryData = "data"
  show CategoryInteractive = "interactive"
  show CategoryElement = "element"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // source type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Source — what generates pixels in a composition layer.
data Source
  -- Media (6)
  = SourceImage Media.ImageSpec
  | SourceVideo Media.VideoSpec
  | SourceAudio Media.AudioSpec
  | SourceSVG Media.SVGSpec
  | SourceDepth Media.DepthSpec
  | SourceNormal Media.NormalSpec
  -- Vector (4)
  | SourceSpline Vector.SplineSpec
  | SourceShape Vector.ShapeSpec
  | SourcePath Vector.PathSpec
  | SourceText Vector.TextSpec
  -- 3D (5)
  | SourceModel ThreeD.ModelSpec
  | SourcePointCloud ThreeD.PointCloudSpec
  | SourceCamera ThreeD.CameraSpec
  | SourceLight ThreeD.LightSpec
  | SourceParticles ThreeD.ParticleSystemSpec
  -- Generative (4)
  | SourceProcedural Generative.ProceduralSpec
  | SourceNoise Generative.NoiseSpec
  | SourceDiffusion Generative.DiffusionSpec
  | SourceGenerated Generative.GeneratedMapSpec
  -- Data (10)
  | SourceChart Data.ChartSpec
  | SourceTable Data.TableSpec
  | SourceGraph Data.GraphSpec
  | SourceMap Data.MapSpec
  | SourceMetric Data.MetricSpec
  | SourceTimeline Data.TimelineSpec
  | SourceHeatmap Data.HeatmapSpec
  | SourceTree Data.TreeSpec
  | SourceSankey Data.SankeySpec
  | SourceFunnel Data.FunnelSpec
  -- Interactive (8)
  | SourceWidget Interactive.WidgetSpec
  | SourceForm Interactive.FormSpec
  | SourceCanvas Interactive.CanvasSpec
  | SourceTerminal Interactive.TerminalSpec
  | SourceCode Interactive.CodeEditorSpec
  | SourceMarkdown Interactive.MarkdownSpec
  | SourceBrowser Interactive.BrowserSpec
  | SourcePDF Interactive.PDFSpec
  -- Element (1) — Bridge to Element.Core pure data shapes
  | SourceElement Element.Element

derive instance eqSource :: Eq Source

instance showSource :: Show Source where
  show (SourceImage _) = "SourceImage"
  show (SourceVideo _) = "SourceVideo"
  show (SourceAudio _) = "SourceAudio"
  show (SourceSVG _) = "SourceSVG"
  show (SourceDepth _) = "SourceDepth"
  show (SourceNormal _) = "SourceNormal"
  show (SourceSpline _) = "SourceSpline"
  show (SourceShape _) = "SourceShape"
  show (SourcePath _) = "SourcePath"
  show (SourceText _) = "SourceText"
  show (SourceModel _) = "SourceModel"
  show (SourcePointCloud _) = "SourcePointCloud"
  show (SourceCamera _) = "SourceCamera"
  show (SourceLight _) = "SourceLight"
  show (SourceParticles _) = "SourceParticles"
  show (SourceProcedural _) = "SourceProcedural"
  show (SourceNoise _) = "SourceNoise"
  show (SourceDiffusion _) = "SourceDiffusion"
  show (SourceGenerated _) = "SourceGenerated"
  show (SourceChart _) = "SourceChart"
  show (SourceTable _) = "SourceTable"
  show (SourceGraph _) = "SourceGraph"
  show (SourceMap _) = "SourceMap"
  show (SourceMetric _) = "SourceMetric"
  show (SourceTimeline _) = "SourceTimeline"
  show (SourceHeatmap _) = "SourceHeatmap"
  show (SourceTree _) = "SourceTree"
  show (SourceSankey _) = "SourceSankey"
  show (SourceFunnel _) = "SourceFunnel"
  show (SourceWidget _) = "SourceWidget"
  show (SourceForm _) = "SourceForm"
  show (SourceCanvas _) = "SourceCanvas"
  show (SourceTerminal _) = "SourceTerminal"
  show (SourceCode _) = "SourceCode"
  show (SourceMarkdown _) = "SourceMarkdown"
  show (SourceBrowser _) = "SourceBrowser"
  show (SourcePDF _) = "SourcePDF"
  show (SourceElement _) = "SourceElement"

-- | Get the category of a source.
sourceCategory :: Source -> SourceCategory
sourceCategory (SourceImage _) = CategoryMedia
sourceCategory (SourceVideo _) = CategoryMedia
sourceCategory (SourceAudio _) = CategoryMedia
sourceCategory (SourceSVG _) = CategoryMedia
sourceCategory (SourceDepth _) = CategoryMedia
sourceCategory (SourceNormal _) = CategoryMedia
sourceCategory (SourceSpline _) = CategoryVector
sourceCategory (SourceShape _) = CategoryVector
sourceCategory (SourcePath _) = CategoryVector
sourceCategory (SourceText _) = CategoryVector
sourceCategory (SourceModel _) = CategoryThreeD
sourceCategory (SourcePointCloud _) = CategoryThreeD
sourceCategory (SourceCamera _) = CategoryThreeD
sourceCategory (SourceLight _) = CategoryThreeD
sourceCategory (SourceParticles _) = CategoryThreeD
sourceCategory (SourceProcedural _) = CategoryGenerative
sourceCategory (SourceNoise _) = CategoryGenerative
sourceCategory (SourceDiffusion _) = CategoryGenerative
sourceCategory (SourceGenerated _) = CategoryGenerative
sourceCategory (SourceChart _) = CategoryData
sourceCategory (SourceTable _) = CategoryData
sourceCategory (SourceGraph _) = CategoryData
sourceCategory (SourceMap _) = CategoryData
sourceCategory (SourceMetric _) = CategoryData
sourceCategory (SourceTimeline _) = CategoryData
sourceCategory (SourceHeatmap _) = CategoryData
sourceCategory (SourceTree _) = CategoryData
sourceCategory (SourceSankey _) = CategoryData
sourceCategory (SourceFunnel _) = CategoryData
sourceCategory (SourceWidget _) = CategoryInteractive
sourceCategory (SourceForm _) = CategoryInteractive
sourceCategory (SourceCanvas _) = CategoryInteractive
sourceCategory (SourceTerminal _) = CategoryInteractive
sourceCategory (SourceCode _) = CategoryInteractive
sourceCategory (SourceMarkdown _) = CategoryInteractive
sourceCategory (SourceBrowser _) = CategoryInteractive
sourceCategory (SourcePDF _) = CategoryInteractive
sourceCategory (SourceElement _) = CategoryElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // element constructor
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a source from an Element.Core value.
-- |
-- | This bridges the pure Element type to the composition system.
-- | Element values (Rectangle, Ellipse, Path, Text, Group) become
-- | pixel sources that the composition pipeline can render.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Core as E
-- | import Hydrogen.Composition.Source (element, SourceElement)
-- |
-- | myLayer = layer nodeId "shape" (element myRectangle)
-- | ```
element :: Element.Element -> Source
element = SourceElement
