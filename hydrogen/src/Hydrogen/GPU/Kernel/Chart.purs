-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // kernel // chart
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Rendering Kernels — Waveforms, Trends, and Data Visualization
-- |
-- | ## Purpose
-- |
-- | High-performance chart rendering for:
-- |
-- | - Medical dashboards (ECG waveforms, vital sign trends)
-- | - Audio workstations (waveform display, spectrum analyzers)
-- | - Financial dashboards (real-time price charts)
-- | - Industrial monitoring (sensor data visualization)
-- |
-- | ## Waveform Rendering Pipeline
-- |
-- | ```
-- | Sample Buffer → Downsample → Line/Fill Render → Anti-aliasing
-- |                                    ↓
-- |                              Threshold Overlay
-- |                                    ↓
-- |                              Composited Output
-- | ```
-- |
-- | ## Medical Display Requirements (IEC 60601-1)
-- |
-- | - Minimum 25mm/s sweep speed for ECG
-- | - 1mV = 10mm calibration
-- | - Grid overlay with major/minor divisions
-- | - Color-coded alarm thresholds
-- | - Signal quality indicators
-- |
-- | ## Audio Display Requirements
-- |
-- | - Waveform with peak hold
-- | - RMS envelope overlay
-- | - Zero-crossing indicators
-- | - Stereo correlation
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Chart kernels are deterministic:
-- | - Same samples + config = same pixels (always)
-- | - Sample buffers are content-addressed
-- | - Downsampling is pure function
-- | - Multiple agents can share visualization cache

module Hydrogen.GPU.Kernel.Chart
  ( -- * Core Types
    ChartKernel
      ( KernelWaveform
      , KernelSparkline
      , KernelLinePlot
      , KernelAreaFill
      , KernelBarChart
      , KernelThresholdOverlay
      , KernelGridOverlay
      , KernelChartSequence
      , KernelChartNoop
      )
  , KernelInput
      ( InputSampleBuffer
      , InputTexture
      , InputUniform
      , InputPrevious
      )
  , KernelOutput
      ( OutputTexture
      , OutputBuffer
      , OutputScreen
      )
  , WorkgroupSize
  , DispatchSize
  
  -- * Waveform Rendering
  , WaveformKernel
  , WaveformStyle
      ( WaveformLine
      , WaveformFilled
      , WaveformBars
      , WaveformPoints
      , WaveformMinMax
      )
  , WaveformConfig
  , mkWaveformKernel
  
  -- * Sparkline (Inline Charts)
  , SparklineKernel
  , SparklineStyle
      ( SparklineLine
      , SparklineArea
      , SparklineBar
      , SparklineWinLoss
      )
  , SparklineConfig
  , mkSparklineKernel
  
  -- * Line Plot (Multi-series)
  , LinePlotKernel
  , LineStyle
      ( LineSolid
      , LineDashed
      , LineDotted
      , LineStepBefore
      , LineStepAfter
      , LineCardinal
      , LineMonotone
      )
  , SeriesConfig
  , ChartColor
  , mkLinePlotKernel
  
  -- * Area Fill
  , AreaFillKernel
  , FillMode
      ( FillToZero
      , FillToMin
      , FillBetween
      , FillGradient
      )
  , GradientDirection
      ( GradientVertical
      , GradientHorizontal
      )
  , mkAreaFillKernel
  
  -- * Bar Chart
  , BarChartKernel
  , BarOrientation
      ( BarVertical
      , BarHorizontal
      )
  , BarGrouping
      ( BarStacked
      , BarGrouped
      , BarOverlapped
      )
  , mkBarChartKernel
  
  -- * Threshold Overlay
  , ThresholdOverlayKernel
  , ThresholdZone
  , ThresholdSeverity
      ( SeverityNormal
      , SeverityWarning
      , SeverityCritical
      , SeverityDanger
      )
  , mkThresholdOverlayKernel
  
  -- * Grid Overlay
  , GridOverlayKernel
  , GridStyle
      ( GridLines
      , GridDots
      , GridDashes
      )
  , GridDivisions
  , mkGridOverlayKernel
  
  -- * Chart Configuration
  , ChartKernelConfig
  , defaultChartKernelConfig
  , medicalECGConfig
  , audioWaveformConfig
  , financialChartConfig
  
  -- * Kernel Composition
  , sequenceChartKernels
  , conditionalChartKernel
  
  -- * Dispatch Calculation
  , computeChartWorkgroupSize
  , computeChartDispatchSize
  , estimateChartKernelCost
  
  -- * Presets
  , ecgMonitorPipeline
  , vitalSignsTrendPipeline
  , audioWaveformPipeline
  , spectrumAnalyzerPipeline
  , stockChartPipeline
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , negate
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (<>)
  , (&&)
  , otherwise
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for chart compute dispatch
type WorkgroupSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Dispatch dimensions
type DispatchSize =
  { x :: Int
  , y :: Int
  , z :: Int
  }

-- | Chart kernel input source
data KernelInput
  = InputSampleBuffer Int    -- Sample data buffer
  | InputTexture Int         -- Texture input
  | InputUniform Int         -- Uniform buffer
  | InputPrevious            -- Previous kernel output

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputSampleBuffer i) = "(InputSampleBuffer " <> show i <> ")"
  show (InputTexture i) = "(InputTexture " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"

-- | Chart kernel output target
data KernelOutput
  = OutputTexture Int        -- Render to texture
  | OutputBuffer Int         -- Write to buffer
  | OutputScreen             -- Final screen output

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputScreen = "OutputScreen"

-- | RGBA color for charts
type ChartColor =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | Chart kernel configuration
type ChartKernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int
  , height :: Int
  , backgroundColor :: ChartColor
  }

-- | Default chart kernel configuration
defaultChartKernelConfig :: ChartKernelConfig
defaultChartKernelConfig =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width: 800
  , height: 400
  , backgroundColor: { r: 0.0, g: 0.0, b: 0.0, a: 1.0 }
  }

-- | Medical ECG configuration (IEC 60601-1 compliant)
medicalECGConfig :: Int -> Int -> ChartKernelConfig
medicalECGConfig width height =
  { workgroupSize: { x: 16, y: 1, z: 1 }  -- Optimized for horizontal sweep
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 0.0, g: 0.0, b: 0.0, a: 1.0 }  -- Black background
  }

-- | Audio waveform configuration
audioWaveformConfig :: Int -> Int -> ChartKernelConfig
audioWaveformConfig width height =
  { workgroupSize: { x: 32, y: 1, z: 1 }  -- Wide for sample processing
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 0.1, g: 0.1, b: 0.1, a: 1.0 }  -- Dark gray
  }

-- | Financial chart configuration
financialChartConfig :: Int -> Int -> ChartKernelConfig
financialChartConfig width height =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputSampleBuffer 0
  , output: OutputScreen
  , width
  , height
  , backgroundColor: { r: 1.0, g: 1.0, b: 1.0, a: 1.0 }  -- White background
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // chart kernel adt
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chart rendering kernel variants
data ChartKernel
  = KernelWaveform WaveformKernel
  | KernelSparkline SparklineKernel
  | KernelLinePlot LinePlotKernel
  | KernelAreaFill AreaFillKernel
  | KernelBarChart BarChartKernel
  | KernelThresholdOverlay ThresholdOverlayKernel
  | KernelGridOverlay GridOverlayKernel
  | KernelChartSequence (Array ChartKernel)
  | KernelChartNoop

derive instance eqChartKernel :: Eq ChartKernel

instance showChartKernel :: Show ChartKernel where
  show (KernelWaveform k) = "(KernelWaveform " <> show k <> ")"
  show (KernelSparkline k) = "(KernelSparkline " <> show k <> ")"
  show (KernelLinePlot k) = "(KernelLinePlot " <> show k <> ")"
  show (KernelAreaFill k) = "(KernelAreaFill " <> show k <> ")"
  show (KernelBarChart k) = "(KernelBarChart " <> show k <> ")"
  show (KernelThresholdOverlay k) = "(KernelThresholdOverlay " <> show k <> ")"
  show (KernelGridOverlay k) = "(KernelGridOverlay " <> show k <> ")"
  show (KernelChartSequence _) = "(KernelChartSequence [...])"
  show KernelChartNoop = "KernelChartNoop"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // waveform rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Waveform display style
data WaveformStyle
  = WaveformLine           -- Simple line connecting samples
  | WaveformFilled         -- Filled area from baseline
  | WaveformBars           -- Vertical bars for each sample
  | WaveformPoints         -- Discrete points only
  | WaveformMinMax         -- Min/max envelope (for zoomed out)

derive instance eqWaveformStyle :: Eq WaveformStyle

instance showWaveformStyle :: Show WaveformStyle where
  show WaveformLine = "WaveformLine"
  show WaveformFilled = "WaveformFilled"
  show WaveformBars = "WaveformBars"
  show WaveformPoints = "WaveformPoints"
  show WaveformMinMax = "WaveformMinMax"

-- | Waveform configuration
type WaveformConfig =
  { sampleCount :: Int           -- Number of samples to display
  , channelCount :: Int          -- Mono (1) or Stereo (2+)
  , minValue :: Number           -- Y-axis minimum
  , maxValue :: Number           -- Y-axis maximum
  , lineWidth :: Number          -- Line thickness (pixels)
  , antiAliasing :: Boolean      -- Enable anti-aliasing
  }

-- | Waveform rendering kernel
newtype WaveformKernel = WaveformKernel
  { style :: WaveformStyle
  , waveformConfig :: WaveformConfig
  , color :: ChartColor
  , peakHold :: Boolean          -- Show peak indicators
  , peakDecay :: Number          -- Peak decay rate (dB/s)
  , rmsOverlay :: Boolean        -- Show RMS envelope
  , zeroCrossing :: Boolean      -- Show zero crossing markers
  , config :: ChartKernelConfig
  }

derive instance eqWaveformKernel :: Eq WaveformKernel

instance showWaveformKernel :: Show WaveformKernel where
  show (WaveformKernel k) = 
    "(WaveformKernel style:" <> show k.style <> 
    " samples:" <> show k.waveformConfig.sampleCount <> ")"

-- | Create waveform kernel
mkWaveformKernel 
  :: WaveformStyle 
  -> WaveformConfig 
  -> ChartColor 
  -> ChartKernelConfig 
  -> WaveformKernel
mkWaveformKernel style waveformConfig color config =
  WaveformKernel
    { style
    , waveformConfig
    , color
    , peakHold: false
    , peakDecay: 12.0
    , rmsOverlay: false
    , zeroCrossing: false
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sparkline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sparkline display style
data SparklineStyle
  = SparklineLine          -- Simple line chart
  | SparklineArea          -- Filled area chart
  | SparklineBar           -- Mini bar chart
  | SparklineWinLoss       -- Binary up/down bars

derive instance eqSparklineStyle :: Eq SparklineStyle

instance showSparklineStyle :: Show SparklineStyle where
  show SparklineLine = "SparklineLine"
  show SparklineArea = "SparklineArea"
  show SparklineBar = "SparklineBar"
  show SparklineWinLoss = "SparklineWinLoss"

-- | Sparkline configuration
type SparklineConfig =
  { dataPoints :: Int            -- Number of data points
  , showMinMax :: Boolean        -- Highlight min/max points
  , showLast :: Boolean          -- Highlight last point
  , normalizeRange :: Boolean    -- Auto-scale to data range
  }

-- | Sparkline kernel
newtype SparklineKernel = SparklineKernel
  { style :: SparklineStyle
  , sparklineConfig :: SparklineConfig
  , lineColor :: ChartColor
  , fillColor :: ChartColor
  , minColor :: ChartColor       -- Color for minimum point
  , maxColor :: ChartColor       -- Color for maximum point
  , lastColor :: ChartColor      -- Color for last point
  , config :: ChartKernelConfig
  }

derive instance eqSparklineKernel :: Eq SparklineKernel

instance showSparklineKernel :: Show SparklineKernel where
  show (SparklineKernel k) = 
    "(SparklineKernel style:" <> show k.style <> 
    " points:" <> show k.sparklineConfig.dataPoints <> ")"

-- | Create sparkline kernel
mkSparklineKernel 
  :: SparklineStyle 
  -> SparklineConfig 
  -> ChartColor 
  -> ChartKernelConfig 
  -> SparklineKernel
mkSparklineKernel style sparklineConfig lineColor config =
  SparklineKernel
    { style
    , sparklineConfig
    , lineColor
    , fillColor: lineColor { a = 0.3 }
    , minColor: { r: 1.0, g: 0.0, b: 0.0, a: 1.0 }
    , maxColor: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }
    , lastColor: { r: 0.0, g: 0.5, b: 1.0, a: 1.0 }
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // line plot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line interpolation style
data LineStyle
  = LineSolid              -- Solid line
  | LineDashed             -- Dashed line
  | LineDotted             -- Dotted line
  | LineStepBefore         -- Step function (value before point)
  | LineStepAfter          -- Step function (value after point)
  | LineCardinal           -- Cardinal spline interpolation
  | LineMonotone           -- Monotone cubic interpolation

derive instance eqLineStyle :: Eq LineStyle

instance showLineStyle :: Show LineStyle where
  show LineSolid = "LineSolid"
  show LineDashed = "LineDashed"
  show LineDotted = "LineDotted"
  show LineStepBefore = "LineStepBefore"
  show LineStepAfter = "LineStepAfter"
  show LineCardinal = "LineCardinal"
  show LineMonotone = "LineMonotone"

-- | Series configuration for multi-line plots
type SeriesConfig =
  { seriesId :: Int              -- Unique series identifier
  , label :: String              -- Series name
  , color :: ChartColor          -- Line color
  , lineStyle :: LineStyle       -- Line style
  , lineWidth :: Number          -- Line thickness
  , showPoints :: Boolean        -- Show data points
  , pointRadius :: Number        -- Data point size
  }

-- | Line plot kernel
newtype LinePlotKernel = LinePlotKernel
  { series :: Array SeriesConfig
  , dataPointCount :: Int        -- Points per series
  , xAxisMin :: Number           -- X-axis minimum
  , xAxisMax :: Number           -- X-axis maximum
  , yAxisMin :: Number           -- Y-axis minimum
  , yAxisMax :: Number           -- Y-axis maximum
  , antiAliasing :: Boolean
  , config :: ChartKernelConfig
  }

derive instance eqLinePlotKernel :: Eq LinePlotKernel

instance showLinePlotKernel :: Show LinePlotKernel where
  show (LinePlotKernel k) = 
    "(LinePlotKernel series:" <> show (Array.length k.series) <> 
    " points:" <> show k.dataPointCount <> ")"

-- | Create line plot kernel
mkLinePlotKernel 
  :: Array SeriesConfig 
  -> Int 
  -> ChartKernelConfig 
  -> LinePlotKernel
mkLinePlotKernel series dataPointCount config =
  LinePlotKernel
    { series
    , dataPointCount
    , xAxisMin: 0.0
    , xAxisMax: Int.toNumber dataPointCount
    , yAxisMin: 0.0
    , yAxisMax: 100.0
    , antiAliasing: true
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // area fill
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fill mode for area charts
data FillMode
  = FillToZero             -- Fill from line to zero
  | FillToMin              -- Fill from line to minimum
  | FillBetween            -- Fill between two series
  | FillGradient           -- Gradient fill

derive instance eqFillMode :: Eq FillMode

instance showFillMode :: Show FillMode where
  show FillToZero = "FillToZero"
  show FillToMin = "FillToMin"
  show FillBetween = "FillBetween"
  show FillGradient = "FillGradient"

-- | Gradient direction
data GradientDirection
  = GradientVertical       -- Top to bottom
  | GradientHorizontal     -- Left to right

derive instance eqGradientDirection :: Eq GradientDirection

instance showGradientDirection :: Show GradientDirection where
  show GradientVertical = "GradientVertical"
  show GradientHorizontal = "GradientHorizontal"

-- | Area fill kernel
newtype AreaFillKernel = AreaFillKernel
  { fillMode :: FillMode
  , primaryColor :: ChartColor
  , secondaryColor :: ChartColor  -- For gradient or fill-between
  , gradientDirection :: GradientDirection
  , opacity :: Number
  , seriesIndex :: Int           -- Which series to fill
  , secondSeriesIndex :: Int     -- For fill-between mode
  , config :: ChartKernelConfig
  }

derive instance eqAreaFillKernel :: Eq AreaFillKernel

instance showAreaFillKernel :: Show AreaFillKernel where
  show (AreaFillKernel k) = 
    "(AreaFillKernel mode:" <> show k.fillMode <> ")"

-- | Create area fill kernel
mkAreaFillKernel 
  :: FillMode 
  -> ChartColor 
  -> Number 
  -> ChartKernelConfig 
  -> AreaFillKernel
mkAreaFillKernel fillMode primaryColor opacity config =
  AreaFillKernel
    { fillMode
    , primaryColor
    , secondaryColor: primaryColor { a = 0.0 }
    , gradientDirection: GradientVertical
    , opacity
    , seriesIndex: 0
    , secondSeriesIndex: 1
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bar orientation
data BarOrientation
  = BarVertical            -- Vertical bars
  | BarHorizontal          -- Horizontal bars

derive instance eqBarOrientation :: Eq BarOrientation

instance showBarOrientation :: Show BarOrientation where
  show BarVertical = "BarVertical"
  show BarHorizontal = "BarHorizontal"

-- | Bar grouping mode
data BarGrouping
  = BarStacked             -- Stacked bars
  | BarGrouped             -- Grouped side-by-side
  | BarOverlapped          -- Overlapping with transparency

derive instance eqBarGrouping :: Eq BarGrouping

instance showBarGrouping :: Show BarGrouping where
  show BarStacked = "BarStacked"
  show BarGrouped = "BarGrouped"
  show BarOverlapped = "BarOverlapped"

-- | Bar chart kernel
newtype BarChartKernel = BarChartKernel
  { orientation :: BarOrientation
  , grouping :: BarGrouping
  , barColors :: Array ChartColor
  , barWidth :: Number           -- Width as fraction of available space
  , barSpacing :: Number         -- Space between bars
  , cornerRadius :: Number       -- Rounded corners
  , showValues :: Boolean        -- Show value labels
  , categoryCount :: Int         -- Number of categories
  , seriesCount :: Int           -- Number of series
  , config :: ChartKernelConfig
  }

derive instance eqBarChartKernel :: Eq BarChartKernel

instance showBarChartKernel :: Show BarChartKernel where
  show (BarChartKernel k) = 
    "(BarChartKernel orientation:" <> show k.orientation <> 
    " grouping:" <> show k.grouping <> ")"

-- | Create bar chart kernel
mkBarChartKernel 
  :: BarOrientation 
  -> BarGrouping 
  -> Array ChartColor 
  -> Int 
  -> Int 
  -> ChartKernelConfig 
  -> BarChartKernel
mkBarChartKernel orientation grouping barColors categoryCount seriesCount config =
  BarChartKernel
    { orientation
    , grouping
    , barColors
    , barWidth: 0.8
    , barSpacing: 0.1
    , cornerRadius: 0.0
    , showValues: false
    , categoryCount
    , seriesCount
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // threshold overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Threshold severity level
data ThresholdSeverity
  = SeverityNormal         -- Normal range (green)
  | SeverityWarning        -- Warning range (yellow)
  | SeverityCritical       -- Critical range (orange)
  | SeverityDanger         -- Danger range (red)

derive instance eqThresholdSeverity :: Eq ThresholdSeverity

instance showThresholdSeverity :: Show ThresholdSeverity where
  show SeverityNormal = "SeverityNormal"
  show SeverityWarning = "SeverityWarning"
  show SeverityCritical = "SeverityCritical"
  show SeverityDanger = "SeverityDanger"

-- | Threshold zone definition
type ThresholdZone =
  { minValue :: Number           -- Zone minimum
  , maxValue :: Number           -- Zone maximum
  , severity :: ThresholdSeverity
  , color :: ChartColor          -- Override color (or use severity default)
  , label :: String              -- Zone label
  , showLabel :: Boolean         -- Display label
  }

-- | Threshold overlay kernel
newtype ThresholdOverlayKernel = ThresholdOverlayKernel
  { zones :: Array ThresholdZone
  , fillOpacity :: Number        -- Zone fill opacity
  , showBorders :: Boolean       -- Show zone borders
  , borderWidth :: Number        -- Border line width
  , animated :: Boolean          -- Animate zone transitions
  , pulseOnViolation :: Boolean  -- Pulse when value in danger zone
  , config :: ChartKernelConfig
  }

derive instance eqThresholdOverlayKernel :: Eq ThresholdOverlayKernel

instance showThresholdOverlayKernel :: Show ThresholdOverlayKernel where
  show (ThresholdOverlayKernel k) = 
    "(ThresholdOverlayKernel zones:" <> show (Array.length k.zones) <> ")"

-- | Create threshold overlay kernel
mkThresholdOverlayKernel 
  :: Array ThresholdZone 
  -> Number 
  -> ChartKernelConfig 
  -> ThresholdOverlayKernel
mkThresholdOverlayKernel zones fillOpacity config =
  ThresholdOverlayKernel
    { zones
    , fillOpacity
    , showBorders: true
    , borderWidth: 1.0
    , animated: false
    , pulseOnViolation: false
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // grid overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid line style
data GridStyle
  = GridLines              -- Solid lines
  | GridDots               -- Dotted lines
  | GridDashes             -- Dashed lines

derive instance eqGridStyle :: Eq GridStyle

instance showGridStyle :: Show GridStyle where
  show GridLines = "GridLines"
  show GridDots = "GridDots"
  show GridDashes = "GridDashes"

-- | Grid divisions
type GridDivisions =
  { majorX :: Int                -- Major divisions on X axis
  , majorY :: Int                -- Major divisions on Y axis
  , minorX :: Int                -- Minor divisions between major X
  , minorY :: Int                -- Minor divisions between major Y
  }

-- | Grid overlay kernel
newtype GridOverlayKernel = GridOverlayKernel
  { style :: GridStyle
  , divisions :: GridDivisions
  , majorColor :: ChartColor
  , minorColor :: ChartColor
  , majorWidth :: Number         -- Major line width
  , minorWidth :: Number         -- Minor line width
  , showLabels :: Boolean        -- Show axis labels
  , labelColor :: ChartColor
  , config :: ChartKernelConfig
  }

derive instance eqGridOverlayKernel :: Eq GridOverlayKernel

instance showGridOverlayKernel :: Show GridOverlayKernel where
  show (GridOverlayKernel k) = 
    "(GridOverlayKernel style:" <> show k.style <> ")"

-- | Create grid overlay kernel
mkGridOverlayKernel 
  :: GridStyle 
  -> GridDivisions 
  -> ChartKernelConfig 
  -> GridOverlayKernel
mkGridOverlayKernel style divisions config =
  GridOverlayKernel
    { style
    , divisions
    , majorColor: { r: 0.5, g: 0.5, b: 0.5, a: 0.5 }
    , minorColor: { r: 0.3, g: 0.3, b: 0.3, a: 0.3 }
    , majorWidth: 1.0
    , minorWidth: 0.5
    , showLabels: true
    , labelColor: { r: 0.7, g: 0.7, b: 0.7, a: 1.0 }
    , config
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence multiple chart kernels
sequenceChartKernels :: Array ChartKernel -> ChartKernel
sequenceChartKernels kernels =
  case Array.length kernels of
    0 -> KernelChartNoop
    1 -> case Array.head kernels of
           Nothing -> KernelChartNoop
           Just k -> k
    _ -> KernelChartSequence kernels

-- | Conditional chart kernel execution
conditionalChartKernel 
  :: Boolean 
  -> ChartKernel 
  -> ChartKernel 
  -> ChartKernel
conditionalChartKernel condition thenKernel elseKernel =
  if condition
    then thenKernel
    else elseKernel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // dispatch calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute workgroup size for chart kernel
computeChartWorkgroupSize :: ChartKernel -> WorkgroupSize
computeChartWorkgroupSize kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) -> k.config.workgroupSize
    KernelSparkline (SparklineKernel k) -> k.config.workgroupSize
    KernelLinePlot (LinePlotKernel k) -> k.config.workgroupSize
    KernelAreaFill (AreaFillKernel k) -> k.config.workgroupSize
    KernelBarChart (BarChartKernel k) -> k.config.workgroupSize
    KernelThresholdOverlay (ThresholdOverlayKernel k) -> k.config.workgroupSize
    KernelGridOverlay (GridOverlayKernel k) -> k.config.workgroupSize
    KernelChartSequence kernels -> 
      case Array.head kernels of
        Nothing -> { x: 16, y: 16, z: 1 }
        Just k -> computeChartWorkgroupSize k
    KernelChartNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size for chart kernel
computeChartDispatchSize :: ChartKernel -> DispatchSize
computeChartDispatchSize kernel =
  let
    workgroup = computeChartWorkgroupSize kernel
    dims = getChartKernelDimensions kernel
    divCeil a b = (a + b - 1) / b
  in
    { x: divCeil dims.width workgroup.x
    , y: divCeil dims.height workgroup.y
    , z: 1
    }

-- | Get kernel dimensions
getChartKernelDimensions :: ChartKernel -> { width :: Int, height :: Int }
getChartKernelDimensions kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelSparkline (SparklineKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelLinePlot (LinePlotKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelAreaFill (AreaFillKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelBarChart (BarChartKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelThresholdOverlay (ThresholdOverlayKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelGridOverlay (GridOverlayKernel k) -> 
      { width: k.config.width, height: k.config.height }
    KernelChartSequence kernels ->
      case Array.head kernels of
        Nothing -> { width: 0, height: 0 }
        Just k -> getChartKernelDimensions k
    KernelChartNoop -> { width: 0, height: 0 }

-- | Estimate kernel execution cost (microseconds)
estimateChartKernelCost :: ChartKernel -> Number
estimateChartKernelCost kernel =
  case kernel of
    KernelWaveform (WaveformKernel k) ->
      -- Waveform: ~2μs per 1K samples
      Int.toNumber k.waveformConfig.sampleCount / 500.0
    KernelSparkline (SparklineKernel k) ->
      -- Sparkline: ~1μs per point
      Int.toNumber k.sparklineConfig.dataPoints
    KernelLinePlot (LinePlotKernel k) ->
      -- Line plot: ~5μs per series per 1K points
      Int.toNumber (Array.length k.series * k.dataPointCount) / 200.0
    KernelAreaFill (AreaFillKernel k) ->
      -- Area fill: ~10μs per 1K pixels
      Int.toNumber (k.config.width * k.config.height) / 100.0
    KernelBarChart (BarChartKernel k) ->
      -- Bar chart: ~1μs per bar
      Int.toNumber (k.categoryCount * k.seriesCount)
    KernelThresholdOverlay (ThresholdOverlayKernel k) ->
      -- Threshold: ~5μs per zone per 1K pixels
      Int.toNumber (Array.length k.zones) * 
      Int.toNumber (k.config.width * k.config.height) / 200.0
    KernelGridOverlay (GridOverlayKernel k) ->
      -- Grid: ~2μs per line
      Int.toNumber (k.divisions.majorX + k.divisions.majorY + 
                    k.divisions.minorX * k.divisions.majorX + 
                    k.divisions.minorY * k.divisions.majorY) * 2.0
    KernelChartSequence kernels ->
      foldlArray (\acc k -> acc + estimateChartKernelCost k) 0.0 kernels
    KernelChartNoop -> 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | ECG monitor pipeline (IEC 60601-1 compliant)
-- |
-- | Features:
-- | - 25mm/s sweep speed
-- | - 1mV = 10mm calibration
-- | - Medical-grade grid overlay
-- | - Threshold zones for arrhythmia detection
ecgMonitorPipeline :: Int -> Int -> ChartKernel
ecgMonitorPipeline width height =
  let
    config = medicalECGConfig width height
    
    -- ECG waveform (green on black)
    waveform = KernelWaveform $ WaveformKernel
      { style: WaveformLine
      , waveformConfig:
          { sampleCount: 2500  -- 10 seconds at 250 Hz
          , channelCount: 1
          , minValue: -1.5     -- mV
          , maxValue: 1.5      -- mV
          , lineWidth: 2.0
          , antiAliasing: true
          }
      , color: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }  -- ECG green
      , peakHold: false
      , peakDecay: 0.0
      , rmsOverlay: false
      , zeroCrossing: false
      , config
      }
    
    -- Medical grid (5mm major, 1mm minor)
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridLines
      , divisions:
          { majorX: 10
          , majorY: 6
          , minorX: 5
          , minorY: 5
          }
      , majorColor: { r: 0.3, g: 0.3, b: 0.3, a: 0.8 }
      , minorColor: { r: 0.2, g: 0.2, b: 0.2, a: 0.4 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.5, g: 0.5, b: 0.5, a: 1.0 }
      , config
      }
    
    -- Threshold zones for abnormal rhythms
    thresholds = KernelThresholdOverlay $ ThresholdOverlayKernel
      { zones:
          [ { minValue: -1.5, maxValue: -1.0, severity: SeverityDanger
            , color: { r: 1.0, g: 0.0, b: 0.0, a: 0.2 }, label: "Low", showLabel: true }
          , { minValue: 1.0, maxValue: 1.5, severity: SeverityDanger
            , color: { r: 1.0, g: 0.0, b: 0.0, a: 0.2 }, label: "High", showLabel: true }
          ]
      , fillOpacity: 0.2
      , showBorders: true
      , borderWidth: 1.0
      , animated: false
      , pulseOnViolation: true
      , config
      }
  in
    KernelChartSequence [grid, thresholds, waveform]

-- | Vital signs trend pipeline
-- |
-- | Multi-parameter trending for:
-- | - Heart rate
-- | - Blood pressure (systolic/diastolic)
-- | - SpO2
-- | - Temperature
vitalSignsTrendPipeline :: Int -> Int -> ChartKernel
vitalSignsTrendPipeline width height =
  let
    config = medicalECGConfig width height
    
    -- Multi-series line plot
    linePlot = KernelLinePlot $ LinePlotKernel
      { series:
          [ { seriesId: 0, label: "HR", color: { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 1, label: "SpO2", color: { r: 0.0, g: 0.8, b: 1.0, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 2, label: "Sys", color: { r: 1.0, g: 0.3, b: 0.3, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 3, label: "Dia", color: { r: 1.0, g: 0.6, b: 0.3, a: 1.0 }
            , lineStyle: LineDashed, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          ]
      , dataPointCount: 300   -- 5 minutes at 1 Hz
      , xAxisMin: 0.0
      , xAxisMax: 300.0
      , yAxisMin: 0.0
      , yAxisMax: 200.0
      , antiAliasing: true
      , config
      }
    
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridDashes
      , divisions: { majorX: 5, majorY: 4, minorX: 6, minorY: 2 }
      , majorColor: { r: 0.4, g: 0.4, b: 0.4, a: 0.6 }
      , minorColor: { r: 0.2, g: 0.2, b: 0.2, a: 0.3 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.6, g: 0.6, b: 0.6, a: 1.0 }
      , config
      }
  in
    KernelChartSequence [grid, linePlot]

-- | Audio waveform pipeline
-- |
-- | DAW-style waveform display with:
-- | - Min/max envelope
-- | - RMS overlay
-- | - Peak hold indicators
audioWaveformPipeline :: Int -> Int -> ChartKernel
audioWaveformPipeline width height =
  let
    config = audioWaveformConfig width height
    
    -- Waveform with min/max envelope
    waveform = KernelWaveform $ WaveformKernel
      { style: WaveformMinMax
      , waveformConfig:
          { sampleCount: 44100  -- 1 second at 44.1kHz
          , channelCount: 2     -- Stereo
          , minValue: -1.0
          , maxValue: 1.0
          , lineWidth: 1.0
          , antiAliasing: true
          }
      , color: { r: 0.3, g: 0.7, b: 1.0, a: 1.0 }  -- Blue waveform
      , peakHold: true
      , peakDecay: 12.0        -- 12 dB/s decay
      , rmsOverlay: true
      , zeroCrossing: false
      , config
      }
    
    -- Area fill under waveform
    fill = KernelAreaFill $ AreaFillKernel
      { fillMode: FillGradient
      , primaryColor: { r: 0.3, g: 0.7, b: 1.0, a: 0.5 }
      , secondaryColor: { r: 0.3, g: 0.7, b: 1.0, a: 0.0 }
      , gradientDirection: GradientVertical
      , opacity: 0.5
      , seriesIndex: 0
      , secondSeriesIndex: 0
      , config
      }
  in
    KernelChartSequence [fill, waveform]

-- | Spectrum analyzer pipeline
-- |
-- | Frequency spectrum display with:
-- | - Bar-style frequency bins
-- | - Peak hold
-- | - Logarithmic scale option
spectrumAnalyzerPipeline :: Int -> Int -> ChartKernel
spectrumAnalyzerPipeline width height =
  let
    config = audioWaveformConfig width height
    
    -- Spectrum bars
    bars = KernelBarChart $ BarChartKernel
      { orientation: BarVertical
      , grouping: BarGrouped
      , barColors: 
          [ { r: 0.0, g: 1.0, b: 0.0, a: 1.0 }   -- Green (low)
          , { r: 1.0, g: 1.0, b: 0.0, a: 1.0 }   -- Yellow (mid)
          , { r: 1.0, g: 0.0, b: 0.0, a: 1.0 }   -- Red (high)
          ]
      , barWidth: 0.9
      , barSpacing: 0.05
      , cornerRadius: 2.0
      , showValues: false
      , categoryCount: 32      -- 32 frequency bins
      , seriesCount: 1
      , config
      }
  in
    bars

-- | Stock chart pipeline
-- |
-- | Financial chart with:
-- | - Price line
-- | - Volume bars
-- | - Moving averages
stockChartPipeline :: Int -> Int -> ChartKernel
stockChartPipeline width height =
  let
    config = financialChartConfig width height
    
    -- Price line with moving averages
    priceChart = KernelLinePlot $ LinePlotKernel
      { series:
          [ { seriesId: 0, label: "Price", color: { r: 0.2, g: 0.4, b: 0.8, a: 1.0 }
            , lineStyle: LineSolid, lineWidth: 2.0, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 1, label: "MA20", color: { r: 1.0, g: 0.5, b: 0.0, a: 0.8 }
            , lineStyle: LineSolid, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          , { seriesId: 2, label: "MA50", color: { r: 0.5, g: 0.0, b: 1.0, a: 0.8 }
            , lineStyle: LineSolid, lineWidth: 1.5, showPoints: false, pointRadius: 0.0 }
          ]
      , dataPointCount: 100
      , xAxisMin: 0.0
      , xAxisMax: 100.0
      , yAxisMin: 0.0
      , yAxisMax: 100.0
      , antiAliasing: true
      , config
      }
    
    -- Area fill under price
    fill = KernelAreaFill $ AreaFillKernel
      { fillMode: FillGradient
      , primaryColor: { r: 0.2, g: 0.4, b: 0.8, a: 0.3 }
      , secondaryColor: { r: 0.2, g: 0.4, b: 0.8, a: 0.0 }
      , gradientDirection: GradientVertical
      , opacity: 0.3
      , seriesIndex: 0
      , secondSeriesIndex: 0
      , config
      }
    
    grid = KernelGridOverlay $ GridOverlayKernel
      { style: GridDashes
      , divisions: { majorX: 10, majorY: 5, minorX: 2, minorY: 2 }
      , majorColor: { r: 0.8, g: 0.8, b: 0.8, a: 0.5 }
      , minorColor: { r: 0.9, g: 0.9, b: 0.9, a: 0.3 }
      , majorWidth: 1.0
      , minorWidth: 0.5
      , showLabels: true
      , labelColor: { r: 0.4, g: 0.4, b: 0.4, a: 1.0 }
      , config
      }
  in
    KernelChartSequence [grid, fill, priceChart]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr =
  case Array.uncons arr of
    Nothing -> init
    Just { head, tail } -> foldlArray f (f init head) tail
