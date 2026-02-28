-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // compute-kernel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel — GPU Compute Abstractions for Effect Processing
-- |
-- | ## Design Philosophy
-- |
-- | Hyper-responsive effects require GPU compute for:
-- | - Real-time blur (Gaussian, radial, directional)
-- | - Glow with bloom and color cycling
-- | - Particle physics simulation
-- | - Noise generation (Perlin, Simplex, FBM)
-- | - Diffusion model inference (latent space fills)
-- |
-- | This module defines **pure data** representing compute operations.
-- | The interpreter converts these to WebGPU compute shaders.
-- |
-- | ## Tensor-Native Model
-- |
-- | Every compute kernel operates on tensors:
-- |
-- | ```
-- | ComputeKernel :: InputTensors → OutputTensor
-- | ```
-- |
-- | Where tensors have shape `[N, C, H, W]` (batch, channels, height, width).
-- | This matches both GPU memory layout and ML model expectations.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Kernels are deterministic data:
-- | - Same kernel + same input = same output (always)
-- | - Kernels can be serialized, hashed, cached
-- | - Multiple agents can share kernel definitions
-- | - GPU batches kernels across agents efficiently
-- |
-- | ## WebGPU Mapping
-- |
-- | Each kernel variant maps to a compute shader:
-- |
-- | | Kernel | Workgroup | Dispatch |
-- | |--------|-----------|----------|
-- | | Blur   | 16×16×1   | (W/16, H/16, 1) |
-- | | Glow   | 16×16×1   | (W/16, H/16, 1) |
-- | | Noise  | 8×8×8     | (W/8, H/8, C/8) |
-- | | Particle | 256×1×1 | (N/256, 1, 1) |

module Hydrogen.GPU.ComputeKernel
  ( -- * Core Types
    ComputeKernel(..)
  , KernelInput(..)
  , KernelOutput(..)
  , KernelConfig
  , WorkgroupSize
  , DispatchSize
  
  -- * Blur Kernels
  , BlurKernel(..)
  , BlurQuality(..)
  , RadialBlurType(..)
  , GaussianBlurKernel
  , DirectionalBlurKernel
  , RadialBlurKernel
  , BoxBlurKernel
  
  -- * Glow Kernels
  , GlowKernel(..)
  , GlowTint
  , GlowFalloff(..)
  , BloomKernel
  , OuterGlowKernel
  , InnerGlowKernel
  
  -- * Noise Kernels
  , NoiseKernel(..)
  , WorleyDistance(..)
  , PerlinNoiseKernel
  , SimplexNoiseKernel
  , FBMNoiseKernel
  , WorleyNoiseKernel
  
  -- * Particle Kernels
  , ParticleKernel(..)
  , ParticleBounds(..)
  , ParticleForce
  , SortAxis(..)
  , ParticlePhysicsKernel
  , ParticleEmitKernel
  , ParticleSortKernel
  
  -- * Color Kernels
  , ColorKernel(..)
  , ColorGradingKernel
  , ToneMappingKernel
  , ToneMappingAlgorithm(..)
  , ColorSpaceKernel
  , ColorSpaceType(..)
  
  -- * Distortion Kernels
  , DistortionKernel(..)
  , DisplacementChannel(..)
  , WarpType(..)
  , DisplacementKernel
  , WarpKernel
  , RippleKernel
  
  -- * Composite Kernels
  , CompositeKernel(..)
  , BlendKernelMode(..)
  , MaskChannel(..)
  , AlphaOperation(..)
  , BlendKernel
  , MaskKernel
  , AlphaKernel
  
  -- * Kernel Construction
  , gaussianBlurKernel
  , directionalBlurKernel
  , radialBlurKernel
  , boxBlurKernel
  , bloomKernel
  , outerGlowKernel
  , innerGlowKernel
  , perlinNoiseKernel
  , simplexNoiseKernel
  , fbmNoiseKernel
  , worleyNoiseKernel
  , particlePhysicsKernel
  , particleEmitKernel
  , colorGradingKernel
  , toneMappingKernel
  , displacementKernel
  , warpKernel
  , blendKernel
  , maskKernel
  
  -- * Kernel Dispatch
  , computeWorkgroupSize
  , computeDispatchSize
  , estimateKernelCost
  
  -- * Kernel Composition
  , sequenceKernels
  , parallelKernels
  , conditionalKernel
  
  -- * Condition Types
  , KernelCondition(..)
  , QualityLevel(..)
  , SizeThreshold
  
  -- * Color Adjustment Types
  , ColorAdjust
  
  -- * Presets
  , standardGaussian
  , fastGaussian
  , qualityGaussian
  , standardBloom
  , softBloom
  , intenseBloom
  , standardNoise
  , animatedNoise
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , ($)
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Workgroup size for compute dispatch
type WorkgroupSize =
  { x :: Int               -- Threads in X (typically 8, 16, or 32)
  , y :: Int               -- Threads in Y
  , z :: Int               -- Threads in Z
  }

-- | Dispatch dimensions (number of workgroups)
type DispatchSize =
  { x :: Int               -- Workgroups in X
  , y :: Int               -- Workgroups in Y
  , z :: Int               -- Workgroups in Z
  }

-- | Input source for kernel
data KernelInput
  = InputTexture Int           -- Texture by index
  | InputBuffer Int            -- Storage buffer by index
  | InputUniform Int           -- Uniform buffer by index
  | InputPrevious              -- Output of previous kernel in chain
  | InputConstant Number       -- Constant value

derive instance eqKernelInput :: Eq KernelInput

instance showKernelInput :: Show KernelInput where
  show (InputTexture i) = "(InputTexture " <> show i <> ")"
  show (InputBuffer i) = "(InputBuffer " <> show i <> ")"
  show (InputUniform i) = "(InputUniform " <> show i <> ")"
  show InputPrevious = "InputPrevious"
  show (InputConstant v) = "(InputConstant " <> show v <> ")"

-- | Output target for kernel
data KernelOutput
  = OutputTexture Int          -- Write to texture by index
  | OutputBuffer Int           -- Write to storage buffer
  | OutputNext                 -- Feed to next kernel
  | OutputScreen               -- Final output to screen

derive instance eqKernelOutput :: Eq KernelOutput

instance showKernelOutput :: Show KernelOutput where
  show (OutputTexture i) = "(OutputTexture " <> show i <> ")"
  show (OutputBuffer i) = "(OutputBuffer " <> show i <> ")"
  show OutputNext = "OutputNext"
  show OutputScreen = "OutputScreen"

-- | Kernel configuration
type KernelConfig =
  { workgroupSize :: WorkgroupSize
  , input :: KernelInput
  , output :: KernelOutput
  , width :: Int               -- Output width in pixels
  , height :: Int              -- Output height in pixels
  , channels :: Int            -- Number of channels (typically 4 for RGBA)
  }

-- | A compute kernel — GPU operation description
data ComputeKernel
  = KernelBlur BlurKernel
  | KernelGlow GlowKernel
  | KernelNoise NoiseKernel
  | KernelParticle ParticleKernel
  | KernelColor ColorKernel
  | KernelDistortion DistortionKernel
  | KernelComposite CompositeKernel
  | KernelSequence (Array ComputeKernel)     -- Execute in order
  | KernelParallel (Array ComputeKernel)     -- Execute simultaneously (different outputs)
  | KernelConditional                        -- Conditional execution
      { condition :: KernelCondition
      , thenKernel :: ComputeKernel
      , elseKernel :: Maybe ComputeKernel
      }
  | KernelNoop                               -- Identity (no operation)

derive instance eqComputeKernel :: Eq ComputeKernel

instance showComputeKernel :: Show ComputeKernel where
  show (KernelBlur k) = "(KernelBlur " <> show k <> ")"
  show (KernelGlow k) = "(KernelGlow " <> show k <> ")"
  show (KernelNoise k) = "(KernelNoise " <> show k <> ")"
  show (KernelParticle k) = "(KernelParticle " <> show k <> ")"
  show (KernelColor k) = "(KernelColor " <> show k <> ")"
  show (KernelDistortion k) = "(KernelDistortion " <> show k <> ")"
  show (KernelComposite k) = "(KernelComposite " <> show k <> ")"
  show (KernelSequence _) = "(KernelSequence [...])"
  show (KernelParallel _) = "(KernelParallel [...])"
  show (KernelConditional _) = "(KernelConditional ...)"
  show KernelNoop = "KernelNoop"

-- | Condition for kernel execution
data KernelCondition
  = ConditionQuality QualityLevel    -- Based on quality setting
  | ConditionSize SizeThreshold      -- Based on output size
  | ConditionPerformance Number      -- Based on GPU budget (ms)
  | ConditionAlways                  -- Always true

derive instance eqKernelCondition :: Eq KernelCondition

-- | Quality levels for adaptive processing
data QualityLevel
  = QualityLow
  | QualityMedium
  | QualityHigh
  | QualityUltra

derive instance eqQualityLevel :: Eq QualityLevel

-- | Size threshold for conditional kernels
type SizeThreshold =
  { minWidth :: Int
  , minHeight :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blur kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur kernel variants
data BlurKernel
  = BlurGaussian GaussianBlurKernel
  | BlurDirectional DirectionalBlurKernel
  | BlurRadial RadialBlurKernel
  | BlurBox BoxBlurKernel

derive instance eqBlurKernel :: Eq BlurKernel

instance showBlurKernel :: Show BlurKernel where
  show (BlurGaussian k) = "(BlurGaussian " <> show k <> ")"
  show (BlurDirectional k) = "(BlurDirectional " <> show k <> ")"
  show (BlurRadial k) = "(BlurRadial " <> show k <> ")"
  show (BlurBox k) = "(BlurBox " <> show k <> ")"

-- | Gaussian blur kernel
-- |
-- | Implements separable 2-pass Gaussian blur.
-- | Pass 1: Horizontal convolution
-- | Pass 2: Vertical convolution
newtype GaussianBlurKernel = GaussianBlurKernel
  { radius :: Int              -- Kernel radius in pixels
  , sigma :: Number            -- Standard deviation
  , passes :: Int              -- Number of blur passes (more = softer)
  , config :: KernelConfig
  }

derive instance eqGaussianBlurKernel :: Eq GaussianBlurKernel

instance showGaussianBlurKernel :: Show GaussianBlurKernel where
  show (GaussianBlurKernel k) = "(GaussianBlurKernel radius:" <> show k.radius <> ")"

-- | Directional blur kernel (motion blur)
newtype DirectionalBlurKernel = DirectionalBlurKernel
  { angle :: Number            -- Direction in degrees
  , distance :: Int            -- Blur distance in pixels
  , samples :: Int             -- Number of samples along direction
  , config :: KernelConfig
  }

derive instance eqDirectionalBlurKernel :: Eq DirectionalBlurKernel

instance showDirectionalBlurKernel :: Show DirectionalBlurKernel where
  show (DirectionalBlurKernel k) = "(DirectionalBlurKernel angle:" <> show k.angle <> ")"

-- | Radial blur kernel (spin/zoom)
newtype RadialBlurKernel = RadialBlurKernel
  { centerX :: Number          -- Center X (0.0-1.0 normalized)
  , centerY :: Number          -- Center Y (0.0-1.0 normalized)
  , amount :: Number           -- Blur strength
  , blurType :: RadialBlurType -- Spin or zoom
  , samples :: Int             -- Number of samples
  , config :: KernelConfig
  }

derive instance eqRadialBlurKernel :: Eq RadialBlurKernel

instance showRadialBlurKernel :: Show RadialBlurKernel where
  show (RadialBlurKernel k) = "(RadialBlurKernel amount:" <> show k.amount <> ")"

-- | Radial blur type
data RadialBlurType
  = RadialTypeSpin
  | RadialTypeZoom

derive instance eqRadialBlurType :: Eq RadialBlurType

-- | Blur quality levels — controls compute precision vs performance tradeoff
-- |
-- | At billion-agent scale, quality selection determines GPU budget allocation:
-- | - Low: Fast, acceptable for backgrounds, UI blur
-- | - Medium: Balanced for general use
-- | - High: Best quality for hero elements, slower
data BlurQuality
  = BlurQualityLow            -- Fast: fewer samples, single pass
  | BlurQualityMedium         -- Balanced: moderate samples, dual pass
  | BlurQualityHigh           -- Quality: many samples, multi-pass

derive instance eqBlurQuality :: Eq BlurQuality

instance showBlurQuality :: Show BlurQuality where
  show BlurQualityLow = "BlurQualityLow"
  show BlurQualityMedium = "BlurQualityMedium"
  show BlurQualityHigh = "BlurQualityHigh"

-- | Box blur kernel (fast, lower quality)
newtype BoxBlurKernel = BoxBlurKernel
  { radius :: Int              -- Box radius
  , iterations :: Int          -- Multiple passes for approximated Gaussian
  , config :: KernelConfig
  }

derive instance eqBoxBlurKernel :: Eq BoxBlurKernel

instance showBoxBlurKernel :: Show BoxBlurKernel where
  show (BoxBlurKernel k) = "(BoxBlurKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow kernel variants
data GlowKernel
  = GlowBloom BloomKernel
  | GlowOuter OuterGlowKernel
  | GlowInner InnerGlowKernel

derive instance eqGlowKernel :: Eq GlowKernel

instance showGlowKernel :: Show GlowKernel where
  show (GlowBloom k) = "(GlowBloom " <> show k <> ")"
  show (GlowOuter k) = "(GlowOuter " <> show k <> ")"
  show (GlowInner k) = "(GlowInner " <> show k <> ")"

-- | Bloom kernel — extract bright pixels, blur, composite
-- |
-- | 3-pass pipeline:
-- | 1. Threshold: Extract pixels above threshold
-- | 2. Blur: Gaussian blur the extracted pixels
-- | 3. Composite: Add blurred result back to original
newtype BloomKernel = BloomKernel
  { threshold :: Number        -- Brightness threshold (0.0-1.0)
  , intensity :: Number        -- Bloom intensity
  , radius :: Int              -- Blur radius
  , passes :: Int              -- Blur passes for quality
  , tint :: GlowTint           -- Optional color tint
  , config :: KernelConfig
  }

derive instance eqBloomKernel :: Eq BloomKernel

instance showBloomKernel :: Show BloomKernel where
  show (BloomKernel k) = "(BloomKernel threshold:" <> show k.threshold <> ")"

-- | Glow color tint
type GlowTint =
  { r :: Number                -- Red (0.0-1.0)
  , g :: Number                -- Green (0.0-1.0)
  , b :: Number                -- Blue (0.0-1.0)
  , enabled :: Boolean         -- Whether tint is applied
  }

-- | Outer glow kernel — glow outside element edges
newtype OuterGlowKernel = OuterGlowKernel
  { color :: GlowTint
  , radius :: Int              -- Glow spread radius
  , intensity :: Number        -- Glow intensity (0.0-1.0)
  , falloff :: GlowFalloff     -- Intensity falloff curve
  , config :: KernelConfig
  }

derive instance eqOuterGlowKernel :: Eq OuterGlowKernel

instance showOuterGlowKernel :: Show OuterGlowKernel where
  show (OuterGlowKernel k) = "(OuterGlowKernel radius:" <> show k.radius <> ")"

-- | Glow falloff type
data GlowFalloff
  = FalloffLinear
  | FalloffQuadratic
  | FalloffExponential
  | FalloffGaussian

derive instance eqGlowFalloff :: Eq GlowFalloff

-- | Inner glow kernel — glow inside element edges
newtype InnerGlowKernel = InnerGlowKernel
  { color :: GlowTint
  , radius :: Int
  , intensity :: Number
  , choke :: Number            -- Edge hardness (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqInnerGlowKernel :: Eq InnerGlowKernel

instance showInnerGlowKernel :: Show InnerGlowKernel where
  show (InnerGlowKernel k) = "(InnerGlowKernel radius:" <> show k.radius <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise kernel variants
data NoiseKernel
  = NoisePerlin PerlinNoiseKernel
  | NoiseSimplex SimplexNoiseKernel
  | NoiseFBM FBMNoiseKernel
  | NoiseWorley WorleyNoiseKernel

derive instance eqNoiseKernel :: Eq NoiseKernel

instance showNoiseKernel :: Show NoiseKernel where
  show (NoisePerlin k) = "(NoisePerlin " <> show k <> ")"
  show (NoiseSimplex k) = "(NoiseSimplex " <> show k <> ")"
  show (NoiseFBM k) = "(NoiseFBM " <> show k <> ")"
  show (NoiseWorley k) = "(NoiseWorley " <> show k <> ")"

-- | Perlin noise kernel
newtype PerlinNoiseKernel = PerlinNoiseKernel
  { scale :: Number            -- Noise scale (frequency)
  , seed :: Int                -- Random seed for determinism
  , octaves :: Int             -- Number of octaves
  , persistence :: Number      -- Amplitude decay per octave
  , lacunarity :: Number       -- Frequency growth per octave
  , time :: Number             -- Time for animation
  , config :: KernelConfig
  }

derive instance eqPerlinNoiseKernel :: Eq PerlinNoiseKernel

instance showPerlinNoiseKernel :: Show PerlinNoiseKernel where
  show (PerlinNoiseKernel k) = "(PerlinNoiseKernel scale:" <> show k.scale <> ")"

-- | Simplex noise kernel (faster than Perlin)
newtype SimplexNoiseKernel = SimplexNoiseKernel
  { scale :: Number
  , seed :: Int
  , time :: Number
  , config :: KernelConfig
  }

derive instance eqSimplexNoiseKernel :: Eq SimplexNoiseKernel

instance showSimplexNoiseKernel :: Show SimplexNoiseKernel where
  show (SimplexNoiseKernel k) = "(SimplexNoiseKernel scale:" <> show k.scale <> ")"

-- | Fractal Brownian Motion noise kernel
newtype FBMNoiseKernel = FBMNoiseKernel
  { scale :: Number
  , seed :: Int
  , octaves :: Int             -- Number of noise layers
  , persistence :: Number      -- Amplitude decay (0.0-1.0)
  , lacunarity :: Number       -- Frequency multiplier (typically 2.0)
  , time :: Number
  , turbulent :: Boolean       -- Use absolute value (turbulence)
  , config :: KernelConfig
  }

derive instance eqFBMNoiseKernel :: Eq FBMNoiseKernel

instance showFBMNoiseKernel :: Show FBMNoiseKernel where
  show (FBMNoiseKernel k) = "(FBMNoiseKernel octaves:" <> show k.octaves <> ")"

-- | Worley (cellular) noise kernel
newtype WorleyNoiseKernel = WorleyNoiseKernel
  { scale :: Number
  , seed :: Int
  , cellCount :: Int           -- Number of cells
  , distanceType :: WorleyDistance
  , time :: Number
  , config :: KernelConfig
  }

derive instance eqWorleyNoiseKernel :: Eq WorleyNoiseKernel

instance showWorleyNoiseKernel :: Show WorleyNoiseKernel where
  show (WorleyNoiseKernel k) = "(WorleyNoiseKernel cells:" <> show k.cellCount <> ")"

-- | Worley noise distance metric
data WorleyDistance
  = WorleyEuclidean
  | WorleyManhattan
  | WorleyChebyshev

derive instance eqWorleyDistance :: Eq WorleyDistance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // particle kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle kernel variants
data ParticleKernel
  = ParticlePhysics ParticlePhysicsKernel
  | ParticleEmit ParticleEmitKernel
  | ParticleSort ParticleSortKernel

derive instance eqParticleKernel :: Eq ParticleKernel

instance showParticleKernel :: Show ParticleKernel where
  show (ParticlePhysics k) = "(ParticlePhysics " <> show k <> ")"
  show (ParticleEmit k) = "(ParticleEmit " <> show k <> ")"
  show (ParticleSort k) = "(ParticleSort " <> show k <> ")"

-- | Particle physics simulation kernel
-- |
-- | Updates particle positions, velocities, and lifetimes.
-- | GPU-parallel: each thread handles one particle.
newtype ParticlePhysicsKernel = ParticlePhysicsKernel
  { particleCount :: Int       -- Number of particles
  , deltaTime :: Number        -- Time step in seconds
  , gravity :: Number          -- Gravity strength
  , damping :: Number          -- Velocity damping
  , bounds :: ParticleBounds   -- Boundary behavior
  , forces :: Array ParticleForce  -- External forces
  , config :: KernelConfig
  }

derive instance eqParticlePhysicsKernel :: Eq ParticlePhysicsKernel

instance showParticlePhysicsKernel :: Show ParticlePhysicsKernel where
  show (ParticlePhysicsKernel k) = "(ParticlePhysicsKernel count:" <> show k.particleCount <> ")"

-- | Particle boundary behavior
data ParticleBounds
  = BoundsNone               -- No boundaries
  | BoundsWrap               -- Wrap around edges
  | BoundsBounce             -- Bounce off edges
  | BoundsKill               -- Kill particles at edges

derive instance eqParticleBounds :: Eq ParticleBounds

-- | External force on particles
type ParticleForce =
  { x :: Number                -- Force X component
  , y :: Number                -- Force Y component
  , z :: Number                -- Force Z component
  , strength :: Number         -- Force magnitude
  , falloff :: Number          -- Distance falloff
  }

-- | Particle emission kernel
newtype ParticleEmitKernel = ParticleEmitKernel
  { emitCount :: Int           -- Particles to emit this frame
  , positionX :: Number        -- Emitter X (0.0-1.0)
  , positionY :: Number        -- Emitter Y (0.0-1.0)
  , spread :: Number           -- Emission cone spread (radians)
  , velocity :: Number         -- Initial velocity
  , velocityVariance :: Number -- Velocity randomness
  , lifetime :: Number         -- Particle lifetime (seconds)
  , lifetimeVariance :: Number -- Lifetime randomness
  , seed :: Int                -- Random seed
  , config :: KernelConfig
  }

derive instance eqParticleEmitKernel :: Eq ParticleEmitKernel

instance showParticleEmitKernel :: Show ParticleEmitKernel where
  show (ParticleEmitKernel k) = "(ParticleEmitKernel emit:" <> show k.emitCount <> ")"

-- | Particle sort kernel (for depth ordering)
newtype ParticleSortKernel = ParticleSortKernel
  { particleCount :: Int
  , sortAxis :: SortAxis       -- Which axis to sort on
  , config :: KernelConfig
  }

derive instance eqParticleSortKernel :: Eq ParticleSortKernel

instance showParticleSortKernel :: Show ParticleSortKernel where
  show (ParticleSortKernel k) = "(ParticleSortKernel count:" <> show k.particleCount <> ")"

-- | Sort axis for particles
data SortAxis
  = SortAxisZ                -- Sort by depth
  | SortAxisDistance         -- Sort by distance from camera

derive instance eqSortAxis :: Eq SortAxis

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color processing kernel variants
data ColorKernel
  = ColorGrading ColorGradingKernel
  | ColorToneMapping ToneMappingKernel
  | ColorSpace ColorSpaceKernel

derive instance eqColorKernel :: Eq ColorKernel

instance showColorKernel :: Show ColorKernel where
  show (ColorGrading k) = "(ColorGrading " <> show k <> ")"
  show (ColorToneMapping k) = "(ColorToneMapping " <> show k <> ")"
  show (ColorSpace k) = "(ColorSpace " <> show k <> ")"

-- | Color grading kernel
newtype ColorGradingKernel = ColorGradingKernel
  { exposure :: Number         -- Exposure adjustment (-2.0 to 2.0)
  , contrast :: Number         -- Contrast (-1.0 to 1.0)
  , saturation :: Number       -- Saturation (0.0 to 2.0)
  , temperature :: Number      -- Color temperature (-1.0 to 1.0)
  , tint :: Number             -- Green/magenta tint (-1.0 to 1.0)
  , shadows :: ColorAdjust     -- Shadow color adjustment
  , midtones :: ColorAdjust    -- Midtone color adjustment
  , highlights :: ColorAdjust  -- Highlight color adjustment
  , config :: KernelConfig
  }

derive instance eqColorGradingKernel :: Eq ColorGradingKernel

instance showColorGradingKernel :: Show ColorGradingKernel where
  show (ColorGradingKernel k) = "(ColorGradingKernel exposure:" <> show k.exposure <> ")"

-- | Color adjustment per tonal range
type ColorAdjust =
  { r :: Number                -- Red adjustment (-1.0 to 1.0)
  , g :: Number                -- Green adjustment
  , b :: Number                -- Blue adjustment
  }

-- | Tone mapping kernel (HDR to LDR)
newtype ToneMappingKernel = ToneMappingKernel
  { algorithm :: ToneMappingAlgorithm
  , whitePoint :: Number       -- Reference white level
  , config :: KernelConfig
  }

derive instance eqToneMappingKernel :: Eq ToneMappingKernel

instance showToneMappingKernel :: Show ToneMappingKernel where
  show (ToneMappingKernel k) = "(ToneMappingKernel " <> show k.algorithm <> ")"

-- | Tone mapping algorithms
data ToneMappingAlgorithm
  = TonemapReinhard
  | TonemapACES
  | TonemapHable           -- Uncharted 2
  | TonemapFilmic

derive instance eqToneMappingAlgorithm :: Eq ToneMappingAlgorithm

instance showToneMappingAlgorithm :: Show ToneMappingAlgorithm where
  show TonemapReinhard = "TonemapReinhard"
  show TonemapACES = "TonemapACES"
  show TonemapHable = "TonemapHable"
  show TonemapFilmic = "TonemapFilmic"

-- | Color space conversion kernel
newtype ColorSpaceKernel = ColorSpaceKernel
  { from :: ColorSpaceType
  , to :: ColorSpaceType
  , config :: KernelConfig
  }

derive instance eqColorSpaceKernel :: Eq ColorSpaceKernel

instance showColorSpaceKernel :: Show ColorSpaceKernel where
  show (ColorSpaceKernel k) = "(ColorSpaceKernel " <> show k.from <> " -> " <> show k.to <> ")"

-- | Color space types
data ColorSpaceType
  = ColorSpaceSRGB
  | ColorSpaceLinear
  | ColorSpaceP3
  | ColorSpaceRec2020
  | ColorSpaceOKLab
  | ColorSpaceOKLCH

derive instance eqColorSpaceType :: Eq ColorSpaceType

instance showColorSpaceType :: Show ColorSpaceType where
  show ColorSpaceSRGB = "sRGB"
  show ColorSpaceLinear = "Linear"
  show ColorSpaceP3 = "P3"
  show ColorSpaceRec2020 = "Rec2020"
  show ColorSpaceOKLab = "OKLab"
  show ColorSpaceOKLCH = "OKLCH"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // distortion kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distortion kernel variants
data DistortionKernel
  = DistortDisplacement DisplacementKernel
  | DistortWarp WarpKernel
  | DistortRipple RippleKernel

derive instance eqDistortionKernel :: Eq DistortionKernel

instance showDistortionKernel :: Show DistortionKernel where
  show (DistortDisplacement k) = "(DistortDisplacement " <> show k <> ")"
  show (DistortWarp k) = "(DistortWarp " <> show k <> ")"
  show (DistortRipple k) = "(DistortRipple " <> show k <> ")"

-- | Displacement map kernel
newtype DisplacementKernel = DisplacementKernel
  { mapInput :: KernelInput    -- Displacement map source
  , scaleX :: Number           -- X displacement scale
  , scaleY :: Number           -- Y displacement scale
  , channel :: DisplacementChannel
  , config :: KernelConfig
  }

derive instance eqDisplacementKernel :: Eq DisplacementKernel

instance showDisplacementKernel :: Show DisplacementKernel where
  show (DisplacementKernel k) = "(DisplacementKernel scaleX:" <> show k.scaleX <> ")"

-- | Channel to use for displacement
data DisplacementChannel
  = DisplaceRed
  | DisplaceGreen
  | DisplaceBlue
  | DisplaceAlpha
  | DisplaceLuminance

derive instance eqDisplacementChannel :: Eq DisplacementChannel

-- | Warp kernel (mesh deformation)
newtype WarpKernel = WarpKernel
  { warpType :: WarpType
  , strength :: Number         -- Warp strength
  , centerX :: Number          -- Warp center X (0.0-1.0)
  , centerY :: Number          -- Warp center Y (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqWarpKernel :: Eq WarpKernel

instance showWarpKernel :: Show WarpKernel where
  show (WarpKernel k) = "(WarpKernel " <> show k.warpType <> ")"

-- | Warp types
data WarpType
  = WarpSphere               -- Spherize
  | WarpPinch                -- Pinch/bulge
  | WarpTwirl                -- Twirl/swirl
  | WarpWave                 -- Wave distortion

derive instance eqWarpType :: Eq WarpType

instance showWarpType :: Show WarpType where
  show WarpSphere = "WarpSphere"
  show WarpPinch = "WarpPinch"
  show WarpTwirl = "WarpTwirl"
  show WarpWave = "WarpWave"

-- | Ripple kernel
newtype RippleKernel = RippleKernel
  { amplitude :: Number        -- Wave amplitude
  , frequency :: Number        -- Wave frequency
  , phase :: Number            -- Phase offset (for animation)
  , centerX :: Number
  , centerY :: Number
  , damping :: Number          -- Distance falloff
  , config :: KernelConfig
  }

derive instance eqRippleKernel :: Eq RippleKernel

instance showRippleKernel :: Show RippleKernel where
  show (RippleKernel k) = "(RippleKernel amplitude:" <> show k.amplitude <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // composite kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Composite kernel variants
data CompositeKernel
  = CompositeBlend BlendKernel
  | CompositeMask MaskKernel
  | CompositeAlpha AlphaKernel

derive instance eqCompositeKernel :: Eq CompositeKernel

instance showCompositeKernel :: Show CompositeKernel where
  show (CompositeBlend k) = "(CompositeBlend " <> show k <> ")"
  show (CompositeMask k) = "(CompositeMask " <> show k <> ")"
  show (CompositeAlpha k) = "(CompositeAlpha " <> show k <> ")"

-- | Blend kernel
newtype BlendKernel = BlendKernel
  { layerA :: KernelInput      -- Bottom layer
  , layerB :: KernelInput      -- Top layer
  , mode :: BlendKernelMode
  , opacity :: Number          -- Top layer opacity (0.0-1.0)
  , config :: KernelConfig
  }

derive instance eqBlendKernel :: Eq BlendKernel

instance showBlendKernel :: Show BlendKernel where
  show (BlendKernel k) = "(BlendKernel " <> show k.mode <> ")"

-- | Blend modes for kernel compositing
data BlendKernelMode
  = KernelBlendNormal
  | KernelBlendAdd
  | KernelBlendMultiply
  | KernelBlendScreen
  | KernelBlendOverlay
  | KernelBlendSoftLight
  | KernelBlendHardLight
  | KernelBlendDifference

derive instance eqBlendKernelMode :: Eq BlendKernelMode

instance showBlendKernelMode :: Show BlendKernelMode where
  show KernelBlendNormal = "Normal"
  show KernelBlendAdd = "Add"
  show KernelBlendMultiply = "Multiply"
  show KernelBlendScreen = "Screen"
  show KernelBlendOverlay = "Overlay"
  show KernelBlendSoftLight = "SoftLight"
  show KernelBlendHardLight = "HardLight"
  show KernelBlendDifference = "Difference"

-- | Mask kernel
newtype MaskKernel = MaskKernel
  { source :: KernelInput      -- Source to mask
  , mask :: KernelInput        -- Mask input
  , channel :: MaskChannel     -- Which mask channel to use
  , invert :: Boolean          -- Invert mask
  , config :: KernelConfig
  }

derive instance eqMaskKernel :: Eq MaskKernel

instance showMaskKernel :: Show MaskKernel where
  show (MaskKernel k) = "(MaskKernel " <> show k.channel <> ")"

-- | Mask channel selection
data MaskChannel
  = MaskRed
  | MaskGreen
  | MaskBlue
  | MaskAlpha
  | MaskLuminance

derive instance eqMaskChannel :: Eq MaskChannel

instance showMaskChannel :: Show MaskChannel where
  show MaskRed = "Red"
  show MaskGreen = "Green"
  show MaskBlue = "Blue"
  show MaskAlpha = "Alpha"
  show MaskLuminance = "Luminance"

-- | Alpha adjustment kernel
newtype AlphaKernel = AlphaKernel
  { source :: KernelInput
  , operation :: AlphaOperation
  , threshold :: Number        -- For threshold operations
  , feather :: Number          -- Edge softness
  , config :: KernelConfig
  }

derive instance eqAlphaKernel :: Eq AlphaKernel

instance showAlphaKernel :: Show AlphaKernel where
  show (AlphaKernel k) = "(AlphaKernel " <> show k.operation <> ")"

-- | Alpha operations
data AlphaOperation
  = AlphaMultiply Number       -- Multiply alpha by factor
  | AlphaThreshold             -- Binary threshold
  | AlphaInvert                -- Invert alpha
  | AlphaRemapRange Number Number  -- Remap alpha range

derive instance eqAlphaOperation :: Eq AlphaOperation

instance showAlphaOperation :: Show AlphaOperation where
  show (AlphaMultiply f) = "(AlphaMultiply " <> show f <> ")"
  show AlphaThreshold = "AlphaThreshold"
  show AlphaInvert = "AlphaInvert"
  show (AlphaRemapRange min' max') = "(AlphaRemapRange " <> show min' <> " " <> show max' <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // kernel construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default kernel config
defaultConfig :: Int -> Int -> KernelConfig
defaultConfig w h =
  { workgroupSize: { x: 16, y: 16, z: 1 }
  , input: InputPrevious
  , output: OutputNext
  , width: w
  , height: h
  , channels: 4
  }

-- Blur kernel constructors
gaussianBlurKernel :: Int -> Number -> Int -> Int -> Int -> ComputeKernel
gaussianBlurKernel radius sigma passes width height = KernelBlur $ BlurGaussian $ GaussianBlurKernel
  { radius, sigma, passes, config: defaultConfig width height }

directionalBlurKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
directionalBlurKernel angle distance samples width height = KernelBlur $ BlurDirectional $ DirectionalBlurKernel
  { angle, distance, samples, config: defaultConfig width height }

radialBlurKernel :: Number -> Number -> Number -> Int -> Int -> Int -> ComputeKernel
radialBlurKernel centerX centerY amount samples width height = KernelBlur $ BlurRadial $ RadialBlurKernel
  { centerX, centerY, amount, blurType: RadialTypeSpin, samples, config: defaultConfig width height }

boxBlurKernel :: Int -> Int -> Int -> Int -> ComputeKernel
boxBlurKernel radius iterations width height = KernelBlur $ BlurBox $ BoxBlurKernel
  { radius, iterations, config: defaultConfig width height }

-- Glow kernel constructors
bloomKernel :: Number -> Number -> Int -> Int -> Int -> Int -> ComputeKernel
bloomKernel threshold intensity radius passes width height = KernelGlow $ GlowBloom $ BloomKernel
  { threshold, intensity, radius, passes
  , tint: { r: 1.0, g: 1.0, b: 1.0, enabled: false }
  , config: defaultConfig width height }

outerGlowKernel :: GlowTint -> Int -> Number -> Int -> Int -> ComputeKernel
outerGlowKernel color radius intensity width height = KernelGlow $ GlowOuter $ OuterGlowKernel
  { color, radius, intensity, falloff: FalloffGaussian, config: defaultConfig width height }

innerGlowKernel :: GlowTint -> Int -> Number -> Number -> Int -> Int -> ComputeKernel
innerGlowKernel color radius intensity choke width height = KernelGlow $ GlowInner $ InnerGlowKernel
  { color, radius, intensity, choke, config: defaultConfig width height }

-- Noise kernel constructors
perlinNoiseKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
perlinNoiseKernel scale seed octaves width height = KernelNoise $ NoisePerlin $ PerlinNoiseKernel
  { scale, seed, octaves, persistence: 0.5, lacunarity: 2.0, time: 0.0, config: defaultConfig width height }

simplexNoiseKernel :: Number -> Int -> Int -> Int -> ComputeKernel
simplexNoiseKernel scale seed width height = KernelNoise $ NoiseSimplex $ SimplexNoiseKernel
  { scale, seed, time: 0.0, config: defaultConfig width height }

fbmNoiseKernel :: Number -> Int -> Int -> Number -> Number -> Int -> Int -> ComputeKernel
fbmNoiseKernel scale seed octaves persistence lacunarity width height = KernelNoise $ NoiseFBM $ FBMNoiseKernel
  { scale, seed, octaves, persistence, lacunarity, time: 0.0, turbulent: false, config: defaultConfig width height }

worleyNoiseKernel :: Number -> Int -> Int -> Int -> Int -> ComputeKernel
worleyNoiseKernel scale seed cellCount width height = KernelNoise $ NoiseWorley $ WorleyNoiseKernel
  { scale, seed, cellCount, distanceType: WorleyEuclidean, time: 0.0, config: defaultConfig width height }

-- Particle kernel constructors
particlePhysicsKernel :: Int -> Number -> Number -> Number -> Int -> Int -> ComputeKernel
particlePhysicsKernel particleCount deltaTime gravity damping width height = KernelParticle $ ParticlePhysics $ ParticlePhysicsKernel
  { particleCount, deltaTime, gravity, damping, bounds: BoundsWrap, forces: [], config: defaultConfig width height }

particleEmitKernel :: Int -> Number -> Number -> Number -> Number -> Number -> Int -> Int -> Int -> ComputeKernel
particleEmitKernel emitCount positionX positionY spread velocity lifetime seed width height = KernelParticle $ ParticleEmit $ ParticleEmitKernel
  { emitCount, positionX, positionY, spread, velocity, velocityVariance: 0.1, lifetime, lifetimeVariance: 0.2, seed, config: defaultConfig width height }

-- Color kernel constructors
colorGradingKernel :: Number -> Number -> Number -> Int -> Int -> ComputeKernel
colorGradingKernel exposure contrast saturation width height = KernelColor $ ColorGrading $ ColorGradingKernel
  { exposure, contrast, saturation, temperature: 0.0, tint: 0.0
  , shadows: { r: 0.0, g: 0.0, b: 0.0 }
  , midtones: { r: 0.0, g: 0.0, b: 0.0 }
  , highlights: { r: 0.0, g: 0.0, b: 0.0 }
  , config: defaultConfig width height }

toneMappingKernel :: ToneMappingAlgorithm -> Number -> Int -> Int -> ComputeKernel
toneMappingKernel algorithm whitePoint width height = KernelColor $ ColorToneMapping $ ToneMappingKernel
  { algorithm, whitePoint, config: defaultConfig width height }

-- Distortion kernel constructors
displacementKernel :: KernelInput -> Number -> Number -> Int -> Int -> ComputeKernel
displacementKernel mapInput scaleX scaleY width height = KernelDistortion $ DistortDisplacement $ DisplacementKernel
  { mapInput, scaleX, scaleY, channel: DisplaceLuminance, config: defaultConfig width height }

warpKernel :: WarpType -> Number -> Number -> Number -> Int -> Int -> ComputeKernel
warpKernel warpType strength centerX centerY width height = KernelDistortion $ DistortWarp $ WarpKernel
  { warpType, strength, centerX, centerY, config: defaultConfig width height }

-- Composite kernel constructors
blendKernel :: KernelInput -> KernelInput -> BlendKernelMode -> Number -> Int -> Int -> ComputeKernel
blendKernel layerA layerB mode opacity width height = KernelComposite $ CompositeBlend $ BlendKernel
  { layerA, layerB, mode, opacity, config: defaultConfig width height }

maskKernel :: KernelInput -> KernelInput -> MaskChannel -> Boolean -> Int -> Int -> ComputeKernel
maskKernel source mask' channel invert width height = KernelComposite $ CompositeMask $ MaskKernel
  { source, mask: mask', channel, invert, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // kernel dispatch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute appropriate workgroup size for kernel type
computeWorkgroupSize :: ComputeKernel -> WorkgroupSize
computeWorkgroupSize = case _ of
  KernelBlur _ -> { x: 16, y: 16, z: 1 }         -- 2D image processing
  KernelGlow _ -> { x: 16, y: 16, z: 1 }
  KernelNoise _ -> { x: 8, y: 8, z: 8 }          -- 3D noise (x, y, octave)
  KernelParticle _ -> { x: 256, y: 1, z: 1 }     -- 1D particle array
  KernelColor _ -> { x: 16, y: 16, z: 1 }
  KernelDistortion _ -> { x: 16, y: 16, z: 1 }
  KernelComposite _ -> { x: 16, y: 16, z: 1 }
  KernelSequence _ -> { x: 16, y: 16, z: 1 }     -- Default for sequences
  KernelParallel _ -> { x: 16, y: 16, z: 1 }
  KernelConditional c -> computeWorkgroupSize c.thenKernel
  KernelNoop -> { x: 1, y: 1, z: 1 }

-- | Compute dispatch size from kernel config
computeDispatchSize :: KernelConfig -> DispatchSize
computeDispatchSize config =
  { x: divCeil config.width config.workgroupSize.x
  , y: divCeil config.height config.workgroupSize.y
  , z: divCeil config.channels config.workgroupSize.z
  }
  where
    divCeil a b = (a + b - 1) / b

-- | Estimate kernel cost in milliseconds (rough)
estimateKernelCost :: ComputeKernel -> Number
estimateKernelCost = case _ of
  KernelBlur (BlurGaussian (GaussianBlurKernel k)) -> 
    Int.toNumber k.radius * Int.toNumber k.passes * 0.01
  KernelBlur (BlurDirectional (DirectionalBlurKernel k)) ->
    Int.toNumber k.samples * 0.005
  KernelBlur (BlurRadial (RadialBlurKernel k)) ->
    Int.toNumber k.samples * 0.008
  KernelBlur (BlurBox (BoxBlurKernel k)) ->
    Int.toNumber k.iterations * 0.003
  KernelGlow (GlowBloom (BloomKernel k)) ->
    Int.toNumber k.passes * Int.toNumber k.radius * 0.015
  KernelGlow _ -> 0.5
  KernelNoise (NoiseFBM (FBMNoiseKernel k)) ->
    Int.toNumber k.octaves * 0.1
  KernelNoise _ -> 0.2
  KernelParticle (ParticlePhysics (ParticlePhysicsKernel k)) ->
    Int.toNumber k.particleCount * 0.00001
  KernelParticle _ -> 0.1
  KernelColor _ -> 0.1
  KernelDistortion _ -> 0.2
  KernelComposite _ -> 0.1
  KernelSequence kernels -> foldlSum (map estimateKernelCost kernels)
  KernelParallel kernels -> foldlMax (map estimateKernelCost kernels)
  KernelConditional c -> estimateKernelCost c.thenKernel
  KernelNoop -> 0.0
  where
    foldlSum arr = foldlArr (\acc x -> acc + x) 0.0 arr
    foldlMax arr = foldlArr (\acc x -> if x > acc then x else acc) 0.0 arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // kernel composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence kernels (execute in order)
sequenceKernels :: Array ComputeKernel -> ComputeKernel
sequenceKernels = KernelSequence

-- | Parallel kernels (execute simultaneously to different outputs)
parallelKernels :: Array ComputeKernel -> ComputeKernel
parallelKernels = KernelParallel

-- | Conditional kernel execution
conditionalKernel :: KernelCondition -> ComputeKernel -> Maybe ComputeKernel -> ComputeKernel
conditionalKernel condition thenKernel elseKernel = KernelConditional
  { condition, thenKernel, elseKernel }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard Gaussian blur preset (balanced quality/performance)
standardGaussian :: Int -> Int -> ComputeKernel
standardGaussian = gaussianBlurKernel 8 4.0 2

-- | Fast Gaussian blur preset (performance priority)
fastGaussian :: Int -> Int -> ComputeKernel
fastGaussian = boxBlurKernel 8 3

-- | Quality Gaussian blur preset (quality priority)
qualityGaussian :: Int -> Int -> ComputeKernel
qualityGaussian = gaussianBlurKernel 16 8.0 4

-- | Standard bloom preset
standardBloom :: Int -> Int -> ComputeKernel
standardBloom = bloomKernel 0.8 1.0 8 3

-- | Soft bloom preset (subtle)
softBloom :: Int -> Int -> ComputeKernel
softBloom = bloomKernel 0.9 0.5 12 2

-- | Intense bloom preset (dramatic)
intenseBloom :: Int -> Int -> ComputeKernel
intenseBloom = bloomKernel 0.6 1.5 16 4

-- | Standard noise preset
standardNoise :: Int -> Int -> ComputeKernel
standardNoise = fbmNoiseKernel 1.0 42 4 0.5 2.0

-- | Animated noise preset
animatedNoise :: Number -> Int -> Int -> ComputeKernel
animatedNoise time width height = KernelNoise $ NoiseFBM $ FBMNoiseKernel
  { scale: 1.0, seed: 42, octaves: 4, persistence: 0.5, lacunarity: 2.0
  , time, turbulent: false, config: defaultConfig width height }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Array.uncons helper
foldlArr :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArr f init arr = case Array.uncons arr of
  Nothing -> init
  Just { head, tail } -> foldlArr f (f init head) tail
