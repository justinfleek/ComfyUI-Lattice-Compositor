-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // composition // source // generative
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generative Sources — Procedural, Noise, Diffusion, AI-Generated.
-- |
-- | Algorithmically generated pixel content.

module Hydrogen.Composition.Source.Generative
  ( -- * Procedural
    ProceduralSpec
  , ShaderRef(..)
  , procedural
  
  -- * Noise
  , NoiseSpec
  , NoiseType(..)
  , noise
  
  -- * Diffusion
  , DiffusionSpec
  , Sampler(..)
  , Scheduler(..)
  , ModelRef(..)
  , PromptEmbedding(..)
  , DiffusionSize
  , diffusionSize
  , diffusion
  
  -- * ControlNet
  , ControlNetSpec
  , ControlNetType(..)
  , controlNet
  
  -- * Generated Maps
  , GeneratedMapSpec
  , GeneratedMapType(..)
  , generatedMap
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , mod
  , (-)
  , (+)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.Opacity (Opacity)
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // procedural
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shader reference.
newtype ShaderRef = ShaderRef String

derive instance eqShaderRef :: Eq ShaderRef
derive instance ordShaderRef :: Ord ShaderRef

instance showShaderRef :: Show ShaderRef where
  show (ShaderRef s) = "(ShaderRef " <> show s <> ")"

-- | Procedural shader source.
type ProceduralSpec =
  { shader :: ShaderRef
  , uniforms :: Array { name :: String, value :: Number }
  , time :: Number        -- Animation time
  , opacity :: Opacity
  }

-- | Create a procedural source.
procedural :: ShaderRef -> Array { name :: String, value :: Number } -> Opacity -> ProceduralSpec
procedural shader uniforms opacity =
  { shader, uniforms, time: 0.0, opacity }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // noise
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Noise type.
data NoiseType
  = NoisePerlin
  | NoiseSimplex
  | NoiseWorley
  | NoiseFBM          -- Fractional Brownian Motion
  | NoiseVoronoi
  | NoiseTurbulence
  | NoiseRidged

derive instance eqNoiseType :: Eq NoiseType

instance showNoiseType :: Show NoiseType where
  show NoisePerlin = "perlin"
  show NoiseSimplex = "simplex"
  show NoiseWorley = "worley"
  show NoiseFBM = "fbm"
  show NoiseVoronoi = "voronoi"
  show NoiseTurbulence = "turbulence"
  show NoiseRidged = "ridged"

-- | Noise source.
type NoiseSpec =
  { noiseType :: NoiseType
  , scale :: Number           -- Noise scale
  , octaves :: Int            -- Detail levels
  , persistence :: Number     -- Amplitude falloff
  , lacunarity :: Number      -- Frequency multiplier
  , seed :: Int               -- Random seed
  , evolution :: Number       -- Animation time
  , color1 :: RGB             -- Low value color
  , color2 :: RGB             -- High value color
  , opacity :: Opacity
  }

-- | Create a noise source.
noise :: NoiseType -> Number -> Int -> RGB -> RGB -> Opacity -> NoiseSpec
noise noiseType scale octaves color1 color2 opacity =
  { noiseType, scale, octaves, color1, color2, opacity
  , persistence: 0.5, lacunarity: 2.0, seed: 0, evolution: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // diffusion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Diffusion model reference.
newtype ModelRef = ModelRef String

derive instance eqModelRef :: Eq ModelRef
derive instance ordModelRef :: Ord ModelRef

instance showModelRef :: Show ModelRef where
  show (ModelRef m) = "(ModelRef " <> show m <> ")"

-- | Pre-computed prompt embedding reference.
newtype PromptEmbedding = PromptEmbedding String

derive instance eqPromptEmbedding :: Eq PromptEmbedding
derive instance ordPromptEmbedding :: Ord PromptEmbedding

instance showPromptEmbedding :: Show PromptEmbedding where
  show (PromptEmbedding p) = "(PromptEmbedding " <> show p <> ")"

-- | Diffusion size (must be divisible by 8).
type DiffusionSize = { width :: Int, height :: Int }

-- | Create a diffusion size, rounding to nearest 8.
diffusionSize :: Int -> Int -> DiffusionSize
diffusionSize w h =
  { width: roundTo8 (Bounded.clampInt 64 4096 w)
  , height: roundTo8 (Bounded.clampInt 64 4096 h) }
  where
    roundTo8 n = let r = mod n 8 in if r == 0 then n else n + (8 - r)

-- | Sampler algorithm.
data Sampler
  = SamplerEuler
  | SamplerEulerA       -- Euler Ancestral
  | SamplerHeun
  | SamplerDPMPP2M      -- DPM++ 2M
  | SamplerDPMPP2MA     -- DPM++ 2M Ancestral
  | SamplerDPMPPSDE     -- DPM++ SDE
  | SamplerDPMPP3M      -- DPM++ 3M
  | SamplerDDIM
  | SamplerUniPC
  | SamplerLCM

derive instance eqSampler :: Eq Sampler

instance showSampler :: Show Sampler where
  show SamplerEuler = "euler"
  show SamplerEulerA = "euler_ancestral"
  show SamplerHeun = "heun"
  show SamplerDPMPP2M = "dpmpp_2m"
  show SamplerDPMPP2MA = "dpmpp_2m_ancestral"
  show SamplerDPMPPSDE = "dpmpp_sde"
  show SamplerDPMPP3M = "dpmpp_3m"
  show SamplerDDIM = "ddim"
  show SamplerUniPC = "uni_pc"
  show SamplerLCM = "lcm"

-- | Noise scheduler.
data Scheduler
  = SchedulerNormal
  | SchedulerKarras
  | SchedulerExponential
  | SchedulerSGMUniform
  | SchedulerSimple
  | SchedulerDDIMUniform
  | SchedulerBeta

derive instance eqScheduler :: Eq Scheduler

instance showScheduler :: Show Scheduler where
  show SchedulerNormal = "normal"
  show SchedulerKarras = "karras"
  show SchedulerExponential = "exponential"
  show SchedulerSGMUniform = "sgm_uniform"
  show SchedulerSimple = "simple"
  show SchedulerDDIMUniform = "ddim_uniform"
  show SchedulerBeta = "beta"

-- | ControlNet type.
data ControlNetType
  = ControlCanny
  | ControlDepth
  | ControlNormal
  | ControlPose
  | ControlSegmentation
  | ControlLineArt
  | ControlSoftEdge
  | ControlScribble
  | ControlTile
  | ControlInpaint

derive instance eqControlNetType :: Eq ControlNetType

instance showControlNetType :: Show ControlNetType where
  show ControlCanny = "canny"
  show ControlDepth = "depth"
  show ControlNormal = "normal"
  show ControlPose = "pose"
  show ControlSegmentation = "segmentation"
  show ControlLineArt = "lineart"
  show ControlSoftEdge = "softedge"
  show ControlScribble = "scribble"
  show ControlTile = "tile"
  show ControlInpaint = "inpaint"

-- | ControlNet specification.
type ControlNetSpec =
  { controlType :: ControlNetType
  , imageRef :: String
  , strength :: Number          -- 0-2
  , startPercent :: Number      -- When to start applying
  , endPercent :: Number        -- When to stop applying
  }

-- | Create a ControlNet spec.
controlNet :: ControlNetType -> String -> Number -> ControlNetSpec
controlNet controlType imageRef strength =
  { controlType, imageRef
  , strength: Bounded.clampNumber 0.0 2.0 strength
  , startPercent: 0.0, endPercent: 1.0 }

-- | Diffusion source specification.
type DiffusionSpec =
  { model :: ModelRef
  , sampler :: Sampler
  , scheduler :: Scheduler
  , steps :: Int                -- 1-150
  , guidance :: Number          -- CFG scale 1-30
  , seed :: Maybe Int           -- Deterministic seed
  , size :: DiffusionSize
  , prompt :: PromptEmbedding
  , negativePrompt :: Maybe PromptEmbedding
  , controlNets :: Array ControlNetSpec
  , denoise :: Number           -- Denoising strength 0-1
  , opacity :: Opacity
  }

-- | Create a diffusion source.
diffusion :: ModelRef -> Sampler -> Scheduler -> Int -> Number
          -> DiffusionSize -> PromptEmbedding -> Opacity -> DiffusionSpec
diffusion mdl sampler scheduler steps guidance size prompt opacity =
  { model: mdl, sampler, scheduler, size, prompt, opacity
  , steps: Bounded.clampInt 1 150 steps
  , guidance: Bounded.clampNumber 1.0 30.0 guidance
  , seed: Nothing, negativePrompt: Nothing
  , controlNets: [], denoise: 1.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // generated maps
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generated map type (AI-generated control maps).
data GeneratedMapType
  = GenDepth          -- MiDaS/ZoeDepth
  | GenNormal         -- Normal estimation
  | GenEdge           -- Canny/HED edges
  | GenPose           -- OpenPose skeleton
  | GenSegment        -- Semantic segmentation
  | GenLineArt        -- Line art extraction
  | GenSoftEdge       -- Soft edge detection
  | GenSalient        -- Saliency map

derive instance eqGeneratedMapType :: Eq GeneratedMapType

instance showGeneratedMapType :: Show GeneratedMapType where
  show GenDepth = "depth"
  show GenNormal = "normal"
  show GenEdge = "edge"
  show GenPose = "pose"
  show GenSegment = "segment"
  show GenLineArt = "lineart"
  show GenSoftEdge = "softedge"
  show GenSalient = "salient"

-- | Generated map source.
type GeneratedMapSpec =
  { mapType :: GeneratedMapType
  , sourceImage :: String       -- Image to process
  , opacity :: Opacity
  }

-- | Create a generated map source.
generatedMap :: GeneratedMapType -> String -> Opacity -> GeneratedMapSpec
generatedMap mapType sourceImage opacity = { mapType, sourceImage, opacity }
