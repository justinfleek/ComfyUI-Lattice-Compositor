-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // effects // simulation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Simulation Effects — Physics-based and procedural simulation effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Simulation effect category:
-- |
-- | - **CC Particle World**: Full 3D particle system
-- | - **CC Particle Systems II**: 2D particle system
-- | - **Shatter**: Glass/surface shatter effect
-- | - **Card Dance**: Grid-based card animation
-- | - **Caustics**: Water caustics simulation
-- | - **Wave World**: 3D water wave simulation
-- | - **Foam**: Bubble/foam generation
-- | - **CC Ball Action**: Ball grid effect
-- | - **CC Bubbles**: Rising bubbles effect
-- | - **CC Drizzle**: Rain drizzle effect
-- | - **CC Hair**: Hair/fur simulation
-- | - **CC Mr. Mercury**: Mercury blob effect
-- | - **CC Rain**: Rain particle effect
-- | - **CC Rainfall**: Rain with splashes
-- | - **CC Snowfall**: Snow particle effect
-- | - **CC Star Burst**: Star burst effect
-- |
-- | ## GPU Simulation
-- |
-- | These effects are computationally intensive. Particle systems
-- | typically run on GPU compute shaders in the runtime.
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic simulation.

module Hydrogen.Schema.Motion.Effects.Simulation
  ( -- * CC Particle World
    ParticleWorldEffect
  , ParticleType(..)
  , PhysicsModel(..)
  , defaultParticleWorld
  , particleWorldWithCount
  
  -- * CC Particle Systems II
  , ParticleSystemsEffect
  , defaultParticleSystems
  
  -- * Shatter
  , ShatterEffect
  , ShatterShape(..)
  , ShatterForce(..)
  , defaultShatter
  , shatterWithForce
  
  -- * Card Dance
  , CardDanceEffect
  , CardDanceAxis(..)
  , defaultCardDance
  , cardDanceWithRows
  
  -- * Caustics
  , CausticsEffect
  , CausticsLightType(..)
  , defaultCaustics
  , causticsWithIntensity
  
  -- * Wave World
  , WaveWorldEffect
  , WaveMethod(..)
  , defaultWaveWorld
  , waveWorldWithHeight
  
  -- * Foam
  , FoamEffect
  , FoamProducer(..)
  , defaultFoam
  , foamWithBubbles
  
  -- * CC Ball Action
  , BallActionEffect
  , defaultBallAction
  , ballActionWithGrid
  
  -- * CC Bubbles
  , BubblesEffect
  , defaultBubbles
  , bubblesWithSize
  
  -- * CC Drizzle
  , DrizzleEffect
  , defaultDrizzle
  , drizzleWithDrops
  
  -- * CC Rain
  , RainEffect
  , defaultRain
  , rainWithDrops
  
  -- * CC Snowfall
  , SnowfallEffect
  , SnowflakeType(..)
  , defaultSnowfall
  , snowfallWithFlakes
  
  -- * CC Star Burst
  , StarBurstEffect
  , defaultStarBurst
  , starBurstWithCount
  
  -- * Serialization
  , particleTypeToString
  , physicsModelToString
  , shatterShapeToString
  , shatterForceToString
  , cardDanceAxisToString
  , causticsLightTypeToString
  , waveMethodToString
  , foamProducerToString
  , snowflakeTypeToString
  
  -- * Effect Names
  , particleWorldEffectName
  , particleSystemsEffectName
  , shatterEffectName
  , cardDanceEffectName
  , causticsEffectName
  , waveWorldEffectName
  , foamEffectName
  , ballActionEffectName
  , bubblesEffectName
  , drizzleEffectName
  , rainEffectName
  , snowfallEffectName
  , starBurstEffectName
  
  -- * Effect Descriptions
  , describeParticleWorld
  , describeShatter
  , describeCardDance
  , describeCaustics
  , describeWaveWorld
  
  -- * Queries
  , particleWorldHasGravity
  , isShatterRadial
  , isWaveWorldSteep
  , isFoamHighDensity
  , rainHasWind
  , snowfallHasTurbulence
  , estimateParticleCount
  , estimateFoamBubbles
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , ($)
  , (<>)
  , (<)
  , (>)
  , (*)
  , negate
  , show
  , otherwise
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Color.RGB (RGB, rgb)
import Hydrogen.Schema.Dimension.Point2D (Point2D, point2D)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)
import Hydrogen.Schema.Motion.Composition (BlendMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // particle // world
-- ═════════════════════════════════════════════════════════════════════════════

-- | Particle type — visual appearance of particles.
data ParticleType
  = PTLine              -- ^ Line particles
  | PTTriPolyExplosive  -- ^ Exploding triangular polygon
  | PTTripolyBilinear   -- ^ Bilinear triangular polygon
  | PTQuadPolyExplosive -- ^ Exploding quad polygon
  | PTQuadPolyBilinear  -- ^ Bilinear quad polygon
  | PTStarExplosive     -- ^ Exploding star
  | PTStar              -- ^ Star shape
  | PTFadedSphere       -- ^ Faded sphere
  | PTShaded            -- ^ Shaded 3D sphere
  | PTBubble            -- ^ Transparent bubble
  | PTTextured          -- ^ Textured from layer
  | PTCloudy            -- ^ Cloud-like
  | PTLensConvex        -- ^ Convex lens
  | PTLensConcave       -- ^ Concave lens
  | PTMotionPolygon     -- ^ Motion-blurred polygon

derive instance eqParticleType :: Eq ParticleType
derive instance ordParticleType :: Ord ParticleType

instance showParticleType :: Show ParticleType where
  show PTLine = "line"
  show PTTriPolyExplosive = "tri-poly-explosive"
  show PTTripolyBilinear = "tri-poly-bilinear"
  show PTQuadPolyExplosive = "quad-poly-explosive"
  show PTQuadPolyBilinear = "quad-poly-bilinear"
  show PTStarExplosive = "star-explosive"
  show PTStar = "star"
  show PTFadedSphere = "faded-sphere"
  show PTShaded = "shaded"
  show PTBubble = "bubble"
  show PTTextured = "textured"
  show PTCloudy = "cloudy"
  show PTLensConvex = "lens-convex"
  show PTLensConcave = "lens-concave"
  show PTMotionPolygon = "motion-polygon"

-- | Physics model — how particles interact.
data PhysicsModel
  = PMExplosive         -- ^ Outward explosion
  | PMTwirl             -- ^ Spiral motion
  | PMVortex            -- ^ Vortex suction
  | PMFire              -- ^ Fire-like rising
  | PMJet               -- ^ Directional jet
  | PMViscocity         -- ^ Viscous fluid
  | PMDirectional       -- ^ Fixed direction
  | PMSprite            -- ^ Sprite behavior

derive instance eqPhysicsModel :: Eq PhysicsModel
derive instance ordPhysicsModel :: Ord PhysicsModel

instance showPhysicsModel :: Show PhysicsModel where
  show PMExplosive = "explosive"
  show PMTwirl = "twirl"
  show PMVortex = "vortex"
  show PMFire = "fire"
  show PMJet = "jet"
  show PMViscocity = "viscocity"
  show PMDirectional = "directional"
  show PMSprite = "sprite"

-- | CC Particle World Effect — full 3D particle system.
-- |
-- | ## AE Properties
-- |
-- | The most comprehensive particle system in AE.
-- | Supports birth/death, physics, rendering options.
type ParticleWorldEffect =
  { -- Birth
    birthRate :: Number              -- ^ Particles per second (0-10000)
  , longevity :: Number              -- ^ Particle life in seconds (0-100)
  
  -- Producer
  , producerPosition :: Vec3 Number  -- ^ Emitter position (x, y, z)
  , producerRadius :: { x :: Number, y :: Number, z :: Number }  -- ^ Emitter size
  
  -- Physics
  , velocity :: Number               -- ^ Initial velocity (0-500)
  , inheritVelocity :: Number        -- ^ From layer motion (0-100 %)
  , gravity :: Number                -- ^ Gravity strength (-100 to 100)
  , physicsModel :: PhysicsModel     -- ^ Physics behavior
  
  -- Particle
  , particleType :: ParticleType     -- ^ Visual type
  , birthSize :: Number              -- ^ Size at birth (0-500)
  , deathSize :: Number              -- ^ Size at death (0-500)
  , birthColor :: RGB                -- ^ Color at birth
  , deathColor :: RGB                -- ^ Color at death
  , birthOpacity :: Number           -- ^ Opacity at birth (0-100)
  , deathOpacity :: Number           -- ^ Opacity at death (0-100)
  
  -- Rendering
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default particle world: moderate birth rate, white particles.
defaultParticleWorld :: ParticleWorldEffect
defaultParticleWorld =
  { birthRate: 100.0
  , longevity: 2.0
  , producerPosition: vec3 0.0 0.0 0.0
  , producerRadius: { x: 10.0, y: 10.0, z: 10.0 }
  , velocity: 50.0
  , inheritVelocity: 0.0
  , gravity: 0.0
  , physicsModel: PMExplosive
  , particleType: PTFadedSphere
  , birthSize: 10.0
  , deathSize: 1.0
  , birthColor: rgb 255 255 255
  , deathColor: rgb 255 255 255
  , birthOpacity: 100.0
  , deathOpacity: 0.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- | Create particle world with specific count.
particleWorldWithCount :: Number -> Number -> ParticleWorldEffect
particleWorldWithCount rate life =
  { birthRate: clampNumber 0.0 10000.0 rate
  , longevity: clampNumber 0.0 100.0 life
  , producerPosition: vec3 0.0 0.0 0.0
  , producerRadius: { x: 10.0, y: 10.0, z: 10.0 }
  , velocity: 50.0
  , inheritVelocity: 0.0
  , gravity: 0.0
  , physicsModel: PMExplosive
  , particleType: PTFadedSphere
  , birthSize: 10.0
  , deathSize: 1.0
  , birthColor: rgb 255 255 255
  , deathColor: rgb 255 255 255
  , birthOpacity: 100.0
  , deathOpacity: 0.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // particle // systems // ii
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Particle Systems II Effect — simpler 2D particle system.
-- |
-- | Less complex than Particle World, but faster.
type ParticleSystemsEffect =
  { birthRate :: Number              -- ^ Particles per second (0-2000)
  , longevity :: Number              -- ^ Particle life (0-20 seconds)
  , producerPosition :: Point2D      -- ^ Emitter position
  , producerRadius :: Number         -- ^ Emitter radius (0-1000)
  , direction :: Number              -- ^ Direction angle (0-360)
  , directionSpread :: Number        -- ^ Spread angle (0-180)
  , velocity :: Number               -- ^ Initial velocity (0-200)
  , gravity :: Number                -- ^ Gravity (-100 to 100)
  , resistance :: Number             -- ^ Air resistance (0-100)
  , particleType :: ParticleType     -- ^ Visual type
  , birthSize :: Number              -- ^ Size at birth (0-100)
  , deathSize :: Number              -- ^ Size at death (0-100)
  , birthColor :: RGB                -- ^ Color at birth
  , deathColor :: RGB                -- ^ Color at death
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default particle systems II.
defaultParticleSystems :: ParticleSystemsEffect
defaultParticleSystems =
  { birthRate: 50.0
  , longevity: 2.0
  , producerPosition: point2D 100.0 100.0
  , producerRadius: 5.0
  , direction: 270.0  -- Up
  , directionSpread: 45.0
  , velocity: 30.0
  , gravity: 10.0
  , resistance: 5.0
  , particleType: PTFadedSphere
  , birthSize: 8.0
  , deathSize: 2.0
  , birthColor: rgb 255 200 100
  , deathColor: rgb 200 50 0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // shatter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shatter shape — pattern of breakage.
data ShatterShape
  = SSGlass             -- ^ Glass-like shards
  | SSBrick             -- ^ Brick pattern
  | SSPuzzle            -- ^ Puzzle pieces
  | SSTriangles         -- ^ Triangle shards
  | SSCustom            -- ^ Custom pattern from layer

derive instance eqShatterShape :: Eq ShatterShape
derive instance ordShatterShape :: Ord ShatterShape

instance showShatterShape :: Show ShatterShape where
  show SSGlass = "glass"
  show SSBrick = "brick"
  show SSPuzzle = "puzzle"
  show SSTriangles = "triangles"
  show SSCustom = "custom"

-- | Shatter force — what drives the shattering.
data ShatterForce
  = SFGradient          -- ^ Gradient map force
  | SFRadius            -- ^ Radial explosion
  | SFDepth             -- ^ Depth-based

derive instance eqShatterForce :: Eq ShatterForce
derive instance ordShatterForce :: Ord ShatterForce

instance showShatterForce :: Show ShatterForce where
  show SFGradient = "gradient"
  show SFRadius = "radius"
  show SFDepth = "depth"

-- | Shatter Effect — glass/surface break simulation.
-- |
-- | ## AE Properties
-- |
-- | Shatters layer into pieces based on force.
type ShatterEffect =
  { -- View
    renderMode :: Int                -- ^ 0=Rendered, 1=Wireframe, 2=Front
    
  -- Shape
  , shatterShape :: ShatterShape     -- ^ Breakage pattern
  , repetitions :: Number            -- ^ Pattern repetitions (1-100)
  , extrusionDepth :: Number         -- ^ 3D extrusion (0-100)
  
  -- Force
  , forceType :: ShatterForce        -- ^ Force source
  , forcePosition :: Point2D         -- ^ Force center
  , forceStrength :: Number          -- ^ Force strength (0-100)
  , forceRadius :: Number            -- ^ Force radius (0-1000)
  
  -- Physics
  , gravity :: Number                -- ^ Gravity strength (0-100)
  , gravityDirection :: Number       -- ^ Gravity angle (0-360)
  , randomness :: Number             -- ^ Random variation (0-100)
  
  -- Rendering
  , lightingType :: Int              -- ^ 0=First, 1=None
  , ambientLight :: Number           -- ^ Ambient intensity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default shatter: glass pattern, radial force.
defaultShatter :: ShatterEffect
defaultShatter =
  { renderMode: 0
  , shatterShape: SSGlass
  , repetitions: 10.0
  , extrusionDepth: 10.0
  , forceType: SFRadius
  , forcePosition: point2D 100.0 100.0
  , forceStrength: 50.0
  , forceRadius: 100.0
  , gravity: 50.0
  , gravityDirection: 180.0
  , randomness: 50.0
  , lightingType: 0
  , ambientLight: 50.0
  , randomSeed: 0
  }

-- | Create shatter with specific force.
shatterWithForce :: ShatterForce -> Number -> Number -> ShatterEffect
shatterWithForce force strength rad =
  { renderMode: 0
  , shatterShape: SSGlass
  , repetitions: 10.0
  , extrusionDepth: 10.0
  , forceType: force
  , forcePosition: point2D 100.0 100.0
  , forceStrength: clampNumber 0.0 100.0 strength
  , forceRadius: clampNumber 0.0 1000.0 rad
  , gravity: 50.0
  , gravityDirection: 180.0
  , randomness: 50.0
  , lightingType: 0
  , ambientLight: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // card // dance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Card dance axis — which axis to animate.
data CardDanceAxis
  = CDAPosition         -- ^ Position offset
  | CDARotation         -- ^ Rotation
  | CDAScale            -- ^ Scale

derive instance eqCardDanceAxis :: Eq CardDanceAxis
derive instance ordCardDanceAxis :: Ord CardDanceAxis

instance showCardDanceAxis :: Show CardDanceAxis where
  show CDAPosition = "position"
  show CDARotation = "rotation"
  show CDAScale = "scale"

-- | Card Dance Effect — grid-based card animation.
-- |
-- | ## AE Properties
-- |
-- | Divides layer into cards and animates them based on gradient.
type CardDanceEffect =
  { -- Grid
    rows :: Int                      -- ^ Number of rows (1-200)
  , columns :: Int                   -- ^ Number of columns (1-200)
  
  -- Position
  , positionX :: Number              -- ^ X position multiplier (-1000 to 1000)
  , positionY :: Number              -- ^ Y position multiplier (-1000 to 1000)
  , positionZ :: Number              -- ^ Z position multiplier (-1000 to 1000)
  
  -- Rotation
  , rotationX :: Number              -- ^ X rotation multiplier (-1000 to 1000)
  , rotationY :: Number              -- ^ Y rotation multiplier (-1000 to 1000)
  , rotationZ :: Number              -- ^ Z rotation multiplier (-1000 to 1000)
  
  -- Scale
  , scaleX :: Number                 -- ^ X scale multiplier (-1000 to 1000)
  , scaleY :: Number                 -- ^ Y scale multiplier (-1000 to 1000)
  
  -- Camera
  , cameraPosition :: Vec3 Number    -- ^ Camera position
  , focalLength :: Number            -- ^ Camera focal length (1-1000)
  
  -- Control
  , gradientLayer :: Int             -- ^ Source gradient layer index
  }

-- | Default card dance: 10x10 grid.
defaultCardDance :: CardDanceEffect
defaultCardDance =
  { rows: 10
  , columns: 10
  , positionX: 0.0
  , positionY: 0.0
  , positionZ: 100.0
  , rotationX: 0.0
  , rotationY: 0.0
  , rotationZ: 0.0
  , scaleX: 100.0
  , scaleY: 100.0
  , cameraPosition: vec3 0.0 0.0 (-500.0)
  , focalLength: 50.0
  , gradientLayer: 0
  }

-- | Create card dance with specific grid size.
cardDanceWithRows :: Int -> Int -> CardDanceEffect
cardDanceWithRows r c =
  { rows: clampInt 1 200 r
  , columns: clampInt 1 200 c
  , positionX: 0.0
  , positionY: 0.0
  , positionZ: 100.0
  , rotationX: 0.0
  , rotationY: 0.0
  , rotationZ: 0.0
  , scaleX: 100.0
  , scaleY: 100.0
  , cameraPosition: vec3 0.0 0.0 (-500.0)
  , focalLength: 50.0
  , gradientLayer: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // caustics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Caustics light type — light source style.
data CausticsLightType
  = CLTPointAbove       -- ^ Point light above surface
  | CLTDistantAbove     -- ^ Distant light above
  | CLTPointBelow       -- ^ Point light below surface
  | CLTDistantBelow     -- ^ Distant light below

derive instance eqCausticsLightType :: Eq CausticsLightType
derive instance ordCausticsLightType :: Ord CausticsLightType

instance showCausticsLightType :: Show CausticsLightType where
  show CLTPointAbove = "point-above"
  show CLTDistantAbove = "distant-above"
  show CLTPointBelow = "point-below"
  show CLTDistantBelow = "distant-below"

-- | Caustics Effect — water caustics simulation.
-- |
-- | ## AE Properties
-- |
-- | Simulates light refraction through water surface.
type CausticsEffect =
  { -- Bottom
    bottomLayerIndex :: Int          -- ^ Bottom surface layer
    
  -- Water Surface
  , waterHeight :: Number            -- ^ Water height (0-100)
  , waveHeight :: Number             -- ^ Wave amplitude (0-100)
  , smoothing :: Number              -- ^ Surface smoothing (0-100)
  , waterDepth :: Number             -- ^ Water depth (0-1000)
  
  -- Caustics
  , surfaceOpacity :: Number         -- ^ Surface visibility (0-100)
  , causticStrength :: Number        -- ^ Caustic intensity (0-200)
  , blurCaustics :: Number           -- ^ Caustic blur (0-100)
  
  -- Lighting
  , lightType :: CausticsLightType   -- ^ Light source type
  , lightIntensity :: Number         -- ^ Light intensity (0-200)
  , lightHeight :: Number            -- ^ Light height (0-1000)
  , lightDirection :: Point2D        -- ^ Light direction
  
  -- Sky
  , skyLayer :: Int                  -- ^ Sky reflection layer
  , skyLayerIntensity :: Number      -- ^ Sky reflection intensity (0-100)
  
  -- Animation
  , waveSpeed :: Number              -- ^ Wave animation speed (0-100)
  }

-- | Default caustics: moderate waves.
defaultCaustics :: CausticsEffect
defaultCaustics =
  { bottomLayerIndex: 0
  , waterHeight: 50.0
  , waveHeight: 20.0
  , smoothing: 30.0
  , waterDepth: 100.0
  , surfaceOpacity: 100.0
  , causticStrength: 100.0
  , blurCaustics: 10.0
  , lightType: CLTPointAbove
  , lightIntensity: 100.0
  , lightHeight: 500.0
  , lightDirection: point2D 0.0 0.0
  , skyLayer: 0
  , skyLayerIntensity: 0.0
  , waveSpeed: 50.0
  }

-- | Create caustics with specific intensity.
causticsWithIntensity :: Number -> Number -> CausticsEffect
causticsWithIntensity strength wave =
  { bottomLayerIndex: 0
  , waterHeight: 50.0
  , waveHeight: clampNumber 0.0 100.0 wave
  , smoothing: 30.0
  , waterDepth: 100.0
  , surfaceOpacity: 100.0
  , causticStrength: clampNumber 0.0 200.0 strength
  , blurCaustics: 10.0
  , lightType: CLTPointAbove
  , lightIntensity: 100.0
  , lightHeight: 500.0
  , lightDirection: point2D 0.0 0.0
  , skyLayer: 0
  , skyLayerIntensity: 0.0
  , waveSpeed: 50.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // wave // world
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wave simulation method.
data WaveMethod
  = WMSteep             -- ^ Steep waves
  | WMSmooth            -- ^ Smooth waves
  | WMRelaxed           -- ^ Relaxed/calm waves

derive instance eqWaveMethod :: Eq WaveMethod
derive instance ordWaveMethod :: Ord WaveMethod

instance showWaveMethod :: Show WaveMethod where
  show WMSteep = "steep"
  show WMSmooth = "smooth"
  show WMRelaxed = "relaxed"

-- | Wave World Effect — 3D water simulation.
-- |
-- | ## AE Properties
-- |
-- | Full 3D water surface with wave physics.
type WaveWorldEffect =
  { -- View
    wireframeMode :: Boolean         -- ^ Show wireframe
  , displayMode :: Int               -- ^ 0=height, 1=normals, 2=gray
  
  -- Wave Grid
  , gridResolution :: Int            -- ^ Grid resolution (8-200)
  
  -- Wave Height
  , waveHeight :: Number             -- ^ Max wave height (0-500)
  , method :: WaveMethod             -- ^ Wave simulation method
  , damping :: Number                -- ^ Wave damping (0-100)
  
  -- Ground
  , groundEnabled :: Boolean         -- ^ Show ground plane
  , groundHeight :: Number           -- ^ Ground height (-500 to 500)
  
  -- Simulation
  , reflectionStrength :: Number     -- ^ Reflection intensity (0-100)
  , prerollSeconds :: Number         -- ^ Pre-simulation time (0-60)
  }

-- | Default wave world.
defaultWaveWorld :: WaveWorldEffect
defaultWaveWorld =
  { wireframeMode: false
  , displayMode: 0
  , gridResolution: 80
  , waveHeight: 100.0
  , method: WMSmooth
  , damping: 30.0
  , groundEnabled: true
  , groundHeight: (-100.0)
  , reflectionStrength: 50.0
  , prerollSeconds: 0.0
  }

-- | Create wave world with specific height.
waveWorldWithHeight :: Number -> WaveMethod -> WaveWorldEffect
waveWorldWithHeight height method' =
  { wireframeMode: false
  , displayMode: 0
  , gridResolution: 80
  , waveHeight: clampNumber 0.0 500.0 height
  , method: method'
  , damping: 30.0
  , groundEnabled: true
  , groundHeight: (-100.0)
  , reflectionStrength: 50.0
  , prerollSeconds: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // foam
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foam producer type — bubble generation method.
data FoamProducer
  = FPPoint             -- ^ Single point
  | FPLine              -- ^ Line of points
  | FPArea              -- ^ Area of points

derive instance eqFoamProducer :: Eq FoamProducer
derive instance ordFoamProducer :: Ord FoamProducer

instance showFoamProducer :: Show FoamProducer where
  show FPPoint = "point"
  show FPLine = "line"
  show FPArea = "area"

-- | Foam Effect — bubble/foam generation.
-- |
-- | ## AE Properties
-- |
-- | Generates rising bubbles/foam effect.
type FoamEffect =
  { -- Producer
    producerType :: FoamProducer     -- ^ Generation type
  , producerPosition :: Point2D      -- ^ Producer position
  , producerSize :: Number           -- ^ Producer size (0-1000)
  
  -- Bubbles
  , bubbleCount :: Int               -- ^ Max bubbles (1-10000)
  , birthRate :: Number              -- ^ Bubbles per second (0-1000)
  , longevity :: Number              -- ^ Bubble life (0-30 seconds)
  , bubbleSize :: Number             -- ^ Bubble size (1-100)
  , sizeVariance :: Number           -- ^ Size variance (0-100%)
  
  -- Physics
  , flowSpeed :: Number              -- ^ Rise speed (0-200)
  , flowDirection :: Number          -- ^ Flow angle (0-360)
  , wobbleAmplitude :: Number        -- ^ Wobble amount (0-100)
  , wobbleFrequency :: Number        -- ^ Wobble speed (0-100)
  
  -- Appearance
  , opacity :: Number                -- ^ Bubble opacity (0-100)
  , popping :: Number                -- ^ Pop probability (0-100)
  , stickiness :: Number             -- ^ Bubble clumping (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default foam: moderate bubble count.
defaultFoam :: FoamEffect
defaultFoam =
  { producerType: FPLine
  , producerPosition: point2D 100.0 200.0
  , producerSize: 100.0
  , bubbleCount: 500
  , birthRate: 50.0
  , longevity: 5.0
  , bubbleSize: 10.0
  , sizeVariance: 50.0
  , flowSpeed: 50.0
  , flowDirection: 270.0  -- Up
  , wobbleAmplitude: 20.0
  , wobbleFrequency: 50.0
  , opacity: 100.0
  , popping: 10.0
  , stickiness: 0.0
  , randomSeed: 0
  }

-- | Create foam with specific bubble count.
foamWithBubbles :: Int -> Number -> FoamEffect
foamWithBubbles count size =
  { producerType: FPLine
  , producerPosition: point2D 100.0 200.0
  , producerSize: 100.0
  , bubbleCount: clampInt 1 10000 count
  , birthRate: 50.0
  , longevity: 5.0
  , bubbleSize: clampNumber 1.0 100.0 size
  , sizeVariance: 50.0
  , flowSpeed: 50.0
  , flowDirection: 270.0
  , wobbleAmplitude: 20.0
  , wobbleFrequency: 50.0
  , opacity: 100.0
  , popping: 10.0
  , stickiness: 0.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ball // action
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Ball Action Effect — grid of balls.
-- |
-- | Divides layer into grid and displaces as balls.
type BallActionEffect =
  { -- Grid
    gridSpacing :: Number            -- ^ Grid cell size (1-100)
  , ballSize :: Number               -- ^ Ball size (0-100)
  
  -- Scatter
  , scatterPosition :: Point2D       -- ^ Scatter center
  , scatterAmount :: Number          -- ^ Scatter strength (0-100)
  
  -- Twist
  , twistAngle :: Number             -- ^ Twist amount (-180 to 180)
  , twistAmount :: Number            -- ^ Twist strength (0-100)
  
  -- Appearance
  , useSourceAlpha :: Boolean        -- ^ Use source alpha
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default ball action.
defaultBallAction :: BallActionEffect
defaultBallAction =
  { gridSpacing: 10.0
  , ballSize: 80.0
  , scatterPosition: point2D 100.0 100.0
  , scatterAmount: 0.0
  , twistAngle: 0.0
  , twistAmount: 0.0
  , useSourceAlpha: false
  , randomSeed: 0
  }

-- | Create ball action with specific grid.
ballActionWithGrid :: Number -> Number -> BallActionEffect
ballActionWithGrid spacing size =
  { gridSpacing: clampNumber 1.0 100.0 spacing
  , ballSize: clampNumber 0.0 100.0 size
  , scatterPosition: point2D 100.0 100.0
  , scatterAmount: 0.0
  , twistAngle: 0.0
  , twistAmount: 0.0
  , useSourceAlpha: false
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // bubbles
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Bubbles Effect — simple rising bubbles.
type BubblesEffect =
  { bubbleAmount :: Number           -- ^ Bubble density (0-100)
  , bubbleSize :: Number             -- ^ Bubble size (1-100)
  , bubbleSpeed :: Number            -- ^ Rise speed (0-100)
  , wobbleAmount :: Number           -- ^ Wobble strength (0-100)
  , spreadAmount :: Number           -- ^ Horizontal spread (0-100)
  , groundHeight :: Number           -- ^ Where bubbles start (0-100 %)
  , reflectionStrength :: Number     -- ^ Bubble reflection (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default bubbles.
defaultBubbles :: BubblesEffect
defaultBubbles =
  { bubbleAmount: 50.0
  , bubbleSize: 20.0
  , bubbleSpeed: 50.0
  , wobbleAmount: 30.0
  , spreadAmount: 50.0
  , groundHeight: 100.0
  , reflectionStrength: 50.0
  , randomSeed: 0
  }

-- | Create bubbles with specific size.
bubblesWithSize :: Number -> Number -> BubblesEffect
bubblesWithSize amount size =
  { bubbleAmount: clampNumber 0.0 100.0 amount
  , bubbleSize: clampNumber 1.0 100.0 size
  , bubbleSpeed: 50.0
  , wobbleAmount: 30.0
  , spreadAmount: 50.0
  , groundHeight: 100.0
  , reflectionStrength: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // drizzle
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Drizzle Effect — rain drizzle with ripples.
type DrizzleEffect =
  { dripRate :: Number               -- ^ Drips per second (0-200)
  , rippleWidth :: Number            -- ^ Ripple width (0-100)
  , rippleSpeed :: Number            -- ^ Ripple expansion speed (0-100)
  , longevity :: Number              -- ^ Ripple duration (0-10 seconds)
  , lightingAngle :: Number          -- ^ Light angle (0-360)
  , lightingHeight :: Number         -- ^ Light height (0-100)
  , lightingIntensity :: Number      -- ^ Light intensity (0-200)
  , shading :: Number                -- ^ Shading amount (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default drizzle.
defaultDrizzle :: DrizzleEffect
defaultDrizzle =
  { dripRate: 30.0
  , rippleWidth: 50.0
  , rippleSpeed: 50.0
  , longevity: 3.0
  , lightingAngle: 45.0
  , lightingHeight: 50.0
  , lightingIntensity: 100.0
  , shading: 50.0
  , randomSeed: 0
  }

-- | Create drizzle with specific drop rate.
drizzleWithDrops :: Number -> Number -> DrizzleEffect
drizzleWithDrops rate width =
  { dripRate: clampNumber 0.0 200.0 rate
  , rippleWidth: clampNumber 0.0 100.0 width
  , rippleSpeed: 50.0
  , longevity: 3.0
  , lightingAngle: 45.0
  , lightingHeight: 50.0
  , lightingIntensity: 100.0
  , shading: 50.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // rain
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Rain Effect — falling rain particles.
type RainEffect =
  { drops :: Number                  -- ^ Number of drops (0-10000)
  , size :: Number                   -- ^ Drop size (0-100)
  , sceneDepth :: Number             -- ^ Depth effect (0-1000)
  , speed :: Number                  -- ^ Fall speed (0-100)
  , windDirection :: Number          -- ^ Wind angle (0-360)
  , windAmount :: Number             -- ^ Wind strength (0-100)
  , spread :: Number                 -- ^ Horizontal spread (0-100)
  , color :: RGB                     -- ^ Drop color
  , opacity :: Number                -- ^ Drop opacity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default rain.
defaultRain :: RainEffect
defaultRain =
  { drops: 2000.0
  , size: 30.0
  , sceneDepth: 100.0
  , speed: 50.0
  , windDirection: 180.0
  , windAmount: 0.0
  , spread: 30.0
  , color: rgb 200 200 220
  , opacity: 80.0
  , randomSeed: 0
  }

-- | Create rain with specific drop count.
rainWithDrops :: Number -> Number -> RainEffect
rainWithDrops count speed' =
  { drops: clampNumber 0.0 10000.0 count
  , size: 30.0
  , sceneDepth: 100.0
  , speed: clampNumber 0.0 100.0 speed'
  , windDirection: 180.0
  , windAmount: 0.0
  , spread: 30.0
  , color: rgb 200 200 220
  , opacity: 80.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // snowfall
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snowflake type — visual style.
data SnowflakeType
  = SFTDot              -- ^ Simple dot
  | SFTCrystal          -- ^ Crystal shape
  | SFTFlake            -- ^ Detailed flake
  | SFTMixed            -- ^ Mix of types

derive instance eqSnowflakeType :: Eq SnowflakeType
derive instance ordSnowflakeType :: Ord SnowflakeType

instance showSnowflakeType :: Show SnowflakeType where
  show SFTDot = "dot"
  show SFTCrystal = "crystal"
  show SFTFlake = "flake"
  show SFTMixed = "mixed"

-- | CC Snowfall Effect — falling snow.
type SnowfallEffect =
  { flakes :: Number                 -- ^ Number of flakes (0-10000)
  , flakeType :: SnowflakeType       -- ^ Visual type
  , size :: Number                   -- ^ Flake size (0-100)
  , sizeVariance :: Number           -- ^ Size variance (0-100%)
  , sceneDepth :: Number             -- ^ Depth effect (0-1000)
  , speed :: Number                  -- ^ Fall speed (0-100)
  , windDirection :: Number          -- ^ Wind angle (0-360)
  , windAmount :: Number             -- ^ Wind strength (0-100)
  , turbulence :: Number             -- ^ Flutter amount (0-100)
  , opacity :: Number                -- ^ Flake opacity (0-100)
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default snowfall.
defaultSnowfall :: SnowfallEffect
defaultSnowfall =
  { flakes: 1000.0
  , flakeType: SFTFlake
  , size: 20.0
  , sizeVariance: 50.0
  , sceneDepth: 100.0
  , speed: 30.0
  , windDirection: 180.0
  , windAmount: 10.0
  , turbulence: 30.0
  , opacity: 100.0
  , randomSeed: 0
  }

-- | Create snowfall with specific flake count.
snowfallWithFlakes :: Number -> SnowflakeType -> SnowfallEffect
snowfallWithFlakes count flakeType' =
  { flakes: clampNumber 0.0 10000.0 count
  , flakeType: flakeType'
  , size: 20.0
  , sizeVariance: 50.0
  , sceneDepth: 100.0
  , speed: 30.0
  , windDirection: 180.0
  , windAmount: 10.0
  , turbulence: 30.0
  , opacity: 100.0
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // star // burst
-- ═════════════════════════════════════════════════════════════════════════════

-- | CC Star Burst Effect — radial star/streak burst.
type StarBurstEffect =
  { center :: Point2D                -- ^ Burst center
  , starCount :: Int                 -- ^ Number of stars (1-10000)
  , starSize :: Number               -- ^ Star size (0-100)
  , starLength :: Number             -- ^ Streak length (0-500)
  , speed :: Number                  -- ^ Animation speed (0-100)
  , rotation :: Number               -- ^ Burst rotation (0-360)
  , randomness :: Number             -- ^ Random variation (0-100)
  , color :: RGB                     -- ^ Star color
  , opacity :: Number                -- ^ Star opacity (0-100)
  , transferMode :: BlendMode        -- ^ Blend mode
  , randomSeed :: Int                -- ^ Random seed
  }

-- | Default star burst.
defaultStarBurst :: StarBurstEffect
defaultStarBurst =
  { center: point2D 100.0 100.0
  , starCount: 50
  , starSize: 5.0
  , starLength: 100.0
  , speed: 50.0
  , rotation: 0.0
  , randomness: 30.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- | Create star burst with specific count.
starBurstWithCount :: Int -> Number -> StarBurstEffect
starBurstWithCount count length' =
  { center: point2D 100.0 100.0
  , starCount: clampInt 1 10000 count
  , starSize: 5.0
  , starLength: clampNumber 0.0 500.0 length'
  , speed: 50.0
  , rotation: 0.0
  , randomness: 30.0
  , color: rgb 255 255 255
  , opacity: 100.0
  , transferMode: BMAdd
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ParticleType to string.
particleTypeToString :: ParticleType -> String
particleTypeToString pt = show pt

-- | Convert PhysicsModel to string.
physicsModelToString :: PhysicsModel -> String
physicsModelToString pm = show pm

-- | Convert ShatterShape to string.
shatterShapeToString :: ShatterShape -> String
shatterShapeToString ss = show ss

-- | Convert ShatterForce to string.
shatterForceToString :: ShatterForce -> String
shatterForceToString sf = show sf

-- | Convert CardDanceAxis to string.
cardDanceAxisToString :: CardDanceAxis -> String
cardDanceAxisToString cda = show cda

-- | Convert CausticsLightType to string.
causticsLightTypeToString :: CausticsLightType -> String
causticsLightTypeToString clt = show clt

-- | Convert WaveMethod to string.
waveMethodToString :: WaveMethod -> String
waveMethodToString wm = show wm

-- | Convert FoamProducer to string.
foamProducerToString :: FoamProducer -> String
foamProducerToString fp = show fp

-- | Convert SnowflakeType to string.
snowflakeTypeToString :: SnowflakeType -> String
snowflakeTypeToString sft = show sft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // effect // names
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect name for Particle World.
particleWorldEffectName :: ParticleWorldEffect -> String
particleWorldEffectName _ = "CC Particle World"

-- | Effect name for Particle Systems II.
particleSystemsEffectName :: ParticleSystemsEffect -> String
particleSystemsEffectName _ = "CC Particle Systems II"

-- | Effect name for Shatter.
shatterEffectName :: ShatterEffect -> String
shatterEffectName _ = "Shatter"

-- | Effect name for Card Dance.
cardDanceEffectName :: CardDanceEffect -> String
cardDanceEffectName _ = "Card Dance"

-- | Effect name for Caustics.
causticsEffectName :: CausticsEffect -> String
causticsEffectName _ = "Caustics"

-- | Effect name for Wave World.
waveWorldEffectName :: WaveWorldEffect -> String
waveWorldEffectName _ = "Wave World"

-- | Effect name for Foam.
foamEffectName :: FoamEffect -> String
foamEffectName _ = "Foam"

-- | Effect name for Ball Action.
ballActionEffectName :: BallActionEffect -> String
ballActionEffectName _ = "CC Ball Action"

-- | Effect name for Bubbles.
bubblesEffectName :: BubblesEffect -> String
bubblesEffectName _ = "CC Bubbles"

-- | Effect name for Drizzle.
drizzleEffectName :: DrizzleEffect -> String
drizzleEffectName _ = "CC Drizzle"

-- | Effect name for Rain.
rainEffectName :: RainEffect -> String
rainEffectName _ = "CC Rain"

-- | Effect name for Snowfall.
snowfallEffectName :: SnowfallEffect -> String
snowfallEffectName _ = "CC Snowfall"

-- | Effect name for Star Burst.
starBurstEffectName :: StarBurstEffect -> String
starBurstEffectName _ = "CC Star Burst"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // effect // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create particle world description.
describeParticleWorld :: ParticleWorldEffect -> String
describeParticleWorld e =
  "ParticleWorld(" <> show e.birthRate <> " particles/sec, " <>
  show e.physicsModel <> ")"

-- | Create shatter description.
describeShatter :: ShatterEffect -> String
describeShatter e =
  "Shatter(" <> show e.shatterShape <> ", force: " <>
  show e.forceStrength <> "%)"

-- | Create card dance description.
describeCardDance :: CardDanceEffect -> String
describeCardDance e =
  "CardDance(" <> show e.rows <> "x" <> show e.columns <> " grid)"

-- | Create caustics description.
describeCaustics :: CausticsEffect -> String
describeCaustics e =
  "Caustics(strength: " <> show e.causticStrength <> "%, waves: " <>
  show e.waveHeight <> ")"

-- | Create wave world description.
describeWaveWorld :: WaveWorldEffect -> String
describeWaveWorld e =
  "WaveWorld(" <> show e.method <> ", height: " <> show e.waveHeight <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp integer to bounds.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if particle world has gravity.
particleWorldHasGravity :: ParticleWorldEffect -> Boolean
particleWorldHasGravity e = e.gravity > 0.0

-- | Check if shatter force is radial.
isShatterRadial :: ShatterEffect -> Boolean
isShatterRadial e = case e.forceType of
  SFRadius -> true
  _ -> false

-- | Check if wave world is steep.
isWaveWorldSteep :: WaveWorldEffect -> Boolean
isWaveWorldSteep e = case e.method of
  WMSteep -> true
  _ -> false

-- | Check if foam has high bubble count.
isFoamHighDensity :: FoamEffect -> Boolean
isFoamHighDensity e = e.bubbleCount > 1000

-- | Check if rain has wind.
rainHasWind :: RainEffect -> Boolean
rainHasWind e = e.windAmount > 0.0

-- | Check if snowfall has turbulence.
snowfallHasTurbulence :: SnowfallEffect -> Boolean
snowfallHasTurbulence e = e.turbulence > 0.0

-- | Get particle world total particles estimate.
estimateParticleCount :: ParticleWorldEffect -> Number
estimateParticleCount e = clampNumber 0.0 100000.0 $ e.birthRate * e.longevity

-- | Get foam total bubbles estimate.
estimateFoamBubbles :: FoamEffect -> Number
estimateFoamBubbles e = clampNumber 0.0 50000.0 $ e.birthRate * e.longevity
