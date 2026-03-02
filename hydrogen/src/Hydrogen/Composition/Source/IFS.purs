-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // composition // source // ifs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Iterated Function Systems — Fractal generation via affine transforms.
-- |
-- | The "Chaos Game" algorithm: repeatedly apply random affine transforms
-- | to generate self-similar fractal structures.
-- |
-- | Reference: Barnsley, M. "Fractals Everywhere" (1988)
-- |            paulbourke.net/fractals/ifs/

module Hydrogen.Composition.Source.IFS
  ( -- * Core Types
    Point2D
  , point
  , origin
  , AffineCoeffs
  , IFSTransform
  , IFSSystem(..)
  
  -- * Transform Operations
  , applyTransform
  , mkTransform
  , mkIFS
  , getTransforms
  , transformCount
  
  -- * Chaos Game
  , ChaosState
  , initChaos
  , selectTransform
  , stepChaos
  , runChaos
  
  -- * Contractivity
  , isContractive
  , isIFSContractive
  , ContractivityResult(..)
  , checkContractivity
  
  -- * Classic Presets
  , IFSPreset(..)
  , presetToIFS
  , barnsleyFern
  , dragon
  , mapleLeaf
  , spiral
  , tree
  , sierpinskiTriangle
  , christmasTree
  
  -- * IFS Spec
  , IFSColorMode(..)
  , IFSSpec
  , ifsFromPreset
  , ifsFromSystem
  
  -- * Bounds
  , Bounds2D
  , calculateBounds
  , normalizePoints
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (&&)
  , (<=)
  , negate
  )

import Data.Array (length, index, foldl)
import Data.Functor (map)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // affine types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A point in 2D space for IFS iteration.
type Point2D = { x :: Number, y :: Number }

-- | Create a point.
point :: Number -> Number -> Point2D
point x y = { x, y }

-- | Origin point (0, 0).
origin :: Point2D
origin = { x: 0.0, y: 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // transform type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Affine transformation coefficients.
-- |
-- | Transforms a point (x, y) to:
-- |   x' = a*x + b*y + e
-- |   y' = c*x + d*y + f
-- |
-- | The matrix form is:
-- |   [ a  b  e ]   [ x ]
-- |   [ c  d  f ] × [ y ]
-- |   [ 0  0  1 ]   [ 1 ]
type AffineCoeffs =
  { a :: Number  -- x scale / rotation component
  , b :: Number  -- x shear component
  , c :: Number  -- y shear component  
  , d :: Number  -- y scale / rotation component
  , e :: Number  -- x translation
  , f :: Number  -- y translation
  }

-- | An IFS transform with probability weight.
type IFSTransform =
  { coeffs :: AffineCoeffs
  , probability :: Number  -- Selection probability (0-1)
  }

-- | Apply an affine transform to a point.
applyTransform :: AffineCoeffs -> Point2D -> Point2D
applyTransform { a, b, c, d, e, f } { x, y } =
  { x: a * x + b * y + e
  , y: c * x + d * y + f
  }

-- | Create a transform with given coefficients and probability.
mkTransform :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> IFSTransform
mkTransform a b c d e f prob =
  { coeffs: { a, b, c, d, e, f }
  , probability: clampProb prob
  }
  where
    clampProb p
      | p < 0.0 = 0.0
      | p <= 1.0 = p
      | true = 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // ifs system
-- ═══════════════════════════════════════════════════════════════════════════════

-- | An Iterated Function System — a collection of affine transforms.
newtype IFSSystem = IFSSystem (Array IFSTransform)

derive instance eqIFSSystem :: Eq IFSSystem

instance showIFSSystem :: Show IFSSystem where
  show (IFSSystem ts) = "(IFSSystem " <> show (length ts) <> " transforms)"

-- | Create an IFS from an array of transforms.
-- | Normalizes probabilities to sum to 1.0.
mkIFS :: Array IFSTransform -> IFSSystem
mkIFS transforms = IFSSystem (normalizeProbabilities transforms)

-- | Normalize probabilities so they sum to 1.0.
normalizeProbabilities :: Array IFSTransform -> Array IFSTransform
normalizeProbabilities ts =
  let 
    total = foldl (\acc t -> acc + t.probability) 0.0 ts
  in
    if total <= 0.0
      then ts  -- Keep as-is if no valid probabilities
      else map (\t -> t { probability = t.probability / total }) ts

-- | Get transforms from an IFS.
getTransforms :: IFSSystem -> Array IFSTransform
getTransforms (IFSSystem ts) = ts

-- | Number of transforms in the system.
transformCount :: IFSSystem -> Int
transformCount (IFSSystem ts) = length ts

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // chaos game state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | State for the chaos game iteration.
type ChaosState =
  { current :: Point2D           -- Current point
  , points :: Array Point2D      -- Accumulated points
  , iteration :: Int             -- Current iteration count
  }

-- | Initial chaos game state.
initChaos :: Point2D -> ChaosState
initChaos start =
  { current: start
  , points: []
  , iteration: 0
  }

-- | Select a transform based on a random value in [0, 1).
-- | Uses cumulative probability distribution.
selectTransform :: Number -> Array IFSTransform -> Maybe IFSTransform
selectTransform rand transforms = go 0.0 transforms
  where
    go _ [] = Nothing
    go cumulative ts = case index ts 0 of
      Nothing -> Nothing
      Just t -> 
        let newCumulative = cumulative + t.probability
        in if rand < newCumulative
           then Just t
           else go newCumulative (dropFirst ts)
    
    dropFirst arr = case index arr 0 of
      Nothing -> []
      Just _ -> fromMaybe [] (dropFirstSafe arr)
    
    dropFirstSafe arr = 
      let len = length arr
      in if len <= 1 
         then Just []
         else Just (sliceFrom 1 arr)

-- | Slice array from index to end.
sliceFrom :: forall a. Int -> Array a -> Array a
sliceFrom start arr = 
  foldl (\acc i -> case index arr i of
    Nothing -> acc
    Just x -> acc <> [x]
  ) [] (rangeInts start (length arr - 1))

-- | Generate integer range (inclusive).
rangeInts :: Int -> Int -> Array Int
rangeInts start end
  | start <= end = [start] <> rangeInts (start + 1) end
  | true = []

-- | Perform one chaos game iteration.
-- | Takes a random value [0, 1) to select the transform.
stepChaos :: Number -> IFSSystem -> ChaosState -> ChaosState
stepChaos rand (IFSSystem transforms) state =
  case selectTransform rand transforms of
    Nothing -> state  -- No valid transform
    Just t ->
      let newPoint = applyTransform t.coeffs state.current
      in state
        { current = newPoint
        , points = state.points <> [newPoint]
        , iteration = state.iteration + 1
        }

-- | Run multiple chaos iterations with an array of random values.
runChaos :: Array Number -> IFSSystem -> ChaosState -> ChaosState
runChaos randoms ifs state = foldl (\s r -> stepChaos r ifs s) state randoms

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // contractivity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a transform is contractive (converges rather than diverges).
-- |
-- | For the mapping to be contractive, all must be true:
-- |   a² + d² < 1
-- |   b² + e² < 1  
-- |   a² + b² + d² + e² < 1 + (a*e - d*b)²
-- |
-- | Note: The reference uses (a,b,c,d,e,f) differently than we do.
-- | Adapting: our (a,b,c,d) maps to their (a,b,d,e).
isContractive :: AffineCoeffs -> Boolean
isContractive { a, b, c, d, e: _, f: _ } =
  let
    -- Condition 1: a² + c² < 1
    cond1 = a * a + c * c < 1.0
    -- Condition 2: b² + d² < 1
    cond2 = b * b + d * d < 1.0
    -- Condition 3: a² + b² + c² + d² < 1 + (a*d - c*b)²
    det = a * d - c * b
    cond3 = a * a + b * b + c * c + d * d < 1.0 + det * det
  in
    cond1 && cond2 && cond3

-- | Check if all transforms in an IFS are contractive.
isIFSContractive :: IFSSystem -> Boolean
isIFSContractive (IFSSystem transforms) =
  foldl (\acc t -> acc && isContractive t.coeffs) true transforms

-- | Contractivity result with details.
data ContractivityResult
  = Contractive
  | NonContractive Int  -- Index of first non-contractive transform

derive instance eqContractivityResult :: Eq ContractivityResult

instance showContractivityResult :: Show ContractivityResult where
  show Contractive = "Contractive"
  show (NonContractive i) = "(NonContractive at index " <> show i <> ")"

-- | Check contractivity with detailed result.
checkContractivity :: IFSSystem -> ContractivityResult
checkContractivity (IFSSystem transforms) = go 0 transforms
  where
    go _ [] = Contractive
    go i ts = case index ts 0 of
      Nothing -> Contractive
      Just t ->
        if isContractive t.coeffs
        then go (i + 1) (sliceFrom 1 ts)
        else NonContractive i

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // classic presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Preset IFS type.
data IFSPreset
  = PresetBarnsleyFern
  | PresetDragon
  | PresetMapleLeaf
  | PresetSpiral
  | PresetTree
  | PresetSierpinskiTriangle
  | PresetChristmasTree

derive instance eqIFSPreset :: Eq IFSPreset
derive instance ordIFSPreset :: Ord IFSPreset

instance showIFSPreset :: Show IFSPreset where
  show PresetBarnsleyFern = "barnsley-fern"
  show PresetDragon = "dragon"
  show PresetMapleLeaf = "maple-leaf"
  show PresetSpiral = "spiral"
  show PresetTree = "tree"
  show PresetSierpinskiTriangle = "sierpinski-triangle"
  show PresetChristmasTree = "christmas-tree"

-- | Get the IFS system for a preset.
presetToIFS :: IFSPreset -> IFSSystem
presetToIFS PresetBarnsleyFern = barnsleyFern
presetToIFS PresetDragon = dragon
presetToIFS PresetMapleLeaf = mapleLeaf
presetToIFS PresetSpiral = spiral
presetToIFS PresetTree = tree
presetToIFS PresetSierpinskiTriangle = sierpinskiTriangle
presetToIFS PresetChristmasTree = christmasTree

-- | Barnsley Fern — the classic fractal fern.
-- | Reference: paulbourke.net/fractals/ifs/
barnsleyFern :: IFSSystem
barnsleyFern = mkIFS
  [ mkTransform 0.0    0.0    0.0    0.16   0.0   0.0    0.01   -- Stem
  , mkTransform 0.2   (-0.26) 0.23   0.22   0.0   1.6    0.07   -- Left leaflet
  , mkTransform (-0.15) 0.28  0.26   0.24   0.0   0.44   0.07   -- Right leaflet
  , mkTransform 0.85   0.04  (-0.04) 0.85   0.0   1.6    0.85   -- Main frond
  ]

-- | Dragon curve IFS.
dragon :: IFSSystem
dragon = mkIFS
  [ mkTransform 0.824074   0.281428  (-0.212346) 0.864198  (-1.882290) (-0.110607) 0.8
  , mkTransform 0.088272   0.520988  (-0.463889) (-0.377778) 0.785360   8.095795   0.2
  ]

-- | Maple Leaf IFS.
mapleLeaf :: IFSSystem
mapleLeaf = mkIFS
  [ mkTransform 0.14   0.01   0.0    0.51  (-0.08) (-1.31) 0.25
  , mkTransform 0.43   0.52  (-0.45) 0.50   1.49   (-0.75) 0.25
  , mkTransform 0.45  (-0.49) 0.47   0.47  (-1.62) (-0.74) 0.25
  , mkTransform 0.49   0.0    0.0    0.51   0.02    1.62   0.25
  ]

-- | Spiral IFS.
spiral :: IFSSystem
spiral = mkIFS
  [ mkTransform 0.787879  (-0.424242) 0.242424  0.859848  1.758647  1.408065  0.90
  , mkTransform (-0.121212) 0.257576  0.151515  0.053030 (-6.721654) 1.377236  0.05
  , mkTransform 0.181818  (-0.136364) 0.090909  0.181818  6.086107  1.568035  0.05
  ]

-- | Tree IFS.
tree :: IFSSystem
tree = mkIFS
  [ mkTransform 0.05   0.0   0.0    0.4   (-0.06) (-0.47) 0.143
  , mkTransform (-0.05) 0.0  0.0   (-0.4) (-0.06) (-0.47) 0.143
  , mkTransform 0.03  (-0.14) 0.0   0.26  (-0.16) (-0.01) 0.143
  , mkTransform (-0.03) 0.14 0.0  (-0.26) (-0.16) (-0.01) 0.143
  , mkTransform 0.56   0.44 (-0.37) 0.51   0.30    0.15   0.143
  , mkTransform 0.19   0.07 (-0.10) 0.15  (-0.20)  0.28   0.143
  , mkTransform (-0.33)(-0.34)(-0.33) 0.34 (-0.54)  0.39   0.143
  ]

-- | Sierpinski Triangle IFS.
sierpinskiTriangle :: IFSSystem
sierpinskiTriangle = mkIFS
  [ mkTransform 0.5  0.0  0.0  0.5  0.0   0.0   0.333
  , mkTransform 0.5  0.0  0.0  0.5  0.5   0.0   0.333
  , mkTransform 0.5  0.0  0.0  0.5  0.25  0.433 0.333  -- sqrt(3)/4 ≈ 0.433
  ]

-- | Christmas Tree IFS.
christmasTree :: IFSSystem
christmasTree = mkIFS
  [ mkTransform 0.0  (-0.5) 0.5  0.0  0.5  0.0  0.333
  , mkTransform 0.0   0.5 (-0.5) 0.0  0.5  0.5  0.333
  , mkTransform 0.5   0.0  0.0   0.5  0.25 0.5  0.333
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // ifs spec type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Color mode for IFS rendering.
data IFSColorMode
  = IFSMonochrome            -- Single color
  | IFSByTransform           -- Color based on which transform was used
  | IFSByIteration           -- Color based on iteration count
  | IFSByDensity             -- Color based on point density

derive instance eqIFSColorMode :: Eq IFSColorMode

instance showIFSColorMode :: Show IFSColorMode where
  show IFSMonochrome = "monochrome"
  show IFSByTransform = "by-transform"
  show IFSByIteration = "by-iteration"
  show IFSByDensity = "by-density"

-- | IFS rendering specification for composition.
type IFSSpec =
  { system :: IFSSystem          -- The IFS to render
  , iterations :: Int            -- Number of points to generate
  , warmup :: Int                -- Iterations to skip before recording
  , colorMode :: IFSColorMode    -- How to color points
  , pointSize :: Number          -- Point size in pixels
  , seed :: Int                  -- Random seed for determinism
  }

-- | Create an IFS spec from a preset.
ifsFromPreset :: IFSPreset -> Int -> IFSSpec
ifsFromPreset preset iterations =
  { system: presetToIFS preset
  , iterations: clampIterations iterations
  , warmup: 100
  , colorMode: IFSByTransform
  , pointSize: 1.0
  , seed: 0
  }

-- | Create an IFS spec from a custom system.
ifsFromSystem :: IFSSystem -> Int -> IFSSpec
ifsFromSystem system iterations =
  { system
  , iterations: clampIterations iterations
  , warmup: 100
  , colorMode: IFSMonochrome
  , pointSize: 1.0
  , seed: 0
  }

-- | Clamp iterations to reasonable bounds.
clampIterations :: Int -> Int
clampIterations n
  | n < 100 = 100
  | n <= 10000000 = n
  | true = 10000000

-- | Calculate bounds of generated points.
type Bounds2D = 
  { minX :: Number
  , maxX :: Number
  , minY :: Number
  , maxY :: Number
  }

-- | Get bounds from an array of points.
calculateBounds :: Array Point2D -> Bounds2D
calculateBounds points =
  foldl updateBounds initBounds points
  where
    initBounds = { minX: 0.0, maxX: 0.0, minY: 0.0, maxY: 0.0 }
    updateBounds b p =
      { minX: minNum b.minX p.x
      , maxX: maxNum b.maxX p.x
      , minY: minNum b.minY p.y
      , maxY: maxNum b.maxY p.y
      }

-- | Minimum of two numbers.
minNum :: Number -> Number -> Number
minNum a b = if a < b then a else b

-- | Maximum of two numbers.
maxNum :: Number -> Number -> Number
maxNum a b = if a < b then b else a

-- | Normalize points to [0, 1] range.
normalizePoints :: Bounds2D -> Array Point2D -> Array Point2D
normalizePoints bounds pts =
  let
    width = bounds.maxX - bounds.minX
    height = bounds.maxY - bounds.minY
    scale = maxNum width height
  in
    if scale <= 0.0
    then pts
    else map (\p -> 
      { x: (p.x - bounds.minX) / scale
      , y: (p.y - bounds.minY) / scale
      }) pts
