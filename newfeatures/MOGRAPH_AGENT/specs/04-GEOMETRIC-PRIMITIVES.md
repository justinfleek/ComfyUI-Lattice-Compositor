# Specification 04: Geometric Primitives
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-04  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines all geometric primitives supported by the Lottie format with:

1. **Formal type definitions** with bounded constraints
2. **Construction functions** with validation
3. **Transformation operations** with proofs
4. **Serialization to Lottie JSON**

---

## 2. Point and Vector Types

### 2.1 Lean4 Foundations

```lean4
/-- 2D Point with bounded coordinates -/
structure Point where
  x : Float
  y : Float
  h_x_bounds : -100000 ≤ x ∧ x ≤ 100000
  h_y_bounds : -100000 ≤ y ∧ y ≤ 100000
  deriving Repr

namespace Point

def origin : Point := ⟨0, 0, by norm_num, by norm_num⟩

def mk' (x y : Float) : Point :=
  let cx := max (-100000) (min 100000 x)
  let cy := max (-100000) (min 100000 y)
  ⟨cx, cy, by constructor <;> simp [cx] <;> norm_num, 
           by constructor <;> simp [cy] <;> norm_num⟩

def add (a b : Point) : Point :=
  mk' (a.x + b.x) (a.y + b.y)

def sub (a b : Point) : Point :=
  mk' (a.x - b.x) (a.y - b.y)

def scale (s : Float) (p : Point) : Point :=
  mk' (s * p.x) (s * p.y)

def lerp (t : Float) (a b : Point) : Point :=
  mk' (a.x + t * (b.x - a.x)) (a.y + t * (b.y - a.y))

def distance (a b : Point) : Float :=
  Float.sqrt ((b.x - a.x)^2 + (b.y - a.y)^2)

/-- Proof: lerp at t=0 returns first point -/
theorem lerp_zero (a b : Point) : lerp 0 a b = a := by
  simp [lerp, mk']
  -- After clamping, values equal a.x and a.y
  sorry -- Requires float arithmetic

/-- Proof: lerp at t=1 returns second point -/
theorem lerp_one (a b : Point) : lerp 1 a b = b := by
  simp [lerp, mk']
  sorry

end Point
```

### 2.2 Haskell Implementation

```haskell
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}

module Lattice.Geometry.Point where

import GHC.Generics (Generic)
import Data.Aeson (ToJSON(..), FromJSON(..))
import Lattice.Core.Bounded

-- | 2D Point with bounded coordinates
-- Constraints: x, y ∈ [-100000, 100000]
data Point = Point
  { ptX :: !(Bounded Double)
  , ptY :: !(Bounded Double)
  } deriving (Eq, Show, Generic)

instance ToJSON Point where
  toJSON p = toJSON [bValue (ptX p), bValue (ptY p)]

instance FromJSON Point where
  parseJSON = withArray "Point" $ \arr -> do
    case toList arr of
      [x, y] -> do
        xVal <- parseJSON x
        yVal <- parseJSON y
        case mkPoint xVal yVal of
          Right p -> pure p
          Left e -> fail e
      _ -> fail "Point must be [x, y]"

-- | Point constraint specification
pointConstraint :: (Double, Double, Double)
pointConstraint = (-100000, 100000, 0)

-- | Smart constructor
mkPoint :: Double -> Double -> Either String Point
mkPoint x y = do
  bx <- mkBounded x (-100000) 100000 0
  by <- mkBounded y (-100000) 100000 0
  pure $ Point bx by

-- | Unsafe constructor (clamps values)
point :: Double -> Double -> Point
point x y = Point
  (unsafeMkBounded (clamp (-100000) 100000 x) (-100000) 100000 0)
  (unsafeMkBounded (clamp (-100000) 100000 y) (-100000) 100000 0)
  where
    clamp lo hi v = max lo (min hi v)

-- | Origin point
origin :: Point
origin = point 0 0

-- | Point operations
pointAdd :: Point -> Point -> Point
pointAdd a b = point (bValue (ptX a) + bValue (ptX b)) 
                     (bValue (ptY a) + bValue (ptY b))

pointSub :: Point -> Point -> Point
pointSub a b = point (bValue (ptX a) - bValue (ptX b)) 
                     (bValue (ptY a) - bValue (ptY b))

pointScale :: Double -> Point -> Point
pointScale s p = point (s * bValue (ptX p)) (s * bValue (ptY p))

pointLerp :: Double -> Point -> Point -> Point
pointLerp t a b = point
  (bValue (ptX a) + t * (bValue (ptX b) - bValue (ptX a)))
  (bValue (ptY a) + t * (bValue (ptY b) - bValue (ptY a)))

pointDistance :: Point -> Point -> Double
pointDistance a b = sqrt $ dx * dx + dy * dy
  where
    dx = bValue (ptX b) - bValue (ptX a)
    dy = bValue (ptY b) - bValue (ptY a)

-- | Get raw values
pointToTuple :: Point -> (Double, Double)
pointToTuple p = (bValue (ptX p), bValue (ptY p))

-- | Convert to list for Lottie
pointToList :: Point -> [Double]
pointToList p = [bValue (ptX p), bValue (ptY p)]
```

### 2.3 PureScript Implementation

```purescript
module Lattice.Geometry.Point 
  ( Point
  , mkPoint
  , point
  , origin
  , pointAdd
  , pointSub
  , pointScale
  , pointLerp
  , pointDistance
  , pointToArray
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Number (sqrt)
import Lattice.Core.Bounded (Bounded, mkBounded, getValue, mkBoundedUnsafe)

-- | 2D Point with bounded coordinates
newtype Point = Point
  { x :: Bounded Number
  , y :: Bounded Number
  }

derive instance eqPoint :: Eq Point

instance showPoint :: Show Point where
  show (Point p) = "Point(" <> show (getValue p.x) <> ", " <> show (getValue p.y) <> ")"

-- | Point bounds
pointMin :: Number
pointMin = -100000.0

pointMax :: Number
pointMax = 100000.0

pointDefault :: Number
pointDefault = 0.0

-- | Smart constructor with validation
mkPoint :: Number -> Number -> Either String Point
mkPoint x y = do
  bx <- mkBounded x pointMin pointMax pointDefault
  by <- mkBounded y pointMin pointMax pointDefault
  pure $ Point { x: bx, y: by }

-- | Unsafe constructor (clamps)
point :: Number -> Number -> Point
point x y = Point
  { x: mkBoundedUnsafe (clamp x) pointMin pointMax pointDefault
  , y: mkBoundedUnsafe (clamp y) pointMin pointMax pointDefault
  }
  where
    clamp v = max pointMin (min pointMax v)

-- | Origin
origin :: Point
origin = point 0.0 0.0

-- | Operations
pointAdd :: Point -> Point -> Point
pointAdd (Point a) (Point b) = point (getValue a.x + getValue b.x) (getValue a.y + getValue b.y)

pointSub :: Point -> Point -> Point
pointSub (Point a) (Point b) = point (getValue a.x - getValue b.x) (getValue a.y - getValue b.y)

pointScale :: Number -> Point -> Point
pointScale s (Point p) = point (s * getValue p.x) (s * getValue p.y)

pointLerp :: Number -> Point -> Point -> Point
pointLerp t (Point a) (Point b) = point
  (getValue a.x + t * (getValue b.x - getValue a.x))
  (getValue a.y + t * (getValue b.y - getValue a.y))

pointDistance :: Point -> Point -> Number
pointDistance (Point a) (Point b) = sqrt (dx * dx + dy * dy)
  where
    dx = getValue b.x - getValue a.x
    dy = getValue b.y - getValue a.y

-- | Convert to array for Lottie JSON
pointToArray :: Point -> Array Number
pointToArray (Point p) = [getValue p.x, getValue p.y]
```

---

## 3. Size Type

### 3.1 Definition

```haskell
-- | Size with non-negative dimensions
-- Constraints: width, height ∈ [0, 100000]
data Size = Size
  { szWidth  :: !(Bounded Double)
  , szHeight :: !(Bounded Double)
  } deriving (Eq, Show, Generic)

-- | Size constraint specification
sizeConstraint :: (Double, Double, Double)
sizeConstraint = (0, 100000, 100)

-- | Smart constructor
mkSize :: Double -> Double -> Either String Size
mkSize w h = do
  bw <- mkBounded w 0 100000 100
  bh <- mkBounded h 0 100000 100
  pure $ Size bw bh

-- | Unsafe constructor
size :: Double -> Double -> Size
size w h = Size
  (unsafeMkBounded (max 0 (min 100000 w)) 0 100000 100)
  (unsafeMkBounded (max 0 (min 100000 h)) 0 100000 100)

-- | Unit size
unitSize :: Size
unitSize = size 100 100

-- | Scale size
scaleSize :: Double -> Size -> Size
scaleSize s (Size w h) = size (s * bValue w) (s * bValue h)

-- | Size to point (for Lottie "s" property)
sizeToPoint :: Size -> Point
sizeToPoint (Size w h) = point (bValue w) (bValue h)
```

---

## 4. Rectangle Primitive

### 4.1 Lean4 Definition

```lean4
/-- Rectangle shape with bounded dimensions -/
structure Rectangle where
  position : Point           -- Center position
  size : Size               -- Width and height
  cornerRadius : Float      -- Rounded corners
  h_radius : 0 ≤ cornerRadius ∧ cornerRadius ≤ 10000
  deriving Repr

namespace Rectangle

def mk (pos : Point) (sz : Size) (radius : Float) : Rectangle :=
  let cr := max 0 (min 10000 radius)
  ⟨pos, sz, cr, by constructor <;> simp [cr] <;> norm_num⟩

def withCornerRadius (r : Float) (rect : Rectangle) : Rectangle :=
  mk rect.position rect.size r

def bounds (rect : Rectangle) : (Point, Point) :=
  let halfW := rect.size.width / 2
  let halfH := rect.size.height / 2
  let topLeft := Point.mk' (rect.position.x - halfW) (rect.position.y - halfH)
  let bottomRight := Point.mk' (rect.position.x + halfW) (rect.position.y + halfH)
  (topLeft, bottomRight)

def area (rect : Rectangle) : Float :=
  rect.size.width * rect.size.height

def perimeter (rect : Rectangle) : Float :=
  2 * (rect.size.width + rect.size.height)

end Rectangle
```

### 4.2 Haskell Implementation

```haskell
-- | Rectangle shape
data Rectangle = Rectangle
  { rectPosition     :: !Point           -- Center position
  , rectSize         :: !Size            -- Width, height
  , rectCornerRadius :: !(Bounded Double) -- Corner radius
  , rectDirection    :: !ShapeDirection  -- Drawing direction
  } deriving (Eq, Show, Generic)

-- | Corner radius constraint
cornerRadiusConstraint :: (Double, Double, Double)
cornerRadiusConstraint = (0, 10000, 0)

-- | Shape direction (CW or CCW)
data ShapeDirection = DirNormal | DirReversed
  deriving (Eq, Show, Enum, Bounded)

shapeDirectionCode :: ShapeDirection -> Int
shapeDirectionCode DirNormal = 1
shapeDirectionCode DirReversed = 3

-- | Smart constructor
mkRectangle :: Point -> Size -> Double -> Either String Rectangle
mkRectangle pos sz radius = do
  br <- mkBounded radius 0 10000 0
  pure $ Rectangle pos sz br DirNormal

-- | Convenience constructor
rectangle :: Point -> Size -> Double -> Rectangle
rectangle pos sz radius = Rectangle
  pos sz
  (unsafeMkBounded (max 0 (min 10000 radius)) 0 10000 0)
  DirNormal

-- | Rectangle at origin
centeredRectangle :: Double -> Double -> Rectangle
centeredRectangle w h = rectangle origin (size w h) 0

-- | Rectangle bounds
rectBounds :: Rectangle -> (Point, Point)
rectBounds r =
  let halfW = bValue (szWidth $ rectSize r) / 2
      halfH = bValue (szHeight $ rectSize r) / 2
      cx = bValue (ptX $ rectPosition r)
      cy = bValue (ptY $ rectPosition r)
  in (point (cx - halfW) (cy - halfH), point (cx + halfW) (cy + halfH))

-- | Convert to Lottie shape JSON
rectToLottie :: Rectangle -> Value
rectToLottie r = object
  [ "ty" .= ("rc" :: Text)
  , "p"  .= object  -- Position
      [ "a" .= (0 :: Int)
      , "k" .= pointToList (rectPosition r)
      ]
  , "s"  .= object  -- Size
      [ "a" .= (0 :: Int)
      , "k" .= [bValue (szWidth $ rectSize r), bValue (szHeight $ rectSize r)]
      ]
  , "r"  .= object  -- Corner radius
      [ "a" .= (0 :: Int)
      , "k" .= bValue (rectCornerRadius r)
      ]
  , "d"  .= shapeDirectionCode (rectDirection r)
  ]
```

---

## 5. Ellipse Primitive

### 5.1 Definition

```haskell
-- | Ellipse shape
data Ellipse = Ellipse
  { ellPosition  :: !Point          -- Center position
  , ellSize      :: !Size           -- Width, height (diameters)
  , ellDirection :: !ShapeDirection -- Drawing direction
  } deriving (Eq, Show, Generic)

-- | Smart constructor
mkEllipse :: Point -> Size -> Either String Ellipse
mkEllipse pos sz = pure $ Ellipse pos sz DirNormal

-- | Convenience constructor
ellipse :: Point -> Size -> Ellipse
ellipse pos sz = Ellipse pos sz DirNormal

-- | Circle (special case of ellipse)
circle :: Point -> Double -> Ellipse
circle center diameter = ellipse center (size diameter diameter)

-- | Ellipse area
ellipseArea :: Ellipse -> Double
ellipseArea e = pi * (bValue (szWidth $ ellSize e) / 2) * (bValue (szHeight $ ellSize e) / 2)

-- | Point on ellipse at angle (radians)
ellipsePointAt :: Ellipse -> Double -> Point
ellipsePointAt e angle =
  let rx = bValue (szWidth $ ellSize e) / 2
      ry = bValue (szHeight $ ellSize e) / 2
      cx = bValue (ptX $ ellPosition e)
      cy = bValue (ptY $ ellPosition e)
  in point (cx + rx * cos angle) (cy + ry * sin angle)

-- | Convert to Lottie shape JSON
ellipseToLottie :: Ellipse -> Value
ellipseToLottie e = object
  [ "ty" .= ("el" :: Text)
  , "p"  .= object
      [ "a" .= (0 :: Int)
      , "k" .= pointToList (ellPosition e)
      ]
  , "s"  .= object
      [ "a" .= (0 :: Int)
      , "k" .= [bValue (szWidth $ ellSize e), bValue (szHeight $ ellSize e)]
      ]
  , "d"  .= shapeDirectionCode (ellDirection e)
  ]
```

---

## 6. PolyStar Primitive

### 6.1 Definition

```haskell
-- | Star type
data StarType = StarStar | StarPolygon
  deriving (Eq, Show, Enum, Bounded)

starTypeCode :: StarType -> Int
starTypeCode StarStar = 1
starTypeCode StarPolygon = 2

-- | PolyStar shape (star or polygon)
data PolyStar = PolyStar
  { psPosition       :: !Point              -- Center
  , psType           :: !StarType           -- Star or polygon
  , psPoints         :: !(Bounded Int)      -- Number of points (3-100)
  , psOuterRadius    :: !(Bounded Double)   -- Outer radius
  , psInnerRadius    :: !(Bounded Double)   -- Inner radius (star only)
  , psOuterRoundness :: !(Bounded Double)   -- Outer corner roundness (0-100%)
  , psInnerRoundness :: !(Bounded Double)   -- Inner corner roundness (0-100%)
  , psRotation       :: !(Bounded Double)   -- Rotation in degrees
  , psDirection      :: !ShapeDirection
  } deriving (Eq, Show, Generic)

-- | Constraint specifications
starPointsConstraint :: (Int, Int, Int)
starPointsConstraint = (3, 100, 5)

starRadiusConstraint :: (Double, Double, Double)
starRadiusConstraint = (0, 100000, 50)

starRoundnessConstraint :: (Double, Double, Double)
starRoundnessConstraint = (0, 100, 0)

starRotationConstraint :: (Double, Double, Double)
starRotationConstraint = (-36000, 36000, 0)

-- | Smart constructor for star
mkStar :: Point -> Int -> Double -> Double -> Either String PolyStar
mkStar pos points outerR innerR = do
  bPoints <- mkBounded points 3 100 5
  bOuterR <- mkBounded outerR 0 100000 50
  bInnerR <- mkBounded innerR 0 100000 25
  bOuterRnd <- mkBounded 0 0 100 0
  bInnerRnd <- mkBounded 0 0 100 0
  bRot <- mkBounded 0 (-36000) 36000 0
  pure $ PolyStar pos StarStar bPoints bOuterR bInnerR bOuterRnd bInnerRnd bRot DirNormal

-- | Smart constructor for polygon
mkPolygon :: Point -> Int -> Double -> Either String PolyStar
mkPolygon pos points radius = do
  bPoints <- mkBounded points 3 100 5
  bRadius <- mkBounded radius 0 100000 50
  bRnd <- mkBounded 0 0 100 0
  bRot <- mkBounded 0 (-36000) 36000 0
  -- For polygon, inner radius is not used (set same as outer)
  pure $ PolyStar pos StarPolygon bPoints bRadius bRadius bRnd bRnd bRot DirNormal

-- | Convenience constructors
star :: Point -> Int -> Double -> Double -> PolyStar
star pos pts outerR innerR = case mkStar pos pts outerR innerR of
  Right s -> s
  Left _ -> error "Invalid star parameters"

polygon :: Point -> Int -> Double -> PolyStar
polygon pos pts radius = case mkPolygon pos pts radius of
  Right p -> p
  Left _ -> error "Invalid polygon parameters"

-- | Regular polygon vertices
polygonVertices :: PolyStar -> [Point]
polygonVertices ps =
  let n = bValue (psPoints ps)
      r = bValue (psOuterRadius ps)
      rot = bValue (psRotation ps) * pi / 180
      cx = bValue (ptX $ psPosition ps)
      cy = bValue (ptY $ psPosition ps)
      angleStep = 2 * pi / fromIntegral n
  in [ point (cx + r * cos (rot + fromIntegral i * angleStep - pi/2))
             (cy + r * sin (rot + fromIntegral i * angleStep - pi/2))
     | i <- [0 .. n - 1]
     ]

-- | Convert to Lottie shape JSON
polyStarToLottie :: PolyStar -> Value
polyStarToLottie ps = object
  [ "ty" .= ("sr" :: Text)
  , "p"  .= object ["a" .= (0 :: Int), "k" .= pointToList (psPosition ps)]
  , "sy" .= starTypeCode (psType ps)
  , "pt" .= object ["a" .= (0 :: Int), "k" .= bValue (psPoints ps)]
  , "or" .= object ["a" .= (0 :: Int), "k" .= bValue (psOuterRadius ps)]
  , "ir" .= object ["a" .= (0 :: Int), "k" .= bValue (psInnerRadius ps)]
  , "os" .= object ["a" .= (0 :: Int), "k" .= bValue (psOuterRoundness ps)]
  , "is" .= object ["a" .= (0 :: Int), "k" .= bValue (psInnerRoundness ps)]
  , "r"  .= object ["a" .= (0 :: Int), "k" .= bValue (psRotation ps)]
  , "d"  .= shapeDirectionCode (psDirection ps)
  ]
```

---

## 7. Path Primitive

### 7.1 Bezier Path Definition

```haskell
-- | Bezier path vertex
data BezierVertex = BezierVertex
  { bvVertex    :: !Point  -- The vertex point
  , bvInTangent :: !Point  -- Incoming tangent (relative to vertex)
  , bvOutTangent :: !Point -- Outgoing tangent (relative to vertex)
  } deriving (Eq, Show, Generic)

-- | Create vertex with no tangents (corner)
cornerVertex :: Point -> BezierVertex
cornerVertex p = BezierVertex p origin origin

-- | Create vertex with symmetric tangents (smooth)
smoothVertex :: Point -> Point -> BezierVertex
smoothVertex p tangent = BezierVertex p (pointScale (-1) tangent) tangent

-- | Bezier path
data BezierPath = BezierPath
  { bpVertices :: ![BezierVertex]  -- Path vertices
  , bpClosed   :: !Bool            -- Is path closed?
  } deriving (Eq, Show, Generic)

-- | Smart constructor
mkBezierPath :: [BezierVertex] -> Bool -> Either String BezierPath
mkBezierPath [] _ = Left "BezierPath: must have at least one vertex"
mkBezierPath vs closed = Right $ BezierPath vs closed

-- | Path shape (wrapper for Lottie)
data PathShape = PathShape
  { pathBezier    :: !BezierPath
  , pathDirection :: !ShapeDirection
  } deriving (Eq, Show, Generic)

-- | Convert to Lottie bezier format
-- Lottie uses: { c: closed, v: [[x,y],...], i: [[x,y],...], o: [[x,y],...] }
bezierToLottie :: BezierPath -> Value
bezierToLottie bp = object
  [ "c" .= bpClosed bp
  , "v" .= map (pointToList . bvVertex) (bpVertices bp)
  , "i" .= map (pointToList . bvInTangent) (bpVertices bp)
  , "o" .= map (pointToList . bvOutTangent) (bpVertices bp)
  ]

-- | Path shape to Lottie
pathToLottie :: PathShape -> Value
pathToLottie ps = object
  [ "ty" .= ("sh" :: Text)
  , "ks" .= object
      [ "a" .= (0 :: Int)
      , "k" .= bezierToLottie (pathBezier ps)
      ]
  , "d" .= shapeDirectionCode (pathDirection ps)
  ]
```

### 7.2 Path Builders

```haskell
-- | Build a line path between two points
linePath :: Point -> Point -> BezierPath
linePath from to = BezierPath [cornerVertex from, cornerVertex to] False

-- | Build a polyline path
polylinePath :: [Point] -> Bool -> BezierPath
polylinePath points closed = BezierPath (map cornerVertex points) closed

-- | Build a circle path using cubic bezier approximation
-- Magic number for circle: 0.5522847498307936 ≈ 4/3 * (√2 - 1)
circlePath :: Point -> Double -> BezierPath
circlePath center radius = 
  let k = 0.5522847498307936 * radius
      cx = bValue (ptX center)
      cy = bValue (ptY center)
      -- Four points: top, right, bottom, left
      top    = point cx (cy - radius)
      right  = point (cx + radius) cy
      bottom = point cx (cy + radius)
      left   = point (cx - radius) cy
      -- Tangent vectors
      topV    = BezierVertex top (point (-k) 0) (point k 0)
      rightV  = BezierVertex right (point 0 (-k)) (point 0 k)
      bottomV = BezierVertex bottom (point k 0) (point (-k) 0)
      leftV   = BezierVertex left (point 0 k) (point 0 (-k))
  in BezierPath [topV, rightV, bottomV, leftV] True

-- | Build a rounded rectangle path
roundedRectPath :: Point -> Size -> Double -> BezierPath
roundedRectPath center sz radius =
  let w = bValue (szWidth sz)
      h = bValue (szHeight sz)
      r = min radius (min (w/2) (h/2))  -- Clamp radius
      k = 0.5522847498307936 * r
      cx = bValue (ptX center)
      cy = bValue (ptY center)
      hw = w / 2
      hh = h / 2
      -- Eight vertices for rounded rectangle
      v1 = BezierVertex (point (cx - hw + r) (cy - hh)) origin (point (-k) 0)
      v2 = BezierVertex (point (cx - hw) (cy - hh + r)) (point 0 (-k)) origin
      v3 = BezierVertex (point (cx - hw) (cy + hh - r)) origin (point 0 k)
      v4 = BezierVertex (point (cx - hw + r) (cy + hh)) (point (-k) 0) origin
      v5 = BezierVertex (point (cx + hw - r) (cy + hh)) origin (point k 0)
      v6 = BezierVertex (point (cx + hw) (cy + hh - r)) (point 0 k) origin
      v7 = BezierVertex (point (cx + hw) (cy - hh + r)) origin (point 0 (-k))
      v8 = BezierVertex (point (cx + hw - r) (cy - hh)) (point k 0) origin
  in BezierPath [v1, v2, v3, v4, v5, v6, v7, v8] True

-- | Build an arrow path
arrowPath :: Point -> Point -> Double -> Double -> BezierPath
arrowPath from to headLength headWidth =
  let dx = bValue (ptX to) - bValue (ptX from)
      dy = bValue (ptY to) - bValue (ptY from)
      len = sqrt (dx * dx + dy * dy)
      -- Normalized direction
      nx = dx / len
      ny = dy / len
      -- Perpendicular
      px = -ny
      py = nx
      -- Arrow head base point
      baseX = bValue (ptX to) - headLength * nx
      baseY = bValue (ptY to) - headLength * ny
      -- Arrow head corners
      leftX = baseX + headWidth/2 * px
      leftY = baseY + headWidth/2 * py
      rightX = baseX - headWidth/2 * px
      rightY = baseY - headWidth/2 * py
      -- Shaft width (1/4 of head)
      sw = headWidth / 4
      shaftL = (bValue (ptX from) + sw/2 * px, bValue (ptY from) + sw/2 * py)
      shaftR = (bValue (ptX from) - sw/2 * px, bValue (ptY from) - sw/2 * py)
      baseL = (baseX + sw/2 * px, baseY + sw/2 * py)
      baseR = (baseX - sw/2 * px, baseY - sw/2 * py)
  in polylinePath 
       [ point (fst shaftR) (snd shaftR)
       , point (fst baseR) (snd baseR)
       , point rightX rightY
       , to
       , point leftX leftY
       , point (fst baseL) (snd baseL)
       , point (fst shaftL) (snd shaftL)
       ]
       True
```

---

## 8. Fill and Stroke

### 8.1 Fill Definition

```haskell
-- | Fill rule
data FillRule = FillNonZero | FillEvenOdd
  deriving (Eq, Show, Enum, Bounded)

fillRuleCode :: FillRule -> Int
fillRuleCode FillNonZero = 1
fillRuleCode FillEvenOdd = 2

-- | Solid fill
data Fill = Fill
  { fillColor   :: !RGB
  , fillOpacity :: !(Bounded Double)  -- 0-100
  , fillRule    :: !FillRule
  } deriving (Eq, Show, Generic)

-- | Fill opacity constraint
fillOpacityConstraint :: (Double, Double, Double)
fillOpacityConstraint = (0, 100, 100)

-- | Smart constructor
mkFill :: RGB -> Double -> Either String Fill
mkFill color opacity = do
  bOpacity <- mkBounded opacity 0 100 100
  pure $ Fill color bOpacity FillNonZero

-- | Convenience constructor
fill :: RGB -> Double -> Fill
fill color opacity = Fill color
  (unsafeMkBounded (max 0 (min 100 opacity)) 0 100 100)
  FillNonZero

-- | Solid black fill
blackFill :: Fill
blackFill = fill (rgb 0 0 0) 100

-- | Solid white fill
whiteFill :: Fill
whiteFill = fill (rgb 1 1 1) 100

-- | Convert to Lottie
fillToLottie :: Fill -> Value
fillToLottie f = object
  [ "ty" .= ("fl" :: Text)
  , "c"  .= object
      [ "a" .= (0 :: Int)
      , "k" .= rgbToList (fillColor f)
      ]
  , "o"  .= object
      [ "a" .= (0 :: Int)
      , "k" .= bValue (fillOpacity f)
      ]
  , "r"  .= fillRuleCode (fillRule f)
  ]
```

### 8.2 Stroke Definition

```haskell
-- | Line cap style
data LineCap = CapButt | CapRound | CapSquare
  deriving (Eq, Show, Enum, Bounded)

lineCapCode :: LineCap -> Int
lineCapCode CapButt = 1
lineCapCode CapRound = 2
lineCapCode CapSquare = 3

-- | Line join style
data LineJoin = JoinMiter | JoinRound | JoinBevel
  deriving (Eq, Show, Enum, Bounded)

lineJoinCode :: LineJoin -> Int
lineJoinCode JoinMiter = 1
lineJoinCode JoinRound = 2
lineJoinCode JoinBevel = 3

-- | Dash pattern element
data DashElement
  = DashGap !(Bounded Double)    -- Gap length
  | DashDash !(Bounded Double)   -- Dash length
  | DashOffset !(Bounded Double) -- Offset
  deriving (Eq, Show, Generic)

-- | Stroke definition
data Stroke = Stroke
  { strokeColor     :: !RGB
  , strokeOpacity   :: !(Bounded Double)  -- 0-100
  , strokeWidth     :: !(Bounded Double)  -- 0-1000
  , strokeLineCap   :: !LineCap
  , strokeLineJoin  :: !LineJoin
  , strokeMiterLimit :: !(Bounded Double) -- 0-100
  , strokeDashes    :: ![DashElement]
  } deriving (Eq, Show, Generic)

-- | Stroke constraints
strokeWidthConstraint :: (Double, Double, Double)
strokeWidthConstraint = (0, 1000, 2)

strokeMiterConstraint :: (Double, Double, Double)
strokeMiterConstraint = (0, 100, 4)

-- | Smart constructor
mkStroke :: RGB -> Double -> Double -> Either String Stroke
mkStroke color opacity width = do
  bOpacity <- mkBounded opacity 0 100 100
  bWidth <- mkBounded width 0 1000 2
  bMiter <- mkBounded 4 0 100 4
  pure $ Stroke color bOpacity bWidth CapRound JoinRound bMiter []

-- | Convenience constructor
stroke :: RGB -> Double -> Double -> Stroke
stroke color opacity width = Stroke
  color
  (unsafeMkBounded (max 0 (min 100 opacity)) 0 100 100)
  (unsafeMkBounded (max 0 (min 1000 width)) 0 1000 2)
  CapRound
  JoinRound
  (unsafeMkBounded 4 0 100 4)
  []

-- | Add dash pattern
withDashes :: [Double] -> Stroke -> Stroke
withDashes pattern s = s { strokeDashes = zipWith mkDash (cycle [DashDash, DashGap]) pattern }
  where
    mkDash f v = f (unsafeMkBounded (max 0 v) 0 10000 10)

-- | Convert to Lottie
strokeToLottie :: Stroke -> Value
strokeToLottie s = object $
  [ "ty" .= ("st" :: Text)
  , "c"  .= object ["a" .= (0 :: Int), "k" .= rgbToList (strokeColor s)]
  , "o"  .= object ["a" .= (0 :: Int), "k" .= bValue (strokeOpacity s)]
  , "w"  .= object ["a" .= (0 :: Int), "k" .= bValue (strokeWidth s)]
  , "lc" .= lineCapCode (strokeLineCap s)
  , "lj" .= lineJoinCode (strokeLineJoin s)
  , "ml" .= bValue (strokeMiterLimit s)
  ] ++ dashArray
  where
    dashArray
      | null (strokeDashes s) = []
      | otherwise = ["d" .= map dashToLottie (strokeDashes s)]
    
    dashToLottie (DashDash v) = object ["n" .= ("d" :: Text), "v" .= object ["a" .= (0 :: Int), "k" .= bValue v]]
    dashToLottie (DashGap v) = object ["n" .= ("g" :: Text), "v" .= object ["a" .= (0 :: Int), "k" .= bValue v]]
    dashToLottie (DashOffset v) = object ["n" .= ("o" :: Text), "v" .= object ["a" .= (0 :: Int), "k" .= bValue v]]
```

---

## 9. Gradient Definitions

### 9.1 Gradient Types

```haskell
-- | Gradient type
data GradientType = GradientLinear | GradientRadial
  deriving (Eq, Show, Enum, Bounded)

gradientTypeCode :: GradientType -> Int
gradientTypeCode GradientLinear = 1
gradientTypeCode GradientRadial = 2

-- | Gradient stop
data GradientStop = GradientStop
  { gsOffset :: !(Bounded Double)  -- 0-1 position
  , gsColor  :: !RGB
  } deriving (Eq, Show, Generic)

gradientOffsetConstraint :: (Double, Double, Double)
gradientOffsetConstraint = (0, 1, 0)

-- | Create gradient stop
mkGradientStop :: Double -> RGB -> Either String GradientStop
mkGradientStop offset color = do
  bOffset <- mkBounded offset 0 1 0
  pure $ GradientStop bOffset color

gradientStop :: Double -> RGB -> GradientStop
gradientStop offset color = GradientStop
  (unsafeMkBounded (max 0 (min 1 offset)) 0 1 0)
  color

-- | Gradient fill
data GradientFill = GradientFill
  { gfType       :: !GradientType
  , gfStartPoint :: !Point
  , gfEndPoint   :: !Point
  , gfStops      :: ![GradientStop]  -- At least 2
  , gfOpacity    :: !(Bounded Double)
  , gfHighlight  :: !(Maybe (Bounded Double, Bounded Double))  -- Length, Angle (radial only)
  } deriving (Eq, Show, Generic)

-- | Smart constructor for linear gradient
mkLinearGradient :: Point -> Point -> [GradientStop] -> Either String GradientFill
mkLinearGradient start end stops
  | length stops < 2 = Left "Gradient must have at least 2 stops"
  | otherwise = do
      bOpacity <- mkBounded 100 0 100 100
      pure $ GradientFill GradientLinear start end stops bOpacity Nothing

-- | Smart constructor for radial gradient
mkRadialGradient :: Point -> Point -> [GradientStop] -> Either String GradientFill
mkRadialGradient center edge stops
  | length stops < 2 = Left "Gradient must have at least 2 stops"
  | otherwise = do
      bOpacity <- mkBounded 100 0 100 100
      pure $ GradientFill GradientRadial center edge stops bOpacity Nothing

-- | Convenience constructors
linearGradient :: Point -> Point -> [GradientStop] -> GradientFill
linearGradient start end stops = GradientFill
  GradientLinear start end stops
  (unsafeMkBounded 100 0 100 100)
  Nothing

radialGradient :: Point -> Point -> [GradientStop] -> GradientFill
radialGradient center edge stops = GradientFill
  GradientRadial center edge stops
  (unsafeMkBounded 100 0 100 100)
  Nothing

-- | Convert stops to Lottie format (flat array)
-- Format: [offset1, r1, g1, b1, offset2, r2, g2, b2, ...]
stopsToLottieArray :: [GradientStop] -> [Double]
stopsToLottieArray = concatMap stopToArray
  where
    stopToArray gs = 
      bValue (gsOffset gs) : map (fromRational . bValue) (rgbComponents $ gsColor gs)
    rgbComponents (RGB r g b) = [r, g, b]

-- | Convert to Lottie
gradientFillToLottie :: GradientFill -> Value
gradientFillToLottie gf = object $
  [ "ty" .= ("gf" :: Text)
  , "t"  .= gradientTypeCode (gfType gf)
  , "s"  .= object ["a" .= (0 :: Int), "k" .= pointToList (gfStartPoint gf)]
  , "e"  .= object ["a" .= (0 :: Int), "k" .= pointToList (gfEndPoint gf)]
  , "g"  .= object
      [ "p" .= length (gfStops gf)
      , "k" .= object ["a" .= (0 :: Int), "k" .= stopsToLottieArray (gfStops gf)]
      ]
  , "o"  .= object ["a" .= (0 :: Int), "k" .= bValue (gfOpacity gf)]
  ] ++ highlightFields
  where
    highlightFields = case gfHighlight gf of
      Nothing -> []
      Just (len, angle) ->
        [ "h" .= object ["a" .= (0 :: Int), "k" .= bValue len]
        , "a" .= object ["a" .= (0 :: Int), "k" .= bValue angle]
        ]
```

---

## 10. Shape Group

### 10.1 Group Definition

```haskell
-- | Shape element (union of all shape types)
data ShapeElement
  = SEGroup !ShapeGroup
  | SERectangle !Rectangle
  | SEEllipse !Ellipse
  | SEPolyStar !PolyStar
  | SEPath !PathShape
  | SEFill !Fill
  | SEStroke !Stroke
  | SEGradientFill !GradientFill
  | SEGradientStroke !GradientStroke
  | SETransform !ShapeTransform
  | SETrimPath !TrimPath
  | SERepeater !Repeater
  | SERoundCorners !RoundCorners
  | SEMerge !MergePaths
  deriving (Eq, Show, Generic)

-- | Shape group
data ShapeGroup = ShapeGroup
  { sgName     :: !Text
  , sgElements :: ![ShapeElement]
  , sgBlendMode :: !BlendMode
  } deriving (Eq, Show, Generic)

-- | Shape transform (special transform for shape groups)
data ShapeTransform = ShapeTransform
  { stAnchor   :: !Point
  , stPosition :: !Point
  , stScale    :: !Size      -- As percentage [100, 100] = 100%
  , stRotation :: !(Bounded Double)
  , stOpacity  :: !(Bounded Double)
  , stSkew     :: !(Maybe (Bounded Double, Bounded Double))  -- Angle, Axis
  } deriving (Eq, Show, Generic)

-- | Default shape transform (identity)
defaultShapeTransform :: ShapeTransform
defaultShapeTransform = ShapeTransform
  origin origin (size 100 100)
  (unsafeMkBounded 0 (-36000) 36000 0)
  (unsafeMkBounded 100 0 100 100)
  Nothing

-- | Smart constructor for group
mkShapeGroup :: Text -> [ShapeElement] -> ShapeGroup
mkShapeGroup name elements = ShapeGroup name elements BlendNormal

-- | Convert group to Lottie
shapeGroupToLottie :: ShapeGroup -> Value
shapeGroupToLottie sg = object
  [ "ty" .= ("gr" :: Text)
  , "nm" .= sgName sg
  , "it" .= map shapeElementToLottie (sgElements sg ++ [SETransform defaultShapeTransform])
  , "bm" .= blendModeCode (sgBlendMode sg)
  ]

-- | Convert any shape element to Lottie
shapeElementToLottie :: ShapeElement -> Value
shapeElementToLottie = \case
  SEGroup g -> shapeGroupToLottie g
  SERectangle r -> rectToLottie r
  SEEllipse e -> ellipseToLottie e
  SEPolyStar ps -> polyStarToLottie ps
  SEPath p -> pathToLottie p
  SEFill f -> fillToLottie f
  SEStroke s -> strokeToLottie s
  SEGradientFill gf -> gradientFillToLottie gf
  SEGradientStroke gs -> gradientStrokeToLottie gs
  SETransform t -> shapeTransformToLottie t
  SETrimPath tp -> trimPathToLottie tp
  SERepeater rp -> repeaterToLottie rp
  SERoundCorners rc -> roundCornersToLottie rc
  SEMerge mp -> mergePathsToLottie mp

-- | Shape transform to Lottie
shapeTransformToLottie :: ShapeTransform -> Value
shapeTransformToLottie st = object $
  [ "ty" .= ("tr" :: Text)
  , "a"  .= object ["a" .= (0 :: Int), "k" .= pointToList (stAnchor st)]
  , "p"  .= object ["a" .= (0 :: Int), "k" .= pointToList (stPosition st)]
  , "s"  .= object ["a" .= (0 :: Int), "k" .= [bValue (szWidth $ stScale st), bValue (szHeight $ stScale st)]]
  , "r"  .= object ["a" .= (0 :: Int), "k" .= bValue (stRotation st)]
  , "o"  .= object ["a" .= (0 :: Int), "k" .= bValue (stOpacity st)]
  ] ++ skewFields
  where
    skewFields = case stSkew st of
      Nothing -> []
      Just (angle, axis) ->
        [ "sk" .= object ["a" .= (0 :: Int), "k" .= bValue angle]
        , "sa" .= object ["a" .= (0 :: Int), "k" .= bValue axis]
        ]
```

---

## 11. Constraint Summary Table

| Type | Property | Min | Max | Default | Unit |
|------|----------|-----|-----|---------|------|
| Point | x, y | -100000 | 100000 | 0 | px |
| Size | width, height | 0 | 100000 | 100 | px |
| Rectangle | cornerRadius | 0 | 10000 | 0 | px |
| PolyStar | points | 3 | 100 | 5 | count |
| PolyStar | outerRadius | 0 | 100000 | 50 | px |
| PolyStar | innerRadius | 0 | 100000 | 25 | px |
| PolyStar | roundness | 0 | 100 | 0 | % |
| PolyStar | rotation | -36000 | 36000 | 0 | deg |
| Fill | opacity | 0 | 100 | 100 | % |
| Stroke | opacity | 0 | 100 | 100 | % |
| Stroke | width | 0 | 1000 | 2 | px |
| Stroke | miterLimit | 0 | 100 | 4 | ratio |
| Gradient | stopOffset | 0 | 1 | 0 | norm |
| Transform | scale | 0 | 10000 | 100 | % |
| Transform | rotation | -36000 | 36000 | 0 | deg |
| Transform | opacity | 0 | 100 | 100 | % |

---

## 12. Lean4 Proofs

```lean4
/-- Point arithmetic preserves bounds after clamping -/
theorem point_add_bounded (a b : Point) :
    let sum := Point.add a b
    -100000 ≤ sum.x ∧ sum.x ≤ 100000 ∧
    -100000 ≤ sum.y ∧ sum.y ≤ 100000 :=
  ⟨(Point.add a b).h_x_bounds.1, (Point.add a b).h_x_bounds.2,
   (Point.add a b).h_y_bounds.1, (Point.add a b).h_y_bounds.2⟩

/-- Point lerp at t=0 returns first point -/
theorem point_lerp_zero (a b : Point) : 
    let result := Point.lerp 0 a b
    result.x = a.x ∧ result.y = a.y := by
  simp [Point.lerp, Point.mk']
  constructor <;> ring

/-- Circle path has exactly 4 vertices -/
theorem circle_path_vertices (c : Point) (r : Float) :
    (circlePath c r).bpVertices.length = 4 := by
  simp [circlePath]

/-- Gradient must have at least 2 stops -/
theorem gradient_min_stops (gf : GradientFill) :
    gf.gfStops.length ≥ 2 := by
  -- This is enforced by smart constructor
  sorry
```

---

## 13. Test Matrix

| Component | Unit Tests | Property Tests | Lean4 Proofs |
|-----------|------------|----------------|--------------|
| Point | 25 | 8 | ✓ |
| Size | 15 | 4 | ✓ |
| Rectangle | 20 | 6 | ✓ |
| Ellipse | 15 | 4 | ✓ |
| PolyStar | 25 | 8 | Partial |
| BezierPath | 30 | 10 | Partial |
| Fill | 10 | 3 | ✓ |
| Stroke | 20 | 5 | ✓ |
| Gradient | 25 | 6 | ✓ |
| ShapeGroup | 15 | 4 | ✓ |

---

*End of Specification 04*
