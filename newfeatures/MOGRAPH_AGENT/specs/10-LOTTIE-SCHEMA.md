# Specification 10: Lottie Schema
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-10  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines the complete Lottie JSON schema with:

1. **Type definitions** for all Lottie structures
2. **Validation rules** with constraints
3. **Serialization** to deterministic JSON
4. **Compatibility** with Lottie spec v5.7.1+

---

## 2. Root Animation Structure

### 2.1 Lean4 Definition

```lean4
/-- Lottie animation document -/
structure LottieAnimation where
  -- Required fields
  v : String                       -- Version string "5.7.1"
  fr : Nat                         -- Frame rate
  ip : Nat                         -- In point (start frame)
  op : Nat                         -- Out point (end frame)
  w : Nat                          -- Width in pixels
  h : Nat                          -- Height in pixels
  layers : List LottieLayer        -- Layer list
  -- Optional fields
  nm : Option String               -- Animation name
  ddd : Option Bool                -- 3D (always false)
  assets : Option (List LottieAsset)
  fonts : Option LottieFonts
  markers : Option (List LottieMarker)
  -- Constraints
  h_fr : 1 ≤ fr ∧ fr ≤ 120
  h_w : 1 ≤ w ∧ w ≤ 16384
  h_h : 1 ≤ h ∧ h ≤ 16384
  h_ip_op : ip ≤ op
  deriving Repr
```

### 2.2 Haskell Implementation

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.Lottie.Schema where

import Data.Aeson
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Core.Bounded

-- | Lottie animation root document
data LottieAnimation = LottieAnimation
  { laVersion    :: !Text               -- "v": version string
  , laFrameRate  :: !(Bounded Int)      -- "fr": 1-120
  , laInPoint    :: !(Bounded Int)      -- "ip": start frame
  , laOutPoint   :: !(Bounded Int)      -- "op": end frame
  , laWidth      :: !(Bounded Int)      -- "w": 1-16384
  , laHeight     :: !(Bounded Int)      -- "h": 1-16384
  , laLayers     :: ![LottieLayer]      -- "layers"
  , laName       :: !(Maybe Text)       -- "nm"
  , la3D         :: !Bool               -- "ddd": always false
  , laAssets     :: ![LottieAsset]      -- "assets"
  , laFonts      :: !(Maybe LottieFonts) -- "fonts"
  , laMarkers    :: ![LottieMarker]     -- "markers"
  } deriving (Eq, Show, Generic)

-- | Constraints
animationConstraints :: AnimationConstraints
animationConstraints = AnimationConstraints
  { acFrameRate = (1, 120, 60)
  , acWidth = (1, 16384, 1920)
  , acHeight = (1, 16384, 1080)
  , acInPoint = (0, maxBound, 0)
  , acOutPoint = (1, maxBound, 180)
  }

-- | Smart constructor with validation
mkLottieAnimation 
  :: Int -> Int -> Int -> Int -> Int -> Int -> [LottieLayer] 
  -> Either String LottieAnimation
mkLottieAnimation fr ip op w h layers = do
  bFr <- mkBounded fr 1 120 60
  bIp <- mkBounded ip 0 maxBound 0
  bOp <- mkBounded op 1 maxBound 180
  bW <- mkBounded w 1 16384 1920
  bH <- mkBounded h 1 16384 1080
  
  when (bValue bIp > bValue bOp) $
    Left "In point must be <= out point"
  
  pure $ LottieAnimation
    { laVersion = "5.7.1"
    , laFrameRate = bFr
    , laInPoint = bIp
    , laOutPoint = bOp
    , laWidth = bW
    , laHeight = bH
    , laLayers = layers
    , laName = Nothing
    , la3D = False
    , laAssets = []
    , laFonts = Nothing
    , laMarkers = []
    }

-- | JSON serialization (deterministic)
instance ToJSON LottieAnimation where
  toJSON la = object $ filter (not . isNull . snd)
    [ "v"      .= laVersion la
    , "fr"     .= bValue (laFrameRate la)
    , "ip"     .= bValue (laInPoint la)
    , "op"     .= bValue (laOutPoint la)
    , "w"      .= bValue (laWidth la)
    , "h"      .= bValue (laHeight la)
    , "nm"     .= laName la
    , "ddd"    .= (if la3D la then 1 else 0 :: Int)
    , "layers" .= laLayers la
    , "assets" .= if null (laAssets la) then Nothing else Just (laAssets la)
    , "fonts"  .= laFonts la
    , "markers" .= if null (laMarkers la) then Nothing else Just (laMarkers la)
    ]
    where
      isNull Null = True
      isNull _ = False
```

---

## 3. Layer Types

### 3.1 Layer Type Enumeration

```haskell
-- | Layer type codes
data LayerType
  = LayerPrecomp   -- 0: Pre-composition
  | LayerSolid     -- 1: Solid color
  | LayerImage     -- 2: Image
  | LayerNull      -- 3: Null (transform only)
  | LayerShape     -- 4: Shape
  | LayerText      -- 5: Text
  | LayerAudio     -- 6: Audio (unsupported)
  | LayerCamera    -- 13: Camera (unsupported)
  deriving (Eq, Show, Enum, Bounded)

layerTypeCode :: LayerType -> Int
layerTypeCode = \case
  LayerPrecomp -> 0
  LayerSolid -> 1
  LayerImage -> 2
  LayerNull -> 3
  LayerShape -> 4
  LayerText -> 5
  LayerAudio -> 6
  LayerCamera -> 13

-- | Base layer fields (common to all types)
data LayerBase = LayerBase
  { lbIndex      :: !Int              -- "ind": layer index
  , lbName       :: !Text             -- "nm": layer name
  , lbType       :: !LayerType        -- "ty": layer type
  , lbInPoint    :: !(Bounded Int)    -- "ip": in point
  , lbOutPoint   :: !(Bounded Int)    -- "op": out point
  , lbStartTime  :: !(Bounded Int)    -- "st": start time
  , lbTransform  :: !LottieTransform  -- "ks": transform
  , lbParent     :: !(Maybe Int)      -- "parent": parent index
  , lbBlendMode  :: !BlendMode        -- "bm": blend mode
  , lbAutoOrient :: !Bool             -- "ao": auto-orient
  , lbHidden     :: !Bool             -- "hd": hidden
  , lbMatte      :: !(Maybe MatteMode) -- "tt": track matte
  } deriving (Eq, Show, Generic)

-- | Complete layer (union type)
data LottieLayer
  = LLShape !LayerBase ![ShapeElement]           -- Shape layer
  | LLSolid !LayerBase !Text !Int !Int           -- Solid (color, w, h)
  | LLImage !LayerBase !Text                     -- Image (asset ref)
  | LLNull !LayerBase                            -- Null layer
  | LLPrecomp !LayerBase !Text !Int !Int         -- Precomp (ref, w, h)
  | LLText !LayerBase !TextData                  -- Text layer
  deriving (Eq, Show, Generic)

-- | Get base from any layer
layerBase :: LottieLayer -> LayerBase
layerBase = \case
  LLShape b _ -> b
  LLSolid b _ _ _ -> b
  LLImage b _ -> b
  LLNull b -> b
  LLPrecomp b _ _ _ -> b
  LLText b _ -> b

instance ToJSON LottieLayer where
  toJSON layer = 
    let base = layerBase layer
        baseFields = 
          [ "ind" .= lbIndex base
          , "nm"  .= lbName base
          , "ty"  .= layerTypeCode (lbType base)
          , "ip"  .= bValue (lbInPoint base)
          , "op"  .= bValue (lbOutPoint base)
          , "st"  .= bValue (lbStartTime base)
          , "ks"  .= lbTransform base
          , "bm"  .= blendModeCode (lbBlendMode base)
          , "ao"  .= (if lbAutoOrient base then 1 else 0 :: Int)
          ]
        parentField = maybe [] (\p -> ["parent" .= p]) (lbParent base)
        hiddenField = if lbHidden base then ["hd" .= True] else []
        matteField = maybe [] (\m -> ["tt" .= matteModeCode m]) (lbMatte base)
        typeFields = case layer of
          LLShape _ shapes -> ["shapes" .= shapes]
          LLSolid _ color w h -> 
            ["sc" .= color, "sw" .= w, "sh" .= h]
          LLImage _ ref -> ["refId" .= ref]
          LLNull _ -> []
          LLPrecomp _ ref w h -> 
            ["refId" .= ref, "w" .= w, "h" .= h]
          LLText _ textData -> ["t" .= textData]
    in object $ baseFields ++ parentField ++ hiddenField ++ matteField ++ typeFields
```

### 3.2 Layer Constraints

| Property | Min | Max | Default |
|----------|-----|-----|---------|
| index | 0 | 10000 | auto |
| inPoint | 0 | MAX_INT | 0 |
| outPoint | 0 | MAX_INT | animation.op |
| startTime | -MAX_INT | MAX_INT | 0 |

---

## 4. Transform Structure

### 4.1 Definition

```haskell
-- | Layer transform (required for all layers)
data LottieTransform = LottieTransform
  { ltAnchor    :: !AnimatedValue Point     -- "a": anchor point
  , ltPosition  :: !AnimatedValue Point     -- "p": position
  , ltScale     :: !AnimatedValue Point     -- "s": scale (as %)
  , ltRotation  :: !AnimatedValue Double    -- "r": rotation (degrees)
  , ltOpacity   :: !AnimatedValue Double    -- "o": opacity (0-100)
  , ltSkew      :: !(Maybe (AnimatedValue Double))  -- "sk": skew angle
  , ltSkewAxis  :: !(Maybe (AnimatedValue Double))  -- "sa": skew axis
  } deriving (Eq, Show, Generic)

-- | Animated value (static or keyframed)
data AnimatedValue a
  = AVStatic !a                    -- Static value
  | AVAnimated ![Keyframe a]       -- Keyframed
  deriving (Eq, Show, Generic)

-- | Keyframe structure
data Keyframe a = Keyframe
  { kfTime    :: !Int              -- "t": frame number
  , kfValue   :: !a                -- "s": start value
  , kfEndValue :: !(Maybe a)       -- "e": end value (deprecated)
  , kfHold    :: !Bool             -- "h": hold keyframe
  , kfEaseIn  :: !(Maybe EasingHandle)  -- "i": ease in
  , kfEaseOut :: !(Maybe EasingHandle)  -- "o": ease out
  } deriving (Eq, Show, Generic)

-- | Easing handle (bezier control point)
data EasingHandle = EasingHandle
  { ehX :: ![Double]  -- X coordinates (0-1)
  , ehY :: ![Double]  -- Y coordinates (can exceed 0-1 for overshoot)
  } deriving (Eq, Show, Generic)

-- | Default transform (identity)
defaultTransform :: LottieTransform
defaultTransform = LottieTransform
  { ltAnchor = AVStatic (point 0 0)
  , ltPosition = AVStatic (point 0 0)
  , ltScale = AVStatic (point 100 100)
  , ltRotation = AVStatic 0
  , ltOpacity = AVStatic 100
  , ltSkew = Nothing
  , ltSkewAxis = Nothing
  }

instance ToJSON LottieTransform where
  toJSON lt = object $ filter (not . isNull . snd)
    [ "a" .= animatedToJSON (ltAnchor lt)
    , "p" .= animatedToJSON (ltPosition lt)
    , "s" .= animatedToJSON (ltScale lt)
    , "r" .= animatedToJSON (ltRotation lt)
    , "o" .= animatedToJSON (ltOpacity lt)
    , "sk" .= fmap animatedToJSON (ltSkew lt)
    , "sa" .= fmap animatedToJSON (ltSkewAxis lt)
    ]
    where
      isNull Null = True
      isNull _ = False

-- | Convert animated value to Lottie JSON
animatedToJSON :: ToJSON a => AnimatedValue a -> Value
animatedToJSON = \case
  AVStatic v -> object
    [ "a" .= (0 :: Int)  -- Not animated
    , "k" .= v
    ]
  AVAnimated kfs -> object
    [ "a" .= (1 :: Int)  -- Animated
    , "k" .= map keyframeToJSON kfs
    ]

keyframeToJSON :: ToJSON a => Keyframe a -> Value
keyframeToJSON kf = object $ filter (not . isNull . snd)
  [ "t" .= kfTime kf
  , "s" .= [kfValue kf]  -- Lottie wraps in array
  , "e" .= fmap (: []) (kfEndValue kf)
  , "h" .= if kfHold kf then Just (1 :: Int) else Nothing
  , "i" .= kfEaseIn kf
  , "o" .= kfEaseOut kf
  ]
  where
    isNull Null = True
    isNull _ = False

instance ToJSON EasingHandle where
  toJSON eh = object
    [ "x" .= ehX eh
    , "y" .= ehY eh
    ]
```

### 4.2 Transform Constraints

| Property | Min | Max | Default | Unit |
|----------|-----|-----|---------|------|
| anchor.x/y | -100000 | 100000 | 0 | px |
| position.x/y | -100000 | 100000 | 0 | px |
| scale.x/y | 0 | 10000 | 100 | % |
| rotation | -36000 | 36000 | 0 | deg |
| opacity | 0 | 100 | 100 | % |
| skew | -90 | 90 | 0 | deg |
| skewAxis | -360 | 360 | 0 | deg |
| easing.x | 0 | 1 | 0.5 | norm |
| easing.y | -2 | 3 | 0.5 | norm |

---

## 5. Shape Elements

### 5.1 Shape Type Codes

```haskell
-- | Shape element type codes
data ShapeType
  = STGroup        -- "gr": Group
  | STRect         -- "rc": Rectangle
  | STEllipse      -- "el": Ellipse
  | STPolyStar     -- "sr": Polystar
  | STPath         -- "sh": Path
  | STFill         -- "fl": Fill
  | STStroke       -- "st": Stroke
  | STGradientFill -- "gf": Gradient fill
  | STGradientStroke -- "gs": Gradient stroke
  | STTransform    -- "tr": Transform
  | STTrimPath     -- "tm": Trim path
  | STRepeater     -- "rp": Repeater
  | STRoundCorners -- "rd": Round corners
  | STMergePaths   -- "mm": Merge paths
  | STTwist        -- "tw": Twist
  | STPuckerBloat  -- "pb": Pucker/bloat
  | STZigZag       -- "zz": Zig-zag
  | STOffset       -- "op": Offset path
  deriving (Eq, Show, Enum, Bounded)

shapeTypeCode :: ShapeType -> Text
shapeTypeCode = \case
  STGroup -> "gr"
  STRect -> "rc"
  STEllipse -> "el"
  STPolyStar -> "sr"
  STPath -> "sh"
  STFill -> "fl"
  STStroke -> "st"
  STGradientFill -> "gf"
  STGradientStroke -> "gs"
  STTransform -> "tr"
  STTrimPath -> "tm"
  STRepeater -> "rp"
  STRoundCorners -> "rd"
  STMergePaths -> "mm"
  STTwist -> "tw"
  STPuckerBloat -> "pb"
  STZigZag -> "zz"
  STOffset -> "op"
```

### 5.2 Shape Element Definitions

```haskell
-- | Shape element (discriminated union)
data ShapeElement
  = SEGroup !ShapeGroup
  | SERect !ShapeRect
  | SEEllipse !ShapeEllipse
  | SEPolyStar !ShapePolyStar
  | SEPath !ShapePath
  | SEFill !ShapeFill
  | SEStroke !ShapeStroke
  | SEGradientFill !ShapeGradientFill
  | SEGradientStroke !ShapeGradientStroke
  | SETransform !ShapeTransform
  | SETrimPath !ShapeTrimPath
  | SERepeater !ShapeRepeater
  | SERoundCorners !ShapeRoundCorners
  | SEMergePaths !ShapeMergePaths
  deriving (Eq, Show, Generic)

-- | Shape group
data ShapeGroup = ShapeGroup
  { sgName       :: !Text
  , sgElements   :: ![ShapeElement]
  , sgNumProps   :: !Int            -- "np": number of properties
  , sgBlendMode  :: !BlendMode
  , sgHidden     :: !Bool
  } deriving (Eq, Show, Generic)

-- | Rectangle shape
data ShapeRect = ShapeRect
  { srName       :: !Text
  , srPosition   :: !AnimatedValue Point
  , srSize       :: !AnimatedValue Point
  , srRadius     :: !AnimatedValue Double  -- Corner radius
  , srDirection  :: !ShapeDirection
  , srHidden     :: !Bool
  } deriving (Eq, Show, Generic)

-- | Ellipse shape
data ShapeEllipse = ShapeEllipse
  { seeName      :: !Text
  , seePosition  :: !AnimatedValue Point
  , seeSize      :: !AnimatedValue Point
  , seeDirection :: !ShapeDirection
  , seeHidden    :: !Bool
  } deriving (Eq, Show, Generic)

-- | Polystar shape (star or polygon)
data ShapePolyStar = ShapePolyStar
  { spsName          :: !Text
  , spsPosition      :: !AnimatedValue Point
  , spsStarType      :: !StarType
  , spsPoints        :: !AnimatedValue Double
  , spsOuterRadius   :: !AnimatedValue Double
  , spsInnerRadius   :: !AnimatedValue Double
  , spsOuterRoundness :: !AnimatedValue Double
  , spsInnerRoundness :: !AnimatedValue Double
  , spsRotation      :: !AnimatedValue Double
  , spsDirection     :: !ShapeDirection
  , spsHidden        :: !Bool
  } deriving (Eq, Show, Generic)

-- | Path shape (bezier)
data ShapePath = ShapePath
  { spName      :: !Text
  , spPath      :: !AnimatedValue BezierShape
  , spDirection :: !ShapeDirection
  , spHidden    :: !Bool
  } deriving (Eq, Show, Generic)

-- | Bezier shape data
data BezierShape = BezierShape
  { bsClosed    :: !Bool
  , bsVertices  :: ![[Double]]    -- [[x,y], ...]
  , bsInTangents :: ![[Double]]   -- Relative to vertex
  , bsOutTangents :: ![[Double]]  -- Relative to vertex
  } deriving (Eq, Show, Generic)

instance ToJSON BezierShape where
  toJSON bs = object
    [ "c" .= bsClosed bs
    , "v" .= bsVertices bs
    , "i" .= bsInTangents bs
    , "o" .= bsOutTangents bs
    ]

-- | Fill shape
data ShapeFill = ShapeFill
  { sfName     :: !Text
  , sfColor    :: !AnimatedValue [Double]  -- [r,g,b] or [r,g,b,a]
  , sfOpacity  :: !AnimatedValue Double
  , sfFillRule :: !FillRule
  , sfHidden   :: !Bool
  } deriving (Eq, Show, Generic)

-- | Stroke shape
data ShapeStroke = ShapeStroke
  { ssName       :: !Text
  , ssColor      :: !AnimatedValue [Double]
  , ssOpacity    :: !AnimatedValue Double
  , ssWidth      :: !AnimatedValue Double
  , ssLineCap    :: !LineCap
  , ssLineJoin   :: !LineJoin
  , ssMiterLimit :: !Double
  , ssDashes     :: ![DashElement]
  , ssHidden     :: !Bool
  } deriving (Eq, Show, Generic)

-- | Dash element
data DashElement = DashElement
  { deName  :: !DashType
  , deValue :: !AnimatedValue Double
  } deriving (Eq, Show, Generic)

data DashType = DashDash | DashGap | DashOffset
  deriving (Eq, Show, Enum, Bounded)

-- | Trim path modifier
data ShapeTrimPath = ShapeTrimPath
  { stpName     :: !Text
  , stpStart    :: !AnimatedValue Double  -- 0-100%
  , stpEnd      :: !AnimatedValue Double  -- 0-100%
  , stpOffset   :: !AnimatedValue Double  -- degrees
  , stpMultiple :: !TrimMultiple
  , stpHidden   :: !Bool
  } deriving (Eq, Show, Generic)

data TrimMultiple = TrimSimultaneously | TrimIndividually
  deriving (Eq, Show, Enum, Bounded)

-- | Shape transform
data ShapeTransform = ShapeTransform
  { sstAnchor   :: !AnimatedValue Point
  , sstPosition :: !AnimatedValue Point
  , sstScale    :: !AnimatedValue Point
  , sstRotation :: !AnimatedValue Double
  , sstOpacity  :: !AnimatedValue Double
  , sstSkew     :: !(Maybe (AnimatedValue Double))
  , sstSkewAxis :: !(Maybe (AnimatedValue Double))
  } deriving (Eq, Show, Generic)
```

### 5.3 Shape Element Serialization

```haskell
instance ToJSON ShapeElement where
  toJSON = \case
    SEGroup g -> object
      [ "ty" .= ("gr" :: Text)
      , "nm" .= sgName g
      , "it" .= sgElements g
      , "np" .= sgNumProps g
      , "bm" .= blendModeCode (sgBlendMode g)
      , "hd" .= sgHidden g
      ]
    
    SERect r -> object
      [ "ty" .= ("rc" :: Text)
      , "nm" .= srName r
      , "p"  .= animatedToJSON (srPosition r)
      , "s"  .= animatedToJSON (srSize r)
      , "r"  .= animatedToJSON (srRadius r)
      , "d"  .= shapeDirectionCode (srDirection r)
      , "hd" .= srHidden r
      ]
    
    SEEllipse e -> object
      [ "ty" .= ("el" :: Text)
      , "nm" .= seeName e
      , "p"  .= animatedToJSON (seePosition e)
      , "s"  .= animatedToJSON (seeSize e)
      , "d"  .= shapeDirectionCode (seeDirection e)
      , "hd" .= seeHidden e
      ]
    
    SEFill f -> object
      [ "ty" .= ("fl" :: Text)
      , "nm" .= sfName f
      , "c"  .= animatedToJSON (sfColor f)
      , "o"  .= animatedToJSON (sfOpacity f)
      , "r"  .= fillRuleCode (sfFillRule f)
      , "hd" .= sfHidden f
      ]
    
    SEStroke s -> object
      [ "ty" .= ("st" :: Text)
      , "nm" .= ssName s
      , "c"  .= animatedToJSON (ssColor s)
      , "o"  .= animatedToJSON (ssOpacity s)
      , "w"  .= animatedToJSON (ssWidth s)
      , "lc" .= lineCapCode (ssLineCap s)
      , "lj" .= lineJoinCode (ssLineJoin s)
      , "ml" .= ssMiterLimit s
      , "d"  .= if null (ssDashes s) then Nothing else Just (ssDashes s)
      , "hd" .= ssHidden s
      ]
    
    SETrimPath tp -> object
      [ "ty" .= ("tm" :: Text)
      , "nm" .= stpName tp
      , "s"  .= animatedToJSON (stpStart tp)
      , "e"  .= animatedToJSON (stpEnd tp)
      , "o"  .= animatedToJSON (stpOffset tp)
      , "m"  .= trimMultipleCode (stpMultiple tp)
      , "hd" .= stpHidden tp
      ]
    
    SETransform t -> object
      [ "ty" .= ("tr" :: Text)
      , "a"  .= animatedToJSON (sstAnchor t)
      , "p"  .= animatedToJSON (sstPosition t)
      , "s"  .= animatedToJSON (sstScale t)
      , "r"  .= animatedToJSON (sstRotation t)
      , "o"  .= animatedToJSON (sstOpacity t)
      , "sk" .= fmap animatedToJSON (sstSkew t)
      , "sa" .= fmap animatedToJSON (sstSkewAxis t)
      ]
    
    -- ... other shape types
    _ -> object []
```

---

## 6. Assets

### 6.1 Asset Types

```haskell
-- | Asset types
data LottieAsset
  = LAImage !ImageAsset
  | LAPrecomp !PrecompAsset
  | LAAudio !AudioAsset
  deriving (Eq, Show, Generic)

-- | Image asset
data ImageAsset = ImageAsset
  { iaId     :: !Text      -- "id": unique identifier
  , iaWidth  :: !Int       -- "w": width
  , iaHeight :: !Int       -- "h": height
  , iaPath   :: !Text      -- "p": file path or data URI
  , iaDir    :: !Text      -- "u": directory
  , iaEmbed  :: !Bool      -- "e": embedded (base64)
  } deriving (Eq, Show, Generic)

-- | Precomposition asset
data PrecompAsset = PrecompAsset
  { paId     :: !Text           -- "id"
  , paLayers :: ![LottieLayer]  -- "layers"
  , paFrameRate :: !(Maybe Int) -- "fr" (optional override)
  } deriving (Eq, Show, Generic)

-- | Audio asset
data AudioAsset = AudioAsset
  { aaId   :: !Text
  , aaPath :: !Text
  , aaDir  :: !Text
  } deriving (Eq, Show, Generic)

instance ToJSON LottieAsset where
  toJSON = \case
    LAImage img -> object
      [ "id" .= iaId img
      , "w"  .= iaWidth img
      , "h"  .= iaHeight img
      , "p"  .= iaPath img
      , "u"  .= iaDir img
      , "e"  .= if iaEmbed img then 1 else 0 :: Int
      ]
    LAPrecomp pc -> object
      [ "id"     .= paId pc
      , "layers" .= paLayers pc
      , "fr"     .= paFrameRate pc
      ]
    LAAudio aud -> object
      [ "id" .= aaId aud
      , "p"  .= aaPath aud
      , "u"  .= aaDir aud
      ]
```

---

## 7. Enumerations

### 7.1 All Enum Definitions

```haskell
-- | Blend modes (Lottie spec)
data BlendMode
  = BlendNormal | BlendMultiply | BlendScreen | BlendOverlay
  | BlendDarken | BlendLighten | BlendColorDodge | BlendColorBurn
  | BlendHardLight | BlendSoftLight | BlendDifference | BlendExclusion
  | BlendHue | BlendSaturation | BlendColor | BlendLuminosity
  | BlendAdd | BlendHardMix
  deriving (Eq, Show, Enum, Bounded)

blendModeCode :: BlendMode -> Int
blendModeCode = fromEnum

-- | Fill rule
data FillRule = FillNonZero | FillEvenOdd
  deriving (Eq, Show, Enum, Bounded)

fillRuleCode :: FillRule -> Int
fillRuleCode FillNonZero = 1
fillRuleCode FillEvenOdd = 2

-- | Line cap
data LineCap = CapButt | CapRound | CapSquare
  deriving (Eq, Show, Enum, Bounded)

lineCapCode :: LineCap -> Int
lineCapCode CapButt = 1
lineCapCode CapRound = 2
lineCapCode CapSquare = 3

-- | Line join
data LineJoin = JoinMiter | JoinRound | JoinBevel
  deriving (Eq, Show, Enum, Bounded)

lineJoinCode :: LineJoin -> Int
lineJoinCode JoinMiter = 1
lineJoinCode JoinRound = 2
lineJoinCode JoinBevel = 3

-- | Shape direction
data ShapeDirection = DirClockwise | DirCounterClockwise
  deriving (Eq, Show, Enum, Bounded)

shapeDirectionCode :: ShapeDirection -> Int
shapeDirectionCode DirClockwise = 1
shapeDirectionCode DirCounterClockwise = 3

-- | Star type
data StarType = StarStar | StarPolygon
  deriving (Eq, Show, Enum, Bounded)

starTypeCode :: StarType -> Int
starTypeCode StarStar = 1
starTypeCode StarPolygon = 2

-- | Gradient type
data GradientType = GradientLinear | GradientRadial
  deriving (Eq, Show, Enum, Bounded)

gradientTypeCode :: GradientType -> Int
gradientTypeCode GradientLinear = 1
gradientTypeCode GradientRadial = 2

-- | Matte mode
data MatteMode = MatteAlpha | MatteInvertedAlpha | MatteLuma | MatteInvertedLuma
  deriving (Eq, Show, Enum, Bounded)

matteModeCode :: MatteMode -> Int
matteModeCode MatteAlpha = 1
matteModeCode MatteInvertedAlpha = 2
matteModeCode MatteLuma = 3
matteModeCode MatteInvertedLuma = 4

-- | Trim path multiple
trimMultipleCode :: TrimMultiple -> Int
trimMultipleCode TrimSimultaneously = 1
trimMultipleCode TrimIndividually = 2
```

---

## 8. Validation

### 8.1 Validation Rules

```haskell
-- | Validation error types
data LottieValidationError
  = LVEInvalidVersion Text
  | LVEInvalidDimension Text Int Int Int  -- name, value, min, max
  | LVEInvalidFrameRange Int Int
  | LVELayerIndexDuplicate Int
  | LVELayerParentCycle [Int]
  | LVEAssetNotFound Text
  | LVEInvalidKeyframe Int Text  -- frame, reason
  | LVEShapeGroupEmpty Text
  | LVEGradientTooFewStops Int
  deriving (Eq, Show)

-- | Validate complete animation
validateLottie :: LottieAnimation -> Either [LottieValidationError] ()
validateLottie anim = do
  let errors = concat
        [ validateVersion anim
        , validateDimensions anim
        , validateFrameRange anim
        , validateLayers anim
        , validateAssets anim
        ]
  if null errors then Right () else Left errors

validateVersion :: LottieAnimation -> [LottieValidationError]
validateVersion anim =
  let v = laVersion anim
  in if v `elem` ["5.7.1", "5.7.0", "5.6.0", "5.5.0"]
     then []
     else [LVEInvalidVersion v]

validateDimensions :: LottieAnimation -> [LottieValidationError]
validateDimensions anim = concat
  [ checkBound "width" (bValue $ laWidth anim) 1 16384
  , checkBound "height" (bValue $ laHeight anim) 1 16384
  , checkBound "frameRate" (bValue $ laFrameRate anim) 1 120
  ]
  where
    checkBound name val lo hi
      | val < lo || val > hi = [LVEInvalidDimension name val lo hi]
      | otherwise = []

validateFrameRange :: LottieAnimation -> [LottieValidationError]
validateFrameRange anim =
  let ip = bValue $ laInPoint anim
      op = bValue $ laOutPoint anim
  in if ip <= op then [] else [LVEInvalidFrameRange ip op]

validateLayers :: LottieAnimation -> [LottieValidationError]
validateLayers anim =
  let layers = laLayers anim
      indices = map (lbIndex . layerBase) layers
      duplicates = findDuplicates indices
      cycles = findParentCycles layers
  in map LVELayerIndexDuplicate duplicates ++
     map LVELayerParentCycle cycles
  where
    findDuplicates xs = [x | (x:_:_) <- group (sort xs)]
    
    findParentCycles layers =
      let indexMap = Map.fromList [(lbIndex $ layerBase l, l) | l <- layers]
      in catMaybes [findCycle indexMap [] (lbIndex $ layerBase l) | l <- layers]
    
    findCycle m visited idx
      | idx `elem` visited = Just (reverse $ idx : visited)
      | otherwise = case Map.lookup idx m of
          Nothing -> Nothing
          Just layer -> case lbParent (layerBase layer) of
            Nothing -> Nothing
            Just pid -> findCycle m (idx : visited) pid
```

---

## 9. Constraint Summary

| Type | Property | Min | Max | Default |
|------|----------|-----|-----|---------|
| Animation | frameRate | 1 | 120 | 60 |
| Animation | width | 1 | 16384 | 1920 |
| Animation | height | 1 | 16384 | 1080 |
| Animation | inPoint | 0 | MAX | 0 |
| Animation | outPoint | 1 | MAX | 180 |
| Layer | index | 0 | 10000 | auto |
| Transform | anchor | -100000 | 100000 | 0 |
| Transform | position | -100000 | 100000 | 0 |
| Transform | scale | 0 | 10000 | 100 |
| Transform | rotation | -36000 | 36000 | 0 |
| Transform | opacity | 0 | 100 | 100 |
| Keyframe | time | 0 | MAX | 0 |
| Easing | x | 0 | 1 | 0.5 |
| Easing | y | -2 | 3 | 0.5 |
| Shape | cornerRadius | 0 | 10000 | 0 |
| Shape | points | 3 | 100 | 5 |
| Fill | opacity | 0 | 100 | 100 |
| Stroke | width | 0 | 1000 | 2 |
| Stroke | miterLimit | 0 | 100 | 4 |
| TrimPath | start/end | 0 | 100 | 0/100 |
| TrimPath | offset | -360 | 360 | 0 |

---

## 10. Test Matrix

| Test | Input | Expected |
|------|-------|----------|
| Empty animation | No layers | Valid Lottie |
| Single shape | Rectangle | Valid with shape layer |
| Animated | Keyframes | Valid with animation |
| Invalid version | "1.0" | Validation error |
| Out of bounds | width=20000 | Clamped to 16384 |
| Parent cycle | A→B→A | Validation error |
| Asset ref | Image layer | Asset in assets array |

---

*End of Specification 10*
