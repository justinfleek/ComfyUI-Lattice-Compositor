-- |
-- Test suite for Lattice.Services.PathMorphing
--

module Lattice.Services.PathMorphingSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.PathMorphing
import Lattice.Utils.NumericSafety (clamp01)

-- Helper to create test points
point :: Double -> Double -> Point2D
point x y = Point2D x y

-- Helper to create test vertices
vertex :: Point2D -> Point2D -> Point2D -> BezierVertex
vertex p inH outH = BezierVertex p inH outH

-- Helper to create test paths
path :: [BezierVertex] -> Bool -> BezierPath
path verts closed = BezierPath verts closed

spec :: TestTree
spec = testGroup "Lattice.Services.PathMorphing"
  [ testGroup "distance"
    [ testCase "distance - same point" $
        distance (point 0 0) (point 0 0) @?= 0.0
    , testCase "distance - horizontal" $
        distance (point 0 0) (point 3 0) @?= 3.0
    , testCase "distance - vertical" $
        distance (point 0 0) (point 0 4) @?= 4.0
    , testCase "distance - diagonal" $
        distance (point 0 0) (point 3 4) @?= 5.0  -- 3-4-5 triangle
    ]
  , testGroup "lerpPoint"
    [ testCase "lerpPoint - t=0" $
        lerpPoint (point 0 0) (point 10 10) 0.0 @?= point 0 0
    , testCase "lerpPoint - t=1" $
        lerpPoint (point 0 0) (point 10 10) 1.0 @?= point 10 10
    , testCase "lerpPoint - t=0.5" $
        lerpPoint (point 0 0) (point 10 10) 0.5 @?= point 5 5
    , testCase "lerpPoint - t=0.25" $
        lerpPoint (point 0 0) (point 8 4) 0.25 @?= point 2 1
    ]
  , testGroup "addPoints"
    [ testCase "addPoints - basic" $
        addPoints (point 1 2) (point 3 4) @?= point 4 6
    , testCase "addPoints - negative" $
        addPoints (point (-1) (-2)) (point 3 4) @?= point 2 2
    ]
  , testGroup "subtractPoints"
    [ testCase "subtractPoints - basic" $
        subtractPoints (point 5 6) (point 2 3) @?= point 3 3
    , testCase "subtractPoints - negative result" $
        subtractPoints (point 1 2) (point 3 4) @?= point (-2) (-2)
    ]
  , testGroup "scalePoint"
    [ testCase "scalePoint - scale by 2" $
        scalePoint (point 3 4) 2.0 @?= point 6 8
    , testCase "scalePoint - scale by 0" $
        scalePoint (point 3 4) 0.0 @?= point 0 0
    , testCase "scalePoint - scale by 0.5" $
        scalePoint (point 4 6) 0.5 @?= point 2 3
    ]
  , testGroup "cubicBezierPoint"
    [ testCase "cubicBezierPoint - t=0" $
        cubicBezierPoint (point 0 0) (point 1 1) (point 2 2) (point 3 3) 0.0 @?= point 0 0
    , testCase "cubicBezierPoint - t=1" $
        cubicBezierPoint (point 0 0) (point 1 1) (point 2 2) (point 3 3) 1.0 @?= point 3 3
    , testCase "cubicBezierPoint - t=0.5" $ do
        let result = cubicBezierPoint (point 0 0) (point 0 1) (point 1 1) (point 1 0) 0.5
        -- At t=0.5, should be approximately (0.5, 0.75) for this curve
        point2DX result @?= 0.5
        point2DY result @?= 0.75
    ]
  , testGroup "morphPaths"
    [ testCase "morphPaths - t=0 returns source" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] False
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] False
            result = morphPaths source target 0.0
        bezierPathVertices result @?= bezierPathVertices source
    , testCase "morphPaths - t=1 returns target" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] False
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] False
            result = morphPaths source target 1.0
        bezierPathVertices result @?= bezierPathVertices target
    , testCase "morphPaths - t=0.5 interpolates" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] False
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] False
            result = morphPaths source target 0.5
            vert = head (bezierPathVertices result)
        point2DX (bezierVertexPoint vert) @?= 5.0
        point2DY (bezierVertexPoint vert) @?= 5.0
    , testCase "morphPaths - multiple vertices" $ do
        let source = path
              [ vertex (point 0 0) (point 0 0) (point 0 0)
              , vertex (point 5 0) (point 5 0) (point 5 0)
              ] False
            target = path
              [ vertex (point 0 10) (point 0 10) (point 0 10)
              , vertex (point 5 10) (point 5 10) (point 5 10)
              ] False
            result = morphPaths source target 0.5
            verts = bezierPathVertices result
        length verts @?= 2
        point2DY (bezierVertexPoint (head verts)) @?= 5.0
        point2DY (bezierVertexPoint (verts !! 1)) @?= 5.0
    , testCase "morphPaths - preserves closed flag" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] True
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] True
            result = morphPaths source target 0.5
        bezierPathClosed result @?= True
    , testCase "morphPaths - handles mismatched vertex counts" $ do
        let source = path
              [ vertex (point 0 0) (point 0 0) (point 0 0)
              , vertex (point 5 0) (point 5 0) (point 5 0)
              ] False
            target = path [vertex (point 0 10) (point 0 10) (point 0 10)] False
            result = morphPaths source target 0.5
        -- Should use minimum count
        length (bezierPathVertices result) @?= 1
    , testCase "morphPaths - clamps t < 0" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] False
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] False
            result = morphPaths source target (-1.0)
        bezierPathVertices result @?= bezierPathVertices source
    , testCase "morphPaths - clamps t > 1" $ do
        let source = path [vertex (point 0 0) (point 0 0) (point 0 0)] False
            target = path [vertex (point 10 10) (point 10 10) (point 10 10)] False
            result = morphPaths source target 2.0
        bezierPathVertices result @?= bezierPathVertices target
    ]
  ]
