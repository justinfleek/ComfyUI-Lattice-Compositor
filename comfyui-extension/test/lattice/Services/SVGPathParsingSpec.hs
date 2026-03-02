-- |
-- Test suite for Lattice.Services.SVGPathParsing
--

module Lattice.Services.SVGPathParsingSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.SVGPathParsing
import Lattice.Utils.ArrayUtils (safeArrayGet)
import Data.Text (Text)
import qualified Data.Text as T

-- Helper to safely get first element
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

spec :: TestTree
spec = testGroup "Lattice.Services.SVGPathParsing"
  [ testGroup "parsePathData - Basic Commands"
    [ testCase "parsePathData - MoveTo absolute" $ do
        let (points, closed) = parsePathData "M 10 20" 0
        length points @?= 1
        closed @?= False
        case safeHead points of
          Just p -> do
            controlPointX p @?= 10.0
            controlPointY p @?= 20.0
          Nothing -> fail "Expected at least one point"
    , testCase "parsePathData - MoveTo relative" $ do
        let (points, closed) = parsePathData "M 10 20 m 5 5" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 15.0
        controlPointY p2 @?= 25.0
    , testCase "parsePathData - LineTo absolute" $ do
        let (points, closed) = parsePathData "M 0 0 L 10 20" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 10.0
        controlPointY p2 @?= 20.0
    , testCase "parsePathData - LineTo relative" $ do
        let (points, closed) = parsePathData "M 10 10 l 5 5" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 15.0
        controlPointY p2 @?= 15.0
    , testCase "parsePathData - Horizontal line absolute" $ do
        let (points, closed) = parsePathData "M 0 0 H 10" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 10.0
        controlPointY p2 @?= 0.0
    , testCase "parsePathData - Horizontal line relative" $ do
        let (points, closed) = parsePathData "M 10 0 h 5" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 15.0
        controlPointY p2 @?= 0.0
    , testCase "parsePathData - Vertical line absolute" $ do
        let (points, closed) = parsePathData "M 0 0 V 10" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 0.0
        controlPointY p2 @?= 10.0
    , testCase "parsePathData - Vertical line relative" $ do
        let (points, closed) = parsePathData "M 0 10 v 5" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 0.0
        controlPointY p2 @?= 15.0
    , testCase "parsePathData - ClosePath" $ do
        let (points, closed) = parsePathData "M 0 0 L 10 10 Z" 0
        closed @?= True
        length points @?= 2
    , testCase "parsePathData - ClosePath lowercase" $ do
        let (points, closed) = parsePathData "M 0 0 L 10 10 z" 0
        closed @?= True
    ]
  , testGroup "parsePathData - Bezier Curves"
    [ testCase "parsePathData - Cubic bezier absolute" $ do
        let (points, closed) = parsePathData "M 0 0 C 10 10 20 10 30 0" 0
        length points @?= 2
        case safeHead points of
          Just p1 -> do
            let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
            -- First point should have outHandle
            controlPointOutHandle p1 @?= Just (ControlPointHandle 10.0 10.0)
            -- Second point should have inHandle
            controlPointInHandle p2 @?= Just (ControlPointHandle 20.0 10.0)
            controlPointX p2 @?= 30.0
            controlPointY p2 @?= 0.0
          Nothing -> fail "Expected at least one point"
    , testCase "parsePathData - Cubic bezier relative" $ do
        let (points, closed) = parsePathData "M 10 10 c 5 5 10 5 15 0" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 25.0
        controlPointY p2 @?= 10.0
    , testCase "parsePathData - Smooth cubic bezier" $ do
        let (points, closed) = parsePathData "M 0 0 C 10 10 20 10 30 0 S 40 10 50 0" 0
        length points @?= 3
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        let p3 = safeArrayGet points 2 (error "Test failed: expected point at index 2")
        -- p2 should have both handles
        controlPointInHandle p2 @?= Just (ControlPointHandle 20.0 10.0)
        controlPointOutHandle p2 @?= Just (ControlPointHandle 40.0 10.0)
        -- p3 should have inHandle (reflected from p2's outHandle)
        controlPointInHandle p3 @?= Just (ControlPointHandle 40.0 10.0)
    , testCase "parsePathData - Quadratic bezier" $ do
        let (points, closed) = parsePathData "M 0 0 Q 10 10 20 0" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        -- Quadratic should be converted to cubic
        controlPointInHandle p2 @?= Just (ControlPointHandle 13.333333333333334 6.666666666666667)
    , testCase "parsePathData - Smooth quadratic bezier" $ do
        let (points, closed) = parsePathData "M 0 0 Q 10 10 20 0 T 40 0" 0
        length points @?= 3
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        let p3 = safeArrayGet points 2 (error "Test failed: expected point at index 2")
        -- p3 should have reflected control point
        controlPointX p3 @?= 40.0
        controlPointY p3 @?= 0.0
    ]
  , testGroup "parsePathData - Arc Commands"
    [ testCase "parsePathData - Arc command (approximated as line)" $ do
        let (points, closed) = parsePathData "M 0 0 A 5 5 0 0 1 10 0" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        -- Arc should be approximated as line to endpoint
        controlPointX p2 @?= 10.0
        controlPointY p2 @?= 0.0
    ]
  , testGroup "parsePathData - Edge Cases"
    [ testCase "parsePathData - Empty path" $ do
        let (points, closed) = parsePathData "" 0
        length points @?= 0
        closed @?= False
    , testCase "parsePathData - Whitespace only" $ do
        let (points, closed) = parsePathData "   " 0
        length points @?= 0
        closed @?= False
    , testCase "parsePathData - Multiple consecutive commands" $ do
        let (points, closed) = parsePathData "M 0 0 L 10 10 L 20 20" 0
        length points @?= 3
    , testCase "parsePathData - Commands without spaces" $ do
        let (points, closed) = parsePathData "M0,0L10,10" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 10.0
        controlPointY p2 @?= 10.0
    , testCase "parsePathData - Negative coordinates" $ do
        let (points, closed) = parsePathData "M -10 -20 L -5 -10" 0
        length points @?= 2
        case safeHead points of
          Just p1 -> do
            let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
            controlPointX p1 @?= -10.0
            controlPointY p1 @?= -20.0
            controlPointX p2 @?= -5.0
            controlPointY p2 @?= -10.0
          Nothing -> fail "Expected at least one point"
    , testCase "parsePathData - Decimal coordinates" $ do
        let (points, closed) = parsePathData "M 10.5 20.75 L 15.25 30.5" 0
        length points @?= 2
        let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointX p2 @?= 15.25
        controlPointY p2 @?= 30.5
    , testCase "parsePathData - Path index preserved" $ do
        let (points1, _) = parsePathData "M 0 0" 0
        let (points2, _) = parsePathData "M 0 0" 1
        case (safeHead points1, safeHead points2) of
          (Just p1, Just p2) -> do
            controlPointId p1 @?= T.pack "cp_0_0"
            controlPointId p2 @?= T.pack "cp_1_0"
          _ -> fail "Expected points in both paths"
    ]
  , testGroup "parseSVGToPaths"
    [ testCase "parseSVGToPaths - Simple path element" $ do
        let svg = T.pack "<svg><path d=\"M 0 0 L 10 10\" fill=\"red\" stroke=\"blue\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 1
        case safeHead paths of
          Just path -> do
            parsedPathFill path @?= T.pack "red"
            parsedPathStroke path @?= T.pack "blue"
            length (parsedPathControlPoints path) @?= 2
          Nothing -> fail "Expected at least one path"
    , testCase "parseSVGToPaths - Multiple path elements" $ do
        let svg = T.pack "<svg><path d=\"M 0 0 L 10 10\"/><path d=\"M 20 20 L 30 30\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 2
    , testCase "parseSVGToPaths - Path with single quotes" $ do
        let svg = T.pack "<svg><path d='M 0 0 L 10 10' fill='red'/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 1
        case safeHead paths of
          Just path -> parsedPathFill path @?= T.pack "red"
          Nothing -> fail "Expected at least one path"
    , testCase "parseSVGToPaths - Path without fill/stroke" $ do
        let svg = T.pack "<svg><path d=\"M 0 0 L 10 10\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 1
        case safeHead paths of
          Just path -> do
            parsedPathFill path @?= T.pack ""
            parsedPathStroke path @?= T.pack ""
          Nothing -> fail "Expected at least one path"
    , testCase "parseSVGToPaths - Invisible path (fill=none)" $ do
        let svg = T.pack "<svg><path d=\"M 0 0 L 10 10\" fill=\"none\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        -- Paths with fill="none" and no stroke should be filtered out
        length paths @?= 0
    , testCase "parseSVGToPaths - Visible path with stroke" $ do
        let svg = T.pack "<svg><path d=\"M 0 0 L 10 10\" fill=\"none\" stroke=\"blue\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        -- Paths with stroke should be included even if fill="none"
        length paths @?= 1
    , testCase "parseSVGToPaths - Path IDs assigned correctly" $ do
        let svg = T.pack "<svg><path d=\"M 0 0\"/><path d=\"M 10 10\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 2
        case safeHead paths of
          Just path1 -> do
            let path2 = safeArrayGet paths 1 (error "Test failed: expected path at index 1")
            parsedPathId path1 @?= T.pack "path_0"
            parsedPathId path2 @?= T.pack "path_1"
          Nothing -> fail "Expected at least one path"
    , testCase "parseSVGToPaths - Empty SVG" $ do
        let svg = T.pack "<svg></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 0
    , testCase "parseSVGToPaths - No path elements" $ do
        let svg = T.pack "<svg><rect x=\"0\" y=\"0\" width=\"10\" height=\"10\"/></svg>"
        let paths = parseSVGToPaths svg 100 100
        length paths @?= 0
    ]
  , testGroup "ControlPoint Properties"
    [ testCase "ControlPoint - Corner point by default" $ do
        let (points, _) = parsePathData "M 0 0 L 10 10" 0
        let p = safeArrayGet points 1 (error "Test failed: expected point at index 1")
        controlPointType p @?= CornerPoint
    , testCase "ControlPoint - Smooth point with handles" $ do
        let (points, _) = parsePathData "M 0 0 C 5 5 10 5 15 0" 0
        case safeHead points of
          Just p1 -> do
            let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
            -- Point with both handles should be smooth
            controlPointType p2 @?= SmoothPoint
          Nothing -> fail "Expected at least one point"
    , testCase "ControlPoint - Handles set correctly" $ do
        let (points, _) = parsePathData "M 0 0 C 10 10 20 10 30 0" 0
        case safeHead points of
          Just p1 -> do
            let p2 = safeArrayGet points 1 (error "Test failed: expected point at index 1")
            controlPointOutHandle p1 @?= Just (ControlPointHandle 10.0 10.0)
            controlPointInHandle p2 @?= Just (ControlPointHandle 20.0 10.0)
          Nothing -> fail "Expected at least one point"
    ]
  ]
