{-|
Module      : Main
Description : Criterion benchmarks for performance-critical Lattice services
Copyright   : (c) Lattice, 2026
License     : MIT

Benchmarks for:
- Gaussian blur kernel generation
- Delaunay triangulation
- Simplex noise generation
- Mat4 transforms

Run: cabal bench lattice-bench
-}

module Main where

import Criterion.Main
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word32)

import Lattice.Services.Blur.Gaussian
import Lattice.Services.Mesh.Delaunay
import Lattice.Services.Noise.SimplexNoise
import Lattice.Services.Math3D.Mat4
import Lattice.Services.Math3D.Vec3 (Vec3(..))

main :: IO ()
main = defaultMain
  [ bgroup "Gaussian"
      [ bench "kernel-5" $ nf generateKernel1D 5
      , bench "kernel-15" $ nf generateKernel1D 15
      , bench "kernel-31" $ nf generateKernel1D 31
      , bench "weight-single" $ nf (\x -> gaussianWeight x 2.5) 1.5
      , bench "sigma-from-radius-10" $ nf sigmaFromRadius 10
      ]
  , bgroup "Delaunay"
      [ bench "triangulate-10pts" $ whnf delaunayTriangulate testPoints10
      , bench "triangulate-50pts" $ whnf delaunayTriangulate testPoints50
      , bench "triangulate-100pts" $ whnf delaunayTriangulate testPoints100
      , bench "circumcircle-test" $ nf testCircumcircle ()
      ]
  , bgroup "SimplexNoise"
      [ bench "single-sample" $ nf (\_ -> simplexNoise2D 1.5 2.5 42) ()
      , bench "fbm-4-octaves" $ nf (\_ -> fbm 1.5 2.5 42 4 0.5 2.0) ()
      , bench "turbulence-4" $ nf (\_ -> turbulence 1.5 2.5 42 4 0.5 2.0) ()
      , bench "ridge-4" $ nf (\_ -> ridgeNoise 1.5 2.5 42 4 0.5 2.0 0.8) ()
      , bench "noise-field-32x32" $ nf generateNoiseField32 42
      ]
  , bgroup "Mat4"
      [ bench "identity" $ whnf (const identity) ()
      , bench "multiply" $ whnf (\_ -> multiply testMat1 testMat2) ()
      , bench "translate" $ whnf (\_ -> translate (Vec3 1.0 2.0 3.0)) ()
      , bench "rotateX" $ whnf rotateX 0.5
      , bench "rotateY" $ whnf rotateY 0.5
      , bench "rotateZ" $ whnf rotateZ 0.5
      , bench "scaleMat" $ whnf (\_ -> scaleMat (Vec3 2.0 3.0 4.0)) ()
      , bench "chain-transforms" $ whnf (\_ -> chainedTransform) ()
      ]
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Test Data
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate test points in a grid pattern
testPoints10 :: Vector Point2D
testPoints10 = V.fromList
  [ Point2D (fromIntegral x * 10.0) (fromIntegral y * 10.0)
  | x <- [0..2 :: Int]
  , y <- [0..2 :: Int]
  ] <> V.singleton (Point2D 15.0 15.0)

testPoints50 :: Vector Point2D
testPoints50 = V.fromList
  [ Point2D (fromIntegral x * 10.0 + jitter x y) (fromIntegral y * 10.0 + jitter y x)
  | x <- [0..6 :: Int]
  , y <- [0..6 :: Int]
  ]
  where
    jitter a b = sin (fromIntegral a * 0.7 + fromIntegral b * 0.3) * 2.0

testPoints100 :: Vector Point2D
testPoints100 = V.fromList
  [ Point2D (fromIntegral x * 10.0 + jitter x y) (fromIntegral y * 10.0 + jitter y x)
  | x <- [0..9 :: Int]
  , y <- [0..9 :: Int]
  ]
  where
    jitter a b = sin (fromIntegral a * 0.7 + fromIntegral b * 0.3) * 2.0

-- | Test circumcircle containment
testCircumcircle :: () -> Bool
testCircumcircle () =
  let a = Point2D 0 0
      b = Point2D 10 0
      c = Point2D 5 10
      pt = Point2D 5 3
  in isPointInCircumcircle pt a b c

-- | Generate a 32x32 noise field
generateNoiseField32 :: Word32 -> Vector Double
generateNoiseField32 seed = V.generate (32 * 32) $ \i ->
  let x = fromIntegral (i `mod` 32) * 0.1
      y = fromIntegral (i `div` 32) * 0.1
  in simplexNoise2D x y seed

-- | Test matrices for multiplication
testMat1 :: Mat4
testMat1 = translate (Vec3 1.0 2.0 3.0)

testMat2 :: Mat4
testMat2 = rotateY 0.5

-- | Chained transform for realistic usage
chainedTransform :: Mat4
chainedTransform =
  let m1 = translate (Vec3 100.0 200.0 0.0)
      m2 = multiply (rotateZ 0.785) m1
      m3 = multiply (scaleMat (Vec3 2.0 2.0 1.0)) m2
  in m3
