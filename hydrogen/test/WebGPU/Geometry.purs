-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // test // webgpu // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebGPU Geometry Generator Property Tests
-- |
-- | Verifies that procedural mesh generators produce correct vertex/index counts
-- | matching the formulas proven in `proofs/Hydrogen/Geometry/Primitives.lean`.
-- |
-- | ## Test Categories
-- |
-- | 1. **Formula Verification**: Count functions match Lean theorems exactly
-- | 2. **Generator Correctness**: Generated meshes match count formulas
-- | 3. **Invariant Preservation**: Triangle validity, normal unit length, UV bounds
-- | 4. **Edge Cases**: Minimum segments, maximum segments, degenerate cases
-- | 5. **Realistic Distributions**: Weighted toward common use cases
-- |
-- | ## Lean Proof References
-- |
-- | - Box: `BoxGeometry.vertexCount`, `BoxGeometry.indexCount`
-- | - Plane: `PlaneGeometry.vertexCount`, `PlaneGeometry.indexCount`
-- | - Sphere: `SphereGeometry.vertexCount`, `SphereGeometry.indexCount`
-- | - Cylinder: `CylinderGeometry.vertexCount`, `CylinderGeometry.indexCount`
-- |
-- | ## Scale Reference
-- |
-- | - **Micro scale**: 0.001-0.01 m — small details, jewelry
-- | - **Human scale**: 0.1-10 m — furniture, rooms, people
-- | - **Architectural scale**: 10-1000 m — buildings, structures
-- | - **Terrain scale**: 1000-100000 m — landscapes, terrain tiles

module Test.WebGPU.Geometry where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just))
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck ((<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec

import Hydrogen.GPU.WebGPU.Scene3D.Geometry
  ( MeshData
  , generateBox
  , generatePlane
  , generateSphere
  , generateCylinder
  , generateCone
  , generateTorus
  , generateRing
  , generateCircle
  , generateCapsule
  , planeVertexCount
  , planeIndexCount
  , boxVertexCount
  , boxIndexCount
  , sphereVertexCount
  , sphereIndexCount
  )
import Hydrogen.Math.Core (sqrt)
import Hydrogen.Schema.Dimension.Physical.SI (Meter, meter)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2, getX2, getY2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, getX3, getY3, getZ3)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // exports
-- ═══════════════════════════════════════════════════════════════════════════════

geometryTests :: Spec Unit
geometryTests = describe "WebGPU Geometry Generators" do
  formulaVerificationTests
  generatorCorrectnessTests
  invariantTests
  edgeCaseTests
  determinismTests
  additionalGeneratorTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a Number in the given range using integer subdivision.
-- | Uses ceiling for lower bound to ensure we never go below requested minimum.
genNumber :: Number -> Number -> Gen Number
genNumber lo hi = do
  -- Use ceiling for lower bound, floor for upper bound
  -- This ensures generated values are always within [lo, hi]
  let loI = ceilInt (lo * 1000.0)
  let hiI = floor (hi * 1000.0)
  -- Ensure loI <= hiI (in case of very small ranges)
  let actualLo = if loI > hiI then hiI else loI
  n <- chooseInt actualLo hiI
  pure (toNumber n / 1000.0)

-- | Ceiling for Int (rounds up)
ceilInt :: Number -> Int
ceilInt x = 
  let floored = floor x
  in if toNumber floored < x then floored + 1 else floored

-- | Generate positive Meter values with realistic distribution.
-- |
-- | Distribution covers:
-- | - Micro: 0.001-0.01 m (jewelry, small details)
-- | - Small: 0.01-0.1 m (handheld objects)
-- | - Human: 0.1-10 m (furniture, rooms)
-- | - Architectural: 10-1000 m (buildings)
-- | - Terrain: 1000-100000 m (landscapes)
genPositiveMeter :: Gen Meter
genPositiveMeter = frequency $ NEA.cons'
  (Tuple 5.0 (meter <$> genNumber 0.001 0.01))    -- Micro
  [ Tuple 15.0 (meter <$> genNumber 0.01 0.1)     -- Small
  , Tuple 40.0 (meter <$> genNumber 0.1 10.0)     -- Human (most common)
  , Tuple 25.0 (meter <$> genNumber 10.0 1000.0)  -- Architectural
  , Tuple 15.0 (meter <$> genNumber 1000.0 100000.0)  -- Terrain
  ]

-- | Generate segment counts with realistic distribution.
-- |
-- | Distribution covers:
-- | - Minimum: 1 (required for valid geometry)
-- | - Low detail: 4-8 (mobile/performance)
-- | - Medium detail: 16-32 (typical usage)
-- | - High detail: 64-128 (close-up/quality)
-- | - Edge case: Very high (stress testing)
genSegments :: Gen Int
genSegments = frequency $ NEA.cons'
  (Tuple 5.0 (pure 1))                            -- Minimum
  [ Tuple 15.0 (chooseInt 4 8)                    -- Low detail
  , Tuple 40.0 (chooseInt 16 32)                  -- Medium detail (most common)
  , Tuple 25.0 (chooseInt 64 128)                 -- High detail
  , Tuple 15.0 (chooseInt 1 256)                  -- Any valid
  ]

-- | Generate segments for spheres (minimum 3 for width, 2 for height).
genSphereWidthSegments :: Gen Int
genSphereWidthSegments = frequency $ NEA.cons'
  (Tuple 5.0 (pure 3))                            -- Minimum
  [ Tuple 20.0 (chooseInt 8 16)                   -- Low poly
  , Tuple 40.0 (chooseInt 24 48)                  -- Medium (most common)
  , Tuple 25.0 (chooseInt 64 128)                 -- High detail
  , Tuple 10.0 (chooseInt 3 256)                  -- Any valid
  ]

genSphereHeightSegments :: Gen Int
genSphereHeightSegments = frequency $ NEA.cons'
  (Tuple 5.0 (pure 2))                            -- Minimum
  [ Tuple 20.0 (chooseInt 4 8)                    -- Low poly
  , Tuple 40.0 (chooseInt 12 24)                  -- Medium (most common)
  , Tuple 25.0 (chooseInt 32 64)                  -- High detail
  , Tuple 10.0 (chooseInt 2 128)                  -- Any valid
  ]

-- | Generate radial segments (for cylinders, cones, circles).
genRadialSegments :: Gen Int
genRadialSegments = frequency $ NEA.cons'
  (Tuple 5.0 (pure 3))                            -- Minimum (triangle)
  [ Tuple 10.0 (chooseInt 4 8)                    -- Low poly
  , Tuple 40.0 (chooseInt 16 48)                  -- Medium (most common)
  , Tuple 30.0 (chooseInt 64 128)                 -- High detail (smooth circles)
  , Tuple 15.0 (chooseInt 3 256)                  -- Any valid
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // default params helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default sphere params with full sphere (phi 0-360, theta 0-180).
defaultSphereParams 
  :: { radius :: Meter, widthSegments :: Int, heightSegments :: Int
     , phiStart :: Degrees, phiLength :: Degrees
     , thetaStart :: Degrees, thetaLength :: Degrees }
defaultSphereParams =
  { radius: meter 1.0
  , widthSegments: 16
  , heightSegments: 8
  , phiStart: degrees 0.0
  , phiLength: degrees 360.0
  , thetaStart: degrees 0.0
  , thetaLength: degrees 180.0
  }

-- | Default cylinder params with full cylinder (theta 0-360).
defaultCylinderParams
  :: { radiusTop :: Meter, radiusBottom :: Meter, height :: Meter
     , radialSegments :: Int, heightSegments :: Int, openEnded :: Boolean
     , thetaStart :: Degrees, thetaLength :: Degrees }
defaultCylinderParams =
  { radiusTop: meter 1.0
  , radiusBottom: meter 1.0
  , height: meter 2.0
  , radialSegments: 16
  , heightSegments: 1
  , openEnded: false
  , thetaStart: degrees 0.0
  , thetaLength: degrees 360.0
  }

-- | Default cone params with full cone (theta 0-360).
defaultConeParams
  :: { radius :: Meter, height :: Meter
     , radialSegments :: Int, heightSegments :: Int, openEnded :: Boolean
     , thetaStart :: Degrees, thetaLength :: Degrees }
defaultConeParams =
  { radius: meter 1.0
  , height: meter 2.0
  , radialSegments: 16
  , heightSegments: 1
  , openEnded: false
  , thetaStart: degrees 0.0
  , thetaLength: degrees 360.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // formula verification tests
-- ═══════════════════════════════════════════════════════════════════════════════

formulaVerificationTests :: Spec Unit
formulaVerificationTests = describe "Formula Verification (Lean Proofs)" do
  
  describe "Box Geometry" do
    
    it "unit box: 24 vertices (Lean: BoxGeometry.unit_vertexCount)" do
      boxVertexCount 1 1 1 `shouldEqual` 24
    
    it "unit box: 36 indices (Lean: BoxGeometry.unit_indexCount)" do
      boxIndexCount 1 1 1 `shouldEqual` 36
    
    it "vertex count matches formula for any segments" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let expected = 
              2 * (wSegs + 1) * (hSegs + 1) +  -- Front/Back
              2 * (dSegs + 1) * (hSegs + 1) +  -- Left/Right
              2 * (wSegs + 1) * (dSegs + 1)    -- Top/Bottom
        pure $ boxVertexCount wSegs hSegs dSegs === expected
    
    it "index count matches formula for any segments" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let expected =
              2 * wSegs * hSegs * 6 +  -- Front/Back
              2 * dSegs * hSegs * 6 +  -- Left/Right
              2 * wSegs * dSegs * 6    -- Top/Bottom
        pure $ boxIndexCount wSegs hSegs dSegs === expected
  
  describe "Plane Geometry" do
    
    it "unit plane: 4 vertices (Lean: PlaneGeometry.unit_vertexCount)" do
      planeVertexCount 1 1 `shouldEqual` 4
    
    it "unit plane: 6 indices (Lean: PlaneGeometry.unit_indexCount)" do
      planeIndexCount 1 1 `shouldEqual` 6
    
    it "vertex count = (w+1) × (h+1) for any segments" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let expected = (wSegs + 1) * (hSegs + 1)
        pure $ planeVertexCount wSegs hSegs === expected
    
    it "index count = w × h × 6 for any segments" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let expected = wSegs * hSegs * 6
        pure $ planeIndexCount wSegs hSegs === expected
  
  describe "Sphere Geometry" do
    
    it "unit sphere (32×16): 561 vertices" do
      sphereVertexCount 32 16 `shouldEqual` 561
    
    it "low-poly sphere (16×8): 153 vertices" do
      sphereVertexCount 16 8 `shouldEqual` 153
    
    it "vertex count = (w+1) × (h+1) for any segments" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let expected = (wSegs + 1) * (hSegs + 1)
        pure $ sphereVertexCount wSegs hSegs === expected
    
    it "index count = w × h × 6 for any segments" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let expected = wSegs * hSegs * 6
        pure $ sphereIndexCount wSegs hSegs === expected

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // generator correctness tests
-- ═══════════════════════════════════════════════════════════════════════════════

generatorCorrectnessTests :: Spec Unit
generatorCorrectnessTests = describe "Generator Correctness" do
  
  describe "Box Generator" do
    
    it "generated vertex count matches formula" do
      Spec.quickCheck do
        width <- genPositiveMeter
        height <- genPositiveMeter
        depth <- genPositiveMeter
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox { width, height, depth
                               , widthSegments: wSegs
                               , heightSegments: hSegs
                               , depthSegments: dSegs }
        let expected = boxVertexCount wSegs hSegs dSegs
        pure $ Array.length mesh.positions == expected
    
    it "generated index count matches formula" do
      Spec.quickCheck do
        width <- genPositiveMeter
        height <- genPositiveMeter
        depth <- genPositiveMeter
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox { width, height, depth
                               , widthSegments: wSegs
                               , heightSegments: hSegs
                               , depthSegments: dSegs }
        let expected = boxIndexCount wSegs hSegs dSegs
        pure $ Array.length mesh.indices == expected
  
  describe "Plane Generator" do
    
    it "generated vertex count matches formula" do
      Spec.quickCheck do
        width <- genPositiveMeter
        height <- genPositiveMeter
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane { width, height
                                 , widthSegments: wSegs
                                 , heightSegments: hSegs }
        let expected = planeVertexCount wSegs hSegs
        pure $ Array.length mesh.positions === expected
    
    it "generated index count matches formula" do
      Spec.quickCheck do
        width <- genPositiveMeter
        height <- genPositiveMeter
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane { width, height
                                 , widthSegments: wSegs
                                 , heightSegments: hSegs }
        let expected = planeIndexCount wSegs hSegs
        pure $ Array.length mesh.indices === expected
  
  describe "Sphere Generator" do
    
    it "generated vertex count matches formula" do
      Spec.quickCheck do
        radius <- genPositiveMeter
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere 
              { radius, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let expected = sphereVertexCount wSegs hSegs
        pure $ Array.length mesh.positions === expected
    
    it "generated index count matches formula" do
      Spec.quickCheck do
        radius <- genPositiveMeter
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere 
              { radius, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let expected = sphereIndexCount wSegs hSegs
        pure $ Array.length mesh.indices === expected

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // invariant tests
-- ═══════════════════════════════════════════════════════════════════════════════

invariantTests :: Spec Unit
invariantTests = describe "Invariant Preservation" do
  
  describe "MeshData Structure Validity" do
    
    it "box MeshData is structurally valid" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh :: MeshData
            mesh = generateBox
              { width: meter 1.0, height: meter 1.0, depth: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs, depthSegments: dSegs }
        pure $ validateMeshData mesh
          <?> "Box MeshData must be structurally valid"
    
    it "sphere MeshData is structurally valid" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh :: MeshData
            mesh = generateSphere
              { radius: meter 1.0, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        pure $ validateMeshData mesh
          <?> "Sphere MeshData must be structurally valid"
    
    it "cylinder MeshData is structurally valid" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh :: MeshData
            mesh = generateCylinder
              { radiusTop: meter 1.0, radiusBottom: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        pure $ validateMeshData mesh
          <?> "Cylinder MeshData must be structurally valid"
    
    it "torus MeshData is structurally valid" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        tubSegs <- genRadialSegments
        let mesh :: MeshData
            mesh = generateTorus
              { radius: meter 1.0, tube: meter 0.3
              , radialSegments: radSegs, tubularSegments: tubSegs
              , arc: degrees 360.0 }
        pure $ validateMeshData mesh
          <?> "Torus MeshData must be structurally valid"
  
  describe "Triangle Validity (Lean: indexCount_div3)" do
    
    it "box index count is always divisible by 3" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        pure $ (boxIndexCount wSegs hSegs dSegs `mod` 3 == 0)
          <?> "Box indices must form complete triangles"
    
    it "plane index count is always divisible by 3" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        pure $ (planeIndexCount wSegs hSegs `mod` 3 == 0)
          <?> "Plane indices must form complete triangles"
    
    it "sphere index count is always divisible by 3" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        pure $ (sphereIndexCount wSegs hSegs `mod` 3 == 0)
          <?> "Sphere indices must form complete triangles"
    
    it "generated box indices divisible by 3" do
      Spec.quickCheck do
        width <- genPositiveMeter
        height <- genPositiveMeter
        depth <- genPositiveMeter
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox { width, height, depth
                               , widthSegments: wSegs
                               , heightSegments: hSegs
                               , depthSegments: dSegs }
        pure $ (Array.length mesh.indices `mod` 3 == 0)
          <?> "Generated box must have triangle-aligned indices"
    
    it "generated sphere indices divisible by 3" do
      Spec.quickCheck do
        radius <- genPositiveMeter
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere 
              { radius, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        pure $ (Array.length mesh.indices `mod` 3 == 0)
          <?> "Generated sphere must have triangle-aligned indices"
  
  describe "Index Range Validity (all indices < vertexCount)" do
    
    it "all box indices reference valid vertices" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox 
              { width: meter 1.0, height: meter 1.0, depth: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs, depthSegments: dSegs }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "All box indices must reference valid vertices"
    
    it "all plane indices reference valid vertices" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane
              { width: meter 1.0, height: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "All plane indices must reference valid vertices"
    
    it "all sphere indices reference valid vertices" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere
              { radius: meter 1.0, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "All sphere indices must reference valid vertices"
    
    it "all cylinder indices reference valid vertices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh = generateCylinder
              { radiusTop: meter 1.0, radiusBottom: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "All cylinder indices must reference valid vertices"
    
    it "all torus indices reference valid vertices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        tubSegs <- genRadialSegments
        let mesh = generateTorus
              { radius: meter 1.0, tube: meter 0.3
              , radialSegments: radSegs, tubularSegments: tubSegs
              , arc: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "All torus indices must reference valid vertices"
  
  describe "No Degenerate Triangles (no duplicate indices per triangle)" do
    
    it "box triangles have no duplicate indices" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox
              { width: meter 1.0, height: meter 1.0, depth: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs, depthSegments: dSegs }
        let valid = allTrianglesNonDegenerate mesh.indices
        pure $ valid <?> "Box triangles must not have duplicate indices"
    
    it "sphere triangles have no duplicate indices" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere
              { radius: meter 1.0, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let valid = allTrianglesNonDegenerate mesh.indices
        pure $ valid <?> "Sphere triangles must not have duplicate indices"
    
    it "plane triangles have no duplicate indices" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane
              { width: meter 1.0, height: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs }
        let valid = allTrianglesNonDegenerate mesh.indices
        pure $ valid <?> "Plane triangles must not have duplicate indices"
  
  describe "Normal Vector Validity (unit length)" do
    
    it "all box normals have unit length (property)" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox
              { width: meter 1.0, height: meter 1.0, depth: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs, depthSegments: dSegs }
        let allUnit = allNormalsUnit mesh.normals
        pure $ allUnit <?> "All box normals must have approximately unit length"
    
    it "all sphere normals have unit length (property)" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere
              { radius: meter 1.0, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let allUnit = allNormalsUnit mesh.normals
        pure $ allUnit <?> "All sphere normals must have approximately unit length"
    
    it "all plane normals have unit length (property)" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane
              { width: meter 1.0, height: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs }
        let allUnit = allNormalsUnit mesh.normals
        pure $ allUnit <?> "All plane normals must have approximately unit length"
    
    it "all cylinder normals have unit length (property)" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh = generateCylinder
              { radiusTop: meter 1.0, radiusBottom: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let allUnit = allNormalsUnit mesh.normals
        pure $ allUnit <?> "All cylinder normals must have approximately unit length"
    
    it "all torus normals have unit length (property)" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        tubSegs <- genRadialSegments
        let mesh = generateTorus
              { radius: meter 1.0, tube: meter 0.3
              , radialSegments: radSegs, tubularSegments: tubSegs
              , arc: degrees 360.0 }
        let allUnit = allNormalsUnit mesh.normals
        pure $ allUnit <?> "All torus normals must have approximately unit length"
  
  describe "UV Bounds (0 ≤ u,v ≤ 1)" do
    
    it "all box UVs are in [0, 1] range" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        dSegs <- genSegments
        let mesh = generateBox
              { width: meter 1.0, height: meter 1.0, depth: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs, depthSegments: dSegs }
        let valid = allUVsInRange mesh.uvs
        pure $ valid <?> "All box UVs must be in [0, 1] range"
    
    it "all sphere UVs are in [0, 1] range" do
      Spec.quickCheck do
        wSegs <- genSphereWidthSegments
        hSegs <- genSphereHeightSegments
        let mesh = generateSphere
              { radius: meter 1.0, widthSegments: wSegs, heightSegments: hSegs
              , phiStart: degrees 0.0, phiLength: degrees 360.0
              , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
        let valid = allUVsInRange mesh.uvs
        pure $ valid <?> "All sphere UVs must be in [0, 1] range"
    
    it "all plane UVs are in [0, 1] range" do
      Spec.quickCheck do
        wSegs <- genSegments
        hSegs <- genSegments
        let mesh = generatePlane
              { width: meter 1.0, height: meter 1.0
              , widthSegments: wSegs, heightSegments: hSegs }
        let valid = allUVsInRange mesh.uvs
        pure $ valid <?> "All plane UVs must be in [0, 1] range"
    
    it "all torus UVs are in [0, 1] range" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        tubSegs <- genRadialSegments
        let mesh = generateTorus
              { radius: meter 1.0, tube: meter 0.3
              , radialSegments: radSegs, tubularSegments: tubSegs
              , arc: degrees 360.0 }
        let valid = allUVsInRange mesh.uvs
        pure $ valid <?> "All torus UVs must be in [0, 1] range"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // edge case tests
-- ═══════════════════════════════════════════════════════════════════════════════

edgeCaseTests :: Spec Unit
edgeCaseTests = describe "Edge Cases" do
  
  describe "Minimum Segments" do
    
    it "box with 1×1×1 segments produces valid mesh" do
      let mesh = generateBox
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1 }
      Array.length mesh.positions `shouldEqual` 24
      Array.length mesh.indices `shouldEqual` 36
    
    it "plane with 1×1 segments produces valid mesh" do
      let mesh = generatePlane
            { width: meter 1.0, height: meter 1.0
            , widthSegments: 1, heightSegments: 1 }
      Array.length mesh.positions `shouldEqual` 4
      Array.length mesh.indices `shouldEqual` 6
    
    it "sphere with 3×2 segments produces valid mesh" do
      let mesh = generateSphere
            { radius: meter 1.0, widthSegments: 3, heightSegments: 2
            , phiStart: degrees 0.0, phiLength: degrees 360.0
            , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
      Array.length mesh.positions `shouldEqual` 12  -- (3+1) * (2+1)
      Array.length mesh.indices `shouldEqual` 36    -- 3 * 2 * 6
  
  describe "High Segment Counts" do
    
    it "box with 64×64×64 segments produces valid mesh" do
      let mesh = generateBox
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 64, heightSegments: 64, depthSegments: 64 }
      let expected = boxVertexCount 64 64 64
      Array.length mesh.positions `shouldEqual` expected
      (Array.length mesh.indices `mod` 3) `shouldEqual` 0
    
    it "sphere with 128×64 segments produces valid mesh" do
      let mesh = generateSphere
            { radius: meter 1.0, widthSegments: 128, heightSegments: 64
            , phiStart: degrees 0.0, phiLength: degrees 360.0
            , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
      let expected = sphereVertexCount 128 64
      Array.length mesh.positions `shouldEqual` expected
      (Array.length mesh.indices `mod` 3) `shouldEqual` 0
  
  describe "Extreme Dimensions" do
    
    it "very small box (1mm) produces valid mesh" do
      let mesh = generateBox
            { width: meter 0.001, height: meter 0.001, depth: meter 0.001
            , widthSegments: 1, heightSegments: 1, depthSegments: 1 }
      Array.length mesh.positions `shouldEqual` 24
    
    it "very large box (1km) produces valid mesh" do
      let mesh = generateBox
            { width: meter 1000.0, height: meter 1000.0, depth: meter 1000.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1 }
      Array.length mesh.positions `shouldEqual` 24
    
    it "very small sphere (1mm radius) produces valid mesh" do
      let mesh = generateSphere
            { radius: meter 0.001, widthSegments: 16, heightSegments: 8
            , phiStart: degrees 0.0, phiLength: degrees 360.0
            , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
      Array.length mesh.positions `shouldEqual` 153
    
    it "very large sphere (1km radius) produces valid mesh" do
      let mesh = generateSphere
            { radius: meter 1000.0, widthSegments: 16, heightSegments: 8
            , phiStart: degrees 0.0, phiLength: degrees 360.0
            , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
      Array.length mesh.positions `shouldEqual` 153

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // determinism tests
-- ═══════════════════════════════════════════════════════════════════════════════

determinismTests :: Spec Unit
determinismTests = describe "Determinism (same params → identical output)" do
  
  it "box generator is deterministic" do
    Spec.quickCheck do
      width <- genPositiveMeter
      height <- genPositiveMeter
      depth <- genPositiveMeter
      wSegs <- genSegments
      hSegs <- genSegments
      dSegs <- genSegments
      let params = { width, height, depth
                   , widthSegments: wSegs
                   , heightSegments: hSegs
                   , depthSegments: dSegs }
      let mesh1 = generateBox params
      let mesh2 = generateBox params
      pure $ (mesh1.positions == mesh2.positions &&
              mesh1.normals == mesh2.normals &&
              mesh1.uvs == mesh2.uvs &&
              mesh1.indices == mesh2.indices)
        <?> "Same box params must produce identical output"
  
  it "sphere generator is deterministic" do
    Spec.quickCheck do
      radius <- genPositiveMeter
      wSegs <- genSphereWidthSegments
      hSegs <- genSphereHeightSegments
      let params = { radius, widthSegments: wSegs, heightSegments: hSegs
                   , phiStart: degrees 0.0, phiLength: degrees 360.0
                   , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }
      let mesh1 = generateSphere params
      let mesh2 = generateSphere params
      pure $ (mesh1.positions == mesh2.positions &&
              mesh1.normals == mesh2.normals &&
              mesh1.uvs == mesh2.uvs &&
              mesh1.indices == mesh2.indices)
        <?> "Same sphere params must produce identical output"
  
  it "plane generator is deterministic" do
    Spec.quickCheck do
      width <- genPositiveMeter
      height <- genPositiveMeter
      wSegs <- genSegments
      hSegs <- genSegments
      let params = { width, height, widthSegments: wSegs, heightSegments: hSegs }
      let mesh1 = generatePlane params
      let mesh2 = generatePlane params
      pure $ (mesh1.positions == mesh2.positions &&
              mesh1.normals == mesh2.normals &&
              mesh1.uvs == mesh2.uvs &&
              mesh1.indices == mesh2.indices)
        <?> "Same plane params must produce identical output"
  
  it "cylinder generator is deterministic" do
    Spec.quickCheck do
      radiusTop <- genPositiveMeter
      radiusBottom <- genPositiveMeter
      height <- genPositiveMeter
      radSegs <- genRadialSegments
      hSegs <- genSegments
      let params = { radiusTop, radiusBottom, height
                   , radialSegments: radSegs, heightSegments: hSegs
                   , openEnded: false
                   , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
      let mesh1 = generateCylinder params
      let mesh2 = generateCylinder params
      pure $ (mesh1.positions == mesh2.positions &&
              mesh1.normals == mesh2.normals &&
              mesh1.uvs == mesh2.uvs &&
              mesh1.indices == mesh2.indices)
        <?> "Same cylinder params must produce identical output"
  
  it "torus generator is deterministic" do
    Spec.quickCheck do
      radius <- genPositiveMeter
      tube <- genPositiveMeter
      radSegs <- genRadialSegments
      tubSegs <- genRadialSegments
      let params = { radius, tube
                   , radialSegments: radSegs, tubularSegments: tubSegs
                   , arc: degrees 360.0 }
      let mesh1 = generateTorus params
      let mesh2 = generateTorus params
      pure $ (mesh1.positions == mesh2.positions &&
              mesh1.normals == mesh2.normals &&
              mesh1.uvs == mesh2.uvs &&
              mesh1.indices == mesh2.indices)
        <?> "Same torus params must produce identical output"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // additional generator tests
-- ═══════════════════════════════════════════════════════════════════════════════

additionalGeneratorTests :: Spec Unit
additionalGeneratorTests = describe "Additional Generators" do
  
  describe "Cylinder Generator" do
    
    it "cylinder with caps has valid indices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh = generateCylinder
              { radiusTop: meter 1.0, radiusBottom: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Cylinder must have valid, triangle-aligned indices"
    
    it "open cylinder (no caps) has valid indices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh = generateCylinder
              { radiusTop: meter 1.0, radiusBottom: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: true
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Open cylinder must have valid, triangle-aligned indices"
    
    it "tapered cylinder has valid indices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        radiusTop <- genPositiveMeter
        radiusBottom <- genPositiveMeter
        let mesh = generateCylinder
              { radiusTop, radiusBottom, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "Tapered cylinder must have valid indices"
  
  describe "Cone Generator" do
    
    it "cone has valid indices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        hSegs <- genSegments
        let mesh = generateCone
              { radius: meter 1.0, height: meter 2.0
              , radialSegments: radSegs, heightSegments: hSegs, openEnded: false
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        pure $ allValid <?> "Cone must have valid indices"
  
  describe "Circle Generator" do
    
    it "full circle has valid indices" do
      Spec.quickCheck do
        segs <- genRadialSegments
        let mesh = generateCircle
              { radius: meter 1.0, segments: segs
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Circle must have valid, triangle-aligned indices"
    
    it "partial circle (arc) has valid indices" do
      let mesh = generateCircle
            { radius: meter 1.0, segments: 16
            , thetaStart: degrees 0.0, thetaLength: degrees 270.0 }
      let vertCount = Array.length mesh.positions
      let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
      allValid `shouldEqual` true
  
  describe "Ring Generator" do
    
    it "ring has valid indices" do
      Spec.quickCheck do
        thetaSegs <- genRadialSegments
        phiSegs <- genSegments
        let mesh = generateRing
              { innerRadius: meter 0.5, outerRadius: meter 1.0
              , thetaSegments: thetaSegs, phiSegments: phiSegs
              , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Ring must have valid, triangle-aligned indices"
    
    it "ring normals are unit length" do
      let mesh = generateRing
            { innerRadius: meter 0.5, outerRadius: meter 1.0
            , thetaSegments: 16, phiSegments: 4
            , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }
      let allUnit = allNormalsUnit mesh.normals
      allUnit `shouldEqual` true
  
  describe "Torus Generator" do
    
    it "torus has valid indices" do
      Spec.quickCheck do
        radSegs <- genRadialSegments
        tubSegs <- genRadialSegments
        let mesh = generateTorus
              { radius: meter 1.0, tube: meter 0.3
              , radialSegments: radSegs, tubularSegments: tubSegs
              , arc: degrees 360.0 }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Torus must have valid, triangle-aligned indices"
    
    it "partial torus (arc) has valid indices" do
      let mesh = generateTorus
            { radius: meter 1.0, tube: meter 0.3
            , radialSegments: 16, tubularSegments: 24
            , arc: degrees 270.0 }
      let vertCount = Array.length mesh.positions
      let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
      allValid `shouldEqual` true
  
  describe "Capsule Generator" do
    
    it "capsule has valid indices" do
      Spec.quickCheck do
        capSegs <- genSegments
        radSegs <- genRadialSegments
        let mesh = generateCapsule
              { radius: meter 0.5, length: meter 2.0
              , capSegments: capSegs, radialSegments: radSegs }
        let vertCount = Array.length mesh.positions
        let allValid = all (\idx -> idx >= 0 && idx < vertCount) mesh.indices
        let triAligned = Array.length mesh.indices `mod` 3 == 0
        pure $ (allValid && triAligned)
          <?> "Capsule must have valid, triangle-aligned indices"
    
    it "capsule normals are unit length" do
      let mesh = generateCapsule
            { radius: meter 0.5, length: meter 2.0
            , capSegments: 8, radialSegments: 16 }
      let allUnit = allNormalsUnit mesh.normals
      allUnit `shouldEqual` true

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Validate mesh data structure completeness.
-- |
-- | A valid MeshData must have:
-- | - Equal counts for positions, normals, and uvs (vertex attributes aligned)
-- | - Index count divisible by 3 (triangles)
-- | - All indices in valid range
validateMeshData :: MeshData -> Boolean
validateMeshData mesh =
  let
    posCount = Array.length mesh.positions
    normCount = Array.length mesh.normals
    uvCount = Array.length mesh.uvs
    idxCount = Array.length mesh.indices
    attributesAligned = posCount == normCount && normCount == uvCount
    triangleAligned = idxCount `mod` 3 == 0
    indicesValid = all (\idx -> idx >= 0 && idx < posCount) mesh.indices
  in
    attributesAligned && triangleAligned && indicesValid

-- | Compute vector length.
vecLength :: Vec3 Number -> Number
vecLength v =
  let x = getX3 v
      y = getY3 v
      z = getZ3 v
  in sqrt (x * x + y * y + z * z)

-- | Check if all normals have approximately unit length (0.99 < |n| < 1.01).
allNormalsUnit :: Array (Vec3 Number) -> Boolean
allNormalsUnit normals =
  all (\n -> let len = vecLength n in len > 0.99 && len < 1.01) normals

-- | Check if all UVs are in [0, 1] range.
allUVsInRange :: Array (Vec2 Number) -> Boolean
allUVsInRange uvs =
  all (\uv -> 
    let u = getX2 uv
        v = getY2 uv
    in u >= 0.0 && u <= 1.0 && v >= 0.0 && v <= 1.0) uvs

-- | Check if all triangles have non-degenerate indices (no duplicates per triangle).
-- | Uses iterative chunking to avoid stack overflow on large meshes.
allTrianglesNonDegenerate :: Array Int -> Boolean
allTrianglesNonDegenerate indices =
  let
    len = Array.length indices
    -- Must be divisible by 3
    validLength = len `mod` 3 == 0
    -- Check each triangle by index, avoiding recursion
    checkTriangle :: Int -> Boolean
    checkTriangle i =
      case Array.index indices i, Array.index indices (i + 1), Array.index indices (i + 2) of
        Just a, Just b, Just c -> a /= b && b /= c && a /= c
        _, _, _ -> false
    -- Generate triangle start indices: 0, 3, 6, 9, ...
    triangleCount = len / 3
    triangleIndices = Array.range 0 (triangleCount - 1) <#> (_ * 3)
  in
    validLength && all checkTriangle triangleIndices
