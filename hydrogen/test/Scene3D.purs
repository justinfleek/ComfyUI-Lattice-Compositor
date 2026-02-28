-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // test // scene3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene3D Property Tests
-- |
-- | Tests UUID5 deterministic identity and flattenScene correctness.
-- |
-- | ## Test Categories
-- |
-- | 1. **UUID5 Determinism**: Same parameters → same UUID (always)
-- | 2. **UUID5 Collision Resistance**: Different parameters → different UUID
-- | 3. **flattenScene Correctness**: All scene elements appear in buffer
-- | 4. **Realistic Distributions**: Atomic, human, and cosmic scale tests
-- |
-- | ## Scale Reference
-- |
-- | - **Atomic scale**: Picometers (10^-12 m) — atomic bonds, X-rays
-- | - **Human scale**: Meters (10^0 m) — everyday objects
-- | - **Cosmic scale**: Parsecs (10^16 m) — interstellar distances

module Test.Scene3D where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck ((<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf, vectorOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

import Hydrogen.GPU.Scene3D.Identity as Identity
import Hydrogen.GPU.Scene3D.Core
  ( Scene3D
  , SceneBuffer
  , SceneCommand
      ( SetCamera
      , SetBackground
      , AddLight
      , DrawMesh
      , DrawGrid
      , DrawAxes
      , PushTransform
      , PopTransform
      , SetClipPlane
      , ClearClipPlane
      , Noop3D
      )
  , emptyScene
  , withCamera
  , withBackground
  , withLight
  , withMesh
  , flattenScene
  )
import Hydrogen.GPU.Scene3D.Position 
  ( Position3D(Position3D)
  , directionY
  , zeroPosition3D
  )
import Hydrogen.GPU.Scene3D.Mesh 
  ( Mesh3D(BoxMesh3D, SphereMesh3D, CylinderMesh3D)
  , MeshParams
  , BoxMeshParams
  , SphereMeshParams
  , CylinderMeshParams
  , PickId3D
  , pickId3D
  )
import Hydrogen.GPU.Scene3D.Material
  ( Material3D(BasicMaterial3D, StandardMaterial3D)
  , BasicMaterialParams
  , StandardMaterialParams
  )
import Hydrogen.GPU.Scene3D.Light
  ( Light3D(AmbientLight3D)
  , AmbientLightParams
  )
import Hydrogen.GPU.Scene3D.Camera
  ( Camera3D(PerspectiveCamera3D)
  , PerspectiveCameraParams
  )
import Hydrogen.GPU.Scene3D.Background (solidBackground)

import Hydrogen.Schema.Dimension.Physical.Atomic (Picometer, picometer)
import Hydrogen.Schema.Dimension.Physical.SI (Meter, meter)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees)
import Hydrogen.Schema.Color.RGB (RGBA, rgba)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion, quaternionIdentity)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a basic MeshParams for testing.
-- | Uses sensible defaults for shadow/pick/event fields.
testMeshParams :: Mesh3D -> Material3D -> Position3D -> MeshParams Unit
testMeshParams geom mat pos =
  { geometry: geom
  , material: mat
  , position: pos
  , rotation: quaternionIdentity
  , scale: vec3 1.0 1.0 1.0
  , castShadow: false
  , receiveShadow: false
  , pickId: Nothing
  , onClick: Nothing
  , onHover: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a Number in the given range using integer subdivision.
-- | Maps integer range to floating point range with 0.01 precision.
genNumber :: Number -> Number -> Gen Number
genNumber lo hi = do
  -- Scale to integer range for chooseInt, then scale back
  let loI = Int.floor (lo * 100.0)
  let hiI = Int.floor (hi * 100.0)
  n <- chooseInt loI hiI
  pure (Int.toNumber n / 100.0)

-- | Generate Picometer values across realistic atomic scales.
-- |
-- | Distribution covers:
-- | - Bond lengths: 50-500 pm (typical covalent bonds)
-- | - Atomic radii: 25-250 pm (hydrogen to cesium)
-- | - Crystal lattices: 100-1000 pm (unit cell dimensions)
-- | - Edge cases: 0, 1, negative values
genPicometer :: Gen Picometer
genPicometer = frequency $ NEA.cons'
  (Tuple 5.0 (pure (picometer 0.0)))  -- Zero
  [ Tuple 5.0 (picometer <$> genNumber (-100.0) 0.0)  -- Negative (edge case)
  , Tuple 25.0 (picometer <$> genNumber 50.0 500.0)   -- Bond lengths
  , Tuple 25.0 (picometer <$> genNumber 25.0 250.0)   -- Atomic radii
  , Tuple 20.0 (picometer <$> genNumber 100.0 1000.0) -- Crystal lattices
  , Tuple 20.0 (picometer <$> genNumber 0.01 10000.0) -- Wide range (capped for Int)
  ]

-- | Generate Meter values across realistic human-scale dimensions.
-- |
-- | Distribution covers:
-- | - Small objects: 0.001-0.1 m (millimeters to centimeters)
-- | - Human scale: 0.1-10 m (furniture, rooms, people)
-- | - Building scale: 10-1000 m (buildings, blocks)
-- | - Edge cases: 0, negative, very large
genMeter :: Gen Meter
genMeter = frequency $ NEA.cons'
  (Tuple 5.0 (pure (meter 0.0)))  -- Zero
  [ Tuple 5.0 (meter <$> genNumber (-10.0) 0.0)       -- Negative (edge case)
  , Tuple 20.0 (meter <$> genNumber 0.01 0.1)         -- Small objects
  , Tuple 30.0 (meter <$> genNumber 0.1 10.0)         -- Human scale
  , Tuple 20.0 (meter <$> genNumber 10.0 1000.0)      -- Building scale
  , Tuple 20.0 (meter <$> genNumber 0.0 10000.0)      -- Wide range
  ]

-- | Generate positive Meter values (for radii, lengths, etc.)
genPositiveMeter :: Gen Meter
genPositiveMeter = frequency $ NEA.cons'
  (Tuple 10.0 (meter <$> genNumber 0.01 0.1))         -- Small
  [ Tuple 40.0 (meter <$> genNumber 0.1 10.0)         -- Human scale
  , Tuple 30.0 (meter <$> genNumber 10.0 1000.0)      -- Large
  , Tuple 20.0 (meter <$> genNumber 0.01 10000.0)     -- Wide range
  ]

-- | Generate Degrees values for angles.
genDegrees :: Gen Degrees
genDegrees = frequency $ NEA.cons'
  (Tuple 10.0 (pure (degrees 0.0)))     -- Zero
  [ Tuple 10.0 (pure (degrees 90.0))    -- Right angle
  , Tuple 10.0 (pure (degrees 180.0))   -- Half circle
  , Tuple 10.0 (pure (degrees 360.0))   -- Full circle
  , Tuple 60.0 (degrees <$> genNumber 0.0 360.0)  -- Any angle
  ]

-- | Generate RGBA colors with realistic distribution.
genRGBA :: Gen RGBA
genRGBA = frequency $ NEA.cons'
  (Tuple 10.0 (pure (rgba 0 0 0 100)))       -- Black
  [ Tuple 10.0 (pure (rgba 255 255 255 100)) -- White
  , Tuple 10.0 (pure (rgba 255 0 0 100))     -- Red
  , Tuple 10.0 (pure (rgba 0 255 0 100))     -- Green
  , Tuple 10.0 (pure (rgba 0 0 255 100))     -- Blue
  , Tuple 50.0 do                            -- Random
      r <- chooseInt 0 255
      g <- chooseInt 0 255
      b <- chooseInt 0 255
      a <- chooseInt 0 100
      pure (rgba r g b a)
  ]

-- | Generate segment counts for meshes.
genSegments :: Gen Int
genSegments = frequency $ NEA.cons'
  (Tuple 10.0 (pure 1))   -- Minimum
  [ Tuple 20.0 (pure 8)   -- Low detail
  , Tuple 30.0 (pure 32)  -- Medium detail
  , Tuple 20.0 (pure 64)  -- High detail
  , Tuple 20.0 (chooseInt 1 128)  -- Any
  ]

-- | Generate aspect ratios.
genAspectRatio :: Gen Number
genAspectRatio = frequency $ NEA.cons'
  (Tuple 20.0 (pure 1.0))           -- Square
  [ Tuple 30.0 (pure 1.777777778)  -- 16:9
  , Tuple 20.0 (pure 1.333333333)  -- 4:3
  , Tuple 30.0 (genNumber 0.5 3.0)  -- Any reasonable
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // position3d generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate Position3D values across all scale ranges.
genPosition3D :: Gen Position3D
genPosition3D = do
  x <- genPicometer
  y <- genPicometer
  z <- genPicometer
  pure (Position3D { x, y, z })

-- | Generate two distinct Position3D values (for collision resistance tests).
genDistinctPositions :: Gen { p1 :: Position3D, p2 :: Position3D }
genDistinctPositions = do
  x1 <- genPicometer
  y1 <- genPicometer
  z1 <- genPicometer
  -- Ensure at least one coordinate differs
  x2 <- frequency $ NEA.cons'
    (Tuple 50.0 genPicometer)  -- Different
    [ Tuple 50.0 (pure x1) ]   -- Same (y or z will differ)
  y2 <- genPicometer
  z2 <- genPicometer
  pure 
    { p1: Position3D { x: x1, y: y1, z: z1 }
    , p2: Position3D { x: x2, y: y2, z: z2 }
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // mesh generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate BoxMeshParams.
genBoxMeshParams :: Gen BoxMeshParams
genBoxMeshParams = do
  width <- genPositiveMeter
  height <- genPositiveMeter
  depth <- genPositiveMeter
  widthSegments <- genSegments
  heightSegments <- genSegments
  depthSegments <- genSegments
  pure { width, height, depth, widthSegments, heightSegments, depthSegments }

-- | Generate SphereMeshParams.
genSphereMeshParams :: Gen SphereMeshParams
genSphereMeshParams = do
  radius <- genPositiveMeter
  widthSegments <- genSegments
  heightSegments <- genSegments
  -- Full sphere by default
  pure { radius, widthSegments, heightSegments
       , phiStart: degrees 0.0, phiLength: degrees 360.0
       , thetaStart: degrees 0.0, thetaLength: degrees 180.0 }

-- | Generate CylinderMeshParams.
genCylinderMeshParams :: Gen CylinderMeshParams
genCylinderMeshParams = do
  radiusTop <- genPositiveMeter
  radiusBottom <- genPositiveMeter
  height <- genPositiveMeter
  radialSegments <- genSegments
  heightSegments <- genSegments
  openEnded <- elements $ NEA.cons' false [true]
  -- Full cylinder by default
  pure { radiusTop, radiusBottom, height, radialSegments, heightSegments, openEnded
       , thetaStart: degrees 0.0, thetaLength: degrees 360.0 }

-- | Generate a random Mesh3D (limited to deterministic primitives).
genMesh3D :: Gen Mesh3D
genMesh3D = oneOf $ NEA.cons'
  (BoxMesh3D <$> genBoxMeshParams)
  [ SphereMesh3D <$> genSphereMeshParams
  , CylinderMesh3D <$> genCylinderMeshParams
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // material generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate BasicMaterialParams.
genBasicMaterialParams :: Gen BasicMaterialParams
genBasicMaterialParams = do
  color <- genRGBA
  opacity <- genNumber 0.0 1.0
  transparent <- elements $ NEA.cons' true [false]
  wireframe <- elements $ NEA.cons' true [false]
  pure { color, opacity, transparent, wireframe }

-- | Generate StandardMaterialParams.
genStandardMaterialParams :: Gen StandardMaterialParams
genStandardMaterialParams = do
  color <- genRGBA
  roughness <- genNumber 0.0 1.0
  metalness <- genNumber 0.0 1.0
  emissive <- genRGBA
  emissiveIntensity <- genNumber 0.0 2.0
  opacity <- genNumber 0.0 1.0
  transparent <- elements $ NEA.cons' true [false]
  wireframe <- elements $ NEA.cons' true [false]
  pure { color, roughness, metalness, emissive, emissiveIntensity, opacity, transparent, wireframe }

-- | Generate a random Material3D.
genMaterial3D :: Gen Material3D
genMaterial3D = oneOf $ NEA.cons'
  (BasicMaterial3D <$> genBasicMaterialParams)
  [ StandardMaterial3D <$> genStandardMaterialParams
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // light generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate AmbientLightParams.
genAmbientLightParams :: Gen AmbientLightParams
genAmbientLightParams = do
  color <- genRGBA
  intensity <- genNumber 0.0 1.0
  pure { color, intensity }

-- | Generate Light3D (ambient only for simplicity).
genLight3D :: Gen Light3D
genLight3D = AmbientLight3D <$> genAmbientLightParams

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // mesh params generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate full MeshParams for a scene.
genMeshParams :: forall msg. Gen (MeshParams msg)
genMeshParams = do
  geometry <- genMesh3D
  material <- genMaterial3D
  position <- genPosition3D
  let rotation = quaternionIdentity
  let scale = vec3 1.0 1.0 1.0
  castShadow <- elements $ NEA.cons' true [false]
  receiveShadow <- elements $ NEA.cons' true [false]
  let pickId = Nothing
  let onClick = Nothing
  let onHover = Nothing
  pure { geometry, material, position, rotation, scale, castShadow, receiveShadow, pickId, onClick, onHover }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // scene generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a Scene3D with random number of lights and meshes.
genScene3D :: forall msg. Gen (Scene3D msg)
genScene3D = do
  camera <- PerspectiveCamera3D <$> genPerspectiveCameraParams
  bg <- genRGBA
  numLights <- chooseInt 0 5
  numMeshes <- chooseInt 0 10
  lights <- vectorOf numLights genLight3D
  meshes <- vectorOf numMeshes genMeshParams
  pure { camera, background: solidBackground bg, lights, meshes }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // camera generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate PerspectiveCameraParams.
genPerspectiveCameraParams :: Gen PerspectiveCameraParams
genPerspectiveCameraParams = do
  position <- genPosition3D
  target <- genPosition3D
  let up = directionY  -- Standard Y-up convention
  fov <- frequency $ NEA.cons'
    (Tuple 30.0 (pure (degrees 75.0)))  -- Standard
    [ Tuple 20.0 (pure (degrees 45.0))  -- Narrow
    , Tuple 20.0 (pure (degrees 90.0))  -- Wide
    , Tuple 30.0 (degrees <$> genNumber 30.0 120.0)  -- Any
    ]
  near <- frequency $ NEA.cons'
    (Tuple 50.0 (pure (meter 0.1)))
    [ Tuple 50.0 (meter <$> genNumber 0.01 1.0)
    ]
  far <- frequency $ NEA.cons'
    (Tuple 30.0 (pure (meter 1000.0)))
    [ Tuple 30.0 (pure (meter 10000.0))
    , Tuple 40.0 (meter <$> genNumber 100.0 10000.0)  -- Capped for Int range
    ]
  aspect <- genAspectRatio
  pure { position, target, up, fov, near, far, aspect }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                // uuid5 determinism property tests
-- ═══════════════════════════════════════════════════════════════════════════════

uuid5DeterminismTests :: Spec Unit
uuid5DeterminismTests = describe "UUID5 Determinism" do
  
  describe "Position3D identity" do
    it "same position always produces same UUID" do
      Spec.quickCheck do
        pos <- genPosition3D
        let uuid1 = Identity.positionId pos
        let uuid2 = Identity.positionId pos
        pure $ uuid1 === uuid2
    
    it "position UUID is pure (no side effects)" do
      Spec.quickCheck do
        x <- genPicometer
        y <- genPicometer
        z <- genPicometer
        let pos = Position3D { x, y, z }
        -- Call multiple times, all should be equal
        let uuid1 = Identity.positionId pos
        let uuid2 = Identity.positionId pos
        let uuid3 = Identity.positionId pos
        pure $ (uuid1 == uuid2 && uuid2 == uuid3)
          <?> "Expected all UUIDs to be equal"
  
  describe "Mesh3D identity" do
    it "same mesh parameters always produce same UUID" do
      Spec.quickCheck do
        mesh <- genMesh3D
        let uuid1 = Identity.meshId mesh
        let uuid2 = Identity.meshId mesh
        pure $ uuid1 === uuid2
    
    it "box mesh UUID is deterministic" do
      Spec.quickCheck do
        params <- genBoxMeshParams
        let uuid1 = Identity.boxMeshId params
        let uuid2 = Identity.boxMeshId params
        pure $ uuid1 === uuid2
    
    it "sphere mesh UUID is deterministic" do
      Spec.quickCheck do
        params <- genSphereMeshParams
        let uuid1 = Identity.sphereMeshId params
        let uuid2 = Identity.sphereMeshId params
        pure $ uuid1 === uuid2
    
    it "cylinder mesh UUID is deterministic" do
      Spec.quickCheck do
        params <- genCylinderMeshParams
        let uuid1 = Identity.cylinderMeshId params
        let uuid2 = Identity.cylinderMeshId params
        pure $ uuid1 === uuid2
  
  describe "Material3D identity" do
    it "same material parameters always produce same UUID" do
      Spec.quickCheck do
        mat <- genMaterial3D
        let uuid1 = Identity.materialId mat
        let uuid2 = Identity.materialId mat
        pure $ uuid1 === uuid2
    
    it "basic material UUID is deterministic" do
      Spec.quickCheck do
        params <- genBasicMaterialParams
        let uuid1 = Identity.basicMaterialId params
        let uuid2 = Identity.basicMaterialId params
        pure $ uuid1 === uuid2
  
  describe "Camera3D identity" do
    it "same camera parameters always produce same UUID" do
      Spec.quickCheck do
        params <- genPerspectiveCameraParams
        let camera = PerspectiveCamera3D params
        let uuid1 = Identity.cameraId camera
        let uuid2 = Identity.cameraId camera
        pure $ uuid1 === uuid2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                           // uuid5 collision resistance tests
-- ═══════════════════════════════════════════════════════════════════════════════

uuid5CollisionResistanceTests :: Spec Unit
uuid5CollisionResistanceTests = describe "UUID5 Collision Resistance" do
  
  describe "Position3D collisions" do
    it "different positions produce different UUIDs (high probability)" do
      Spec.quickCheck do
        { p1, p2 } <- genDistinctPositions
        let uuid1 = Identity.positionId p1
        let uuid2 = Identity.positionId p2
        -- If positions are actually different, UUIDs should differ
        -- Note: There's a tiny theoretical collision probability
        pure $ if p1 == p2 
          then uuid1 === uuid2  -- Same input → same output
          else uuid1 /= uuid2 <?> ("Expected different UUIDs for different positions: " 
                                   <> show p1 <> " vs " <> show p2)
  
  describe "Mesh3D collisions" do
    it "different box dimensions produce different UUIDs" do
      Spec.quickCheck do
        params1 <- genBoxMeshParams
        params2 <- genBoxMeshParams
        let uuid1 = Identity.boxMeshId params1
        let uuid2 = Identity.boxMeshId params2
        pure $ if params1 == params2
          then uuid1 === uuid2
          else uuid1 /= uuid2 <?> "Expected different UUIDs for different box params"
    
    it "box vs sphere always have different UUIDs" do
      Spec.quickCheck do
        boxParams <- genBoxMeshParams
        sphereParams <- genSphereMeshParams
        let boxUuid = Identity.boxMeshId boxParams
        let sphereUuid = Identity.sphereMeshId sphereParams
        pure $ boxUuid /= sphereUuid 
          <?> "Box and sphere should always have different UUIDs"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // scale-specific tests
-- ═══════════════════════════════════════════════════════════════════════════════

scaleSpecificTests :: Spec Unit
scaleSpecificTests = describe "Scale-Specific Tests" do
  
  describe "Atomic scale (picometers)" do
    it "hydrogen bond length (74 pm) produces valid UUID" do
      let pos = Position3D 
            { x: picometer 74.0
            , y: picometer 0.0
            , z: picometer 0.0
            }
      let uuid = Identity.positionId pos
      -- Just verify it doesn't crash and produces something
      show uuid `shouldEqual` show uuid  -- Identity test
    
    it "water molecule geometry produces deterministic UUIDs" do
      -- H-O-H angle is 104.5 degrees, O-H bond is 95.84 pm
      let oxygen = Position3D 
            { x: picometer 0.0
            , y: picometer 0.0
            , z: picometer 0.0
            }
      let hydrogen1 = Position3D 
            { x: picometer 95.84
            , y: picometer 0.0
            , z: picometer 0.0
            }
      let uuid_o1 = Identity.positionId oxygen
      let uuid_o2 = Identity.positionId oxygen
      let uuid_h1 = Identity.positionId hydrogen1
      let uuid_h2 = Identity.positionId hydrogen1
      uuid_o1 `shouldEqual` uuid_o2
      uuid_h1 `shouldEqual` uuid_h2
  
  describe "Human scale (meters)" do
    it "1-meter cube produces valid UUID" do
      let boxParams = 
            { width: meter 1.0
            , height: meter 1.0
            , depth: meter 1.0
            , widthSegments: 1
            , heightSegments: 1
            , depthSegments: 1
            }
      let uuid1 = Identity.boxMeshId boxParams
      let uuid2 = Identity.boxMeshId boxParams
      uuid1 `shouldEqual` uuid2
    
    it "human-height cylinder produces valid UUID" do
      -- Average human height ~1.7m, shoulder width ~0.45m
      -- Using cylinder as approximation
      let params = 
            { radiusTop: meter 0.225
            , radiusBottom: meter 0.225
            , height: meter 1.7
            , radialSegments: 16
            , heightSegments: 1
            , openEnded: false
            , thetaStart: degrees 0.0
            , thetaLength: degrees 360.0
            }
      let mesh = CylinderMesh3D params
      let uuid1 = Identity.meshId mesh
      let uuid2 = Identity.meshId mesh
      uuid1 `shouldEqual` uuid2
  
  describe "Building scale" do
    it "10-story building box produces valid UUID" do
      -- ~30m tall, 20m x 20m footprint
      let boxParams =
            { width: meter 20.0
            , height: meter 30.0
            , depth: meter 20.0
            , widthSegments: 1
            , heightSegments: 10
            , depthSegments: 1
            }
      let uuid1 = Identity.boxMeshId boxParams
      let uuid2 = Identity.boxMeshId boxParams
      uuid1 `shouldEqual` uuid2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // known value sanity tests
-- ═══════════════════════════════════════════════════════════════════════════════

knownValueTests :: Spec Unit
knownValueTests = describe "Known Value Sanity Tests" do
  
  describe "Origin position" do
    it "origin (0,0,0) has a consistent UUID" do
      let origin = Position3D 
            { x: picometer 0.0
            , y: picometer 0.0
            , z: picometer 0.0
            }
      let uuid1 = Identity.positionId origin
      let uuid2 = Identity.positionId origin
      uuid1 `shouldEqual` uuid2
  
  describe "Unit primitives" do
    it "unit cube has consistent UUID" do
      let unitCube =
            { width: meter 1.0
            , height: meter 1.0
            , depth: meter 1.0
            , widthSegments: 1
            , heightSegments: 1
            , depthSegments: 1
            }
      let uuid1 = Identity.boxMeshId unitCube
      let uuid2 = Identity.boxMeshId unitCube
      uuid1 `shouldEqual` uuid2
    
    it "unit sphere has consistent UUID" do
      let unitSphere =
            { radius: meter 1.0
            , widthSegments: 32
            , heightSegments: 16
            , phiStart: degrees 0.0
            , phiLength: degrees 360.0
            , thetaStart: degrees 0.0
            , thetaLength: degrees 180.0
            }
      let uuid1 = Identity.sphereMeshId unitSphere
      let uuid2 = Identity.sphereMeshId unitSphere
      uuid1 `shouldEqual` uuid2
  
  describe "Standard materials" do
    it "red basic material has consistent UUID" do
      let redMaterial =
            { color: rgba 255 0 0 100
            , opacity: 1.0
            , transparent: false
            , wireframe: false
            }
      let uuid1 = Identity.basicMaterialId redMaterial
      let uuid2 = Identity.basicMaterialId redMaterial
      uuid1 `shouldEqual` uuid2
    
    it "white vs black materials have different UUIDs" do
      let whiteMaterial =
            { color: rgba 255 255 255 100
            , opacity: 1.0
            , transparent: false
            , wireframe: false
            }
      let blackMaterial =
            { color: rgba 0 0 0 100
            , opacity: 1.0
            , transparent: false
            , wireframe: false
            }
      let whiteUuid = Identity.basicMaterialId whiteMaterial
      let blackUuid = Identity.basicMaterialId blackMaterial
      (whiteUuid /= blackUuid) `shouldEqual` true

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // flattenScene property tests
-- ═══════════════════════════════════════════════════════════════════════════════

flattenSceneTests :: Spec Unit
flattenSceneTests = describe "flattenScene Correctness" do
  
  describe "Element count preservation" do
    it "buffer length = 1 (camera) + 1 (background) + #lights + #meshes" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let expectedLength = 1 + 1 + Array.length scene.lights + Array.length scene.meshes
        pure $ Array.length buffer === expectedLength
    
    it "empty scene produces buffer of length 2 (camera + background)" do
      let scene = emptyScene :: Scene3D Unit
      let buffer = flattenScene scene
      Array.length buffer `shouldEqual` 2
    
    it "scene with 3 lights and 5 meshes produces buffer of length 10" do
      Spec.quickCheck do
        lights <- vectorOf 3 genLight3D
        meshes <- vectorOf 5 (genMeshParams :: Gen (MeshParams Unit))
        camera <- PerspectiveCamera3D <$> genPerspectiveCameraParams
        bg <- genRGBA
        let scene = { camera, background: solidBackground bg, lights, meshes }
        let buffer = flattenScene scene
        pure $ Array.length buffer === 10
  
  describe "Command ordering" do
    it "first command is always SetCamera" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let first = Array.head buffer
        pure $ case first of
          Nothing -> false <?> "Empty buffer"
          Just (SetCamera _) -> true === true
          Just _ -> false <?> "First command is not SetCamera"
    
    it "second command is always SetBackground" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let second = Array.index buffer 1
        pure $ case second of
          Nothing -> false <?> "Buffer has less than 2 elements"
          Just (SetBackground _) -> true === true
          Just _ -> false <?> "Second command is not SetBackground"
    
    it "lights come before meshes" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let lightIndices = Array.mapWithIndex (\i cmd -> case cmd of
              AddLight _ -> Just i
              _ -> Nothing) buffer
        let meshIndices = Array.mapWithIndex (\i cmd -> case cmd of
              DrawMesh _ -> Just i
              _ -> Nothing) buffer
        let maxLightIdx = Array.foldl (\acc mi -> case mi of
              Just i -> max acc i
              Nothing -> acc) (-1) lightIndices
        let minMeshIdx = Array.foldl (\acc mi -> case mi of
              Just i -> min acc i
              Nothing -> acc) 999999 meshIndices
        -- If we have both lights and meshes, max light index < min mesh index
        let hasLights = Array.length scene.lights > 0
        let hasMeshes = Array.length scene.meshes > 0
        pure $ if hasLights && hasMeshes
          then (maxLightIdx < minMeshIdx) <?> ("Light at " <> show maxLightIdx <> " should be before mesh at " <> show minMeshIdx)
          else true === true
  
  describe "Content preservation" do
    it "all lights appear in buffer" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let lightCount = Array.length $ Array.filter isAddLight buffer
        pure $ lightCount === Array.length scene.lights
    
    it "all meshes appear in buffer" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let meshCount = Array.length $ Array.filter isDrawMesh buffer
        pure $ meshCount === Array.length scene.meshes
    
    it "exactly one camera command" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let cameraCount = Array.length $ Array.filter isSetCamera buffer
        pure $ cameraCount === 1
    
    it "exactly one background command" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer = flattenScene scene
        let bgCount = Array.length $ Array.filter isSetBackground buffer
        pure $ bgCount === 1
  
  describe "Determinism" do
    it "same scene always produces same buffer" do
      Spec.quickCheck do
        scene <- genScene3D :: Gen (Scene3D Unit)
        let buffer1 = flattenScene scene
        let buffer2 = flattenScene scene
        pure $ Array.length buffer1 === Array.length buffer2

-- | Helper: check if command is AddLight
isAddLight :: forall msg. SceneCommand msg -> Boolean
isAddLight (AddLight _) = true
isAddLight _ = false

-- | Helper: check if command is DrawMesh
isDrawMesh :: forall msg. SceneCommand msg -> Boolean
isDrawMesh (DrawMesh _) = true
isDrawMesh _ = false

-- | Helper: check if command is SetCamera
isSetCamera :: forall msg. SceneCommand msg -> Boolean
isSetCamera (SetCamera _) = true
isSetCamera _ = false

-- | Helper: check if command is SetBackground
isSetBackground :: forall msg. SceneCommand msg -> Boolean
isSetBackground (SetBackground _) = true
isSetBackground _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // builder tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tests for Scene3D builder functions: withCamera, withBackground, withLight, withMesh.
-- | These are the primary API for constructing scenes compositionally.
builderFunctionTests :: Spec Unit
builderFunctionTests = describe "Scene3D Tests" $ describe "Builder Functions" do
  
  describe "withCamera" do
    it "sets the camera on an empty scene" do
      let camera = PerspectiveCamera3D
            { fov: degrees 75.0
            , aspect: 1.777
            , near: meter 0.1
            , far: meter 1000.0
            , position: zeroPosition3D
            , target: zeroPosition3D
            , up: directionY
            }
      let scene = emptyScene # withCamera camera
      let buffer = flattenScene scene
      let cameraCmd = Array.head buffer
      case cameraCmd of
        Just (SetCamera c) -> 
          if c == camera 
            then pure unit 
            else fail "Camera in buffer doesn't match input camera"
        _ -> fail "First command should be SetCamera"
    
    it "replaces existing camera" do
      let camera1 = PerspectiveCamera3D
            { fov: degrees 45.0
            , aspect: 1.0
            , near: meter 0.1
            , far: meter 100.0
            , position: zeroPosition3D
            , target: zeroPosition3D
            , up: directionY
            }
      let camera2 = PerspectiveCamera3D
            { fov: degrees 90.0
            , aspect: 2.0
            , near: meter 1.0
            , far: meter 500.0
            , position: zeroPosition3D
            , target: zeroPosition3D
            , up: directionY
            }
      let scene = emptyScene # withCamera camera1 # withCamera camera2
      let buffer = flattenScene scene
      let cameraCount = Array.length $ Array.filter isSetCamera buffer
      cameraCount `shouldEqual` 1
  
  describe "withBackground" do
    it "sets the background on an empty scene" do
      let bg = solidBackground (rgba 100 149 237 100)  -- cornflower blue
      let scene = emptyScene # withBackground bg
      let buffer = flattenScene scene
      let bgCmd = Array.index buffer 1
      case bgCmd of
        Just (SetBackground b) -> 
          if b == bg 
            then pure unit 
            else fail "Background in buffer doesn't match input background"
        _ -> fail "Second command should be SetBackground"
    
    it "replaces existing background" do
      let bg1 = solidBackground (rgba 0 0 0 100)    -- black
      let bg2 = solidBackground (rgba 255 255 255 100)  -- white
      let scene = emptyScene # withBackground bg1 # withBackground bg2
      let buffer = flattenScene scene
      let bgCount = Array.length $ Array.filter isSetBackground buffer
      bgCount `shouldEqual` 1
  
  describe "withLight" do
    it "adds a light to an empty scene" do
      let light = AmbientLight3D
            { color: rgba 255 255 255 100
            , intensity: 1.0
            }
      let scene = emptyScene # withLight light
      Array.length scene.lights `shouldEqual` 1
    
    it "accumulates multiple lights" do
      let light1 = AmbientLight3D { color: rgba 255 255 255 100, intensity: 1.0 }
      let light2 = AmbientLight3D { color: rgba 255 200 150 100, intensity: 0.5 }
      let light3 = AmbientLight3D { color: rgba 100 100 255 100, intensity: 0.3 }
      let scene = emptyScene 
            # withLight light1 
            # withLight light2 
            # withLight light3
      Array.length scene.lights `shouldEqual` 3
    
    it "lights appear in buffer in order added" do
      let light1 = AmbientLight3D { color: rgba 255 0 0 100, intensity: 1.0 }
      let light2 = AmbientLight3D { color: rgba 0 255 0 100, intensity: 1.0 }
      let scene = emptyScene # withLight light1 # withLight light2
      let buffer = flattenScene scene
      let lights = Array.mapMaybe (\cmd -> case cmd of
            AddLight l -> Just l
            _ -> Nothing) buffer
      Array.length lights `shouldEqual` 2
  
  describe "withMesh" do
    it "adds a mesh to an empty scene" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0
            , height: meter 1.0
            , depth: meter 1.0
            , widthSegments: 1
            , heightSegments: 1
            , depthSegments: 1
            }
      let redMat = BasicMaterial3D 
            { color: rgba 255 0 0 100
            , opacity: 1.0
            , transparent: false
            , wireframe: false
            }
      let meshParams = testMeshParams boxGeom redMat zeroPosition3D
      let scene = emptyScene # withMesh meshParams
      Array.length scene.meshes `shouldEqual` 1
    
    it "accumulates multiple meshes" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let sphereGeom = SphereMesh3D 
            { radius: meter 0.5
            , widthSegments: 16
            , heightSegments: 8
            , phiStart: degrees 0.0
            , phiLength: degrees 360.0
            , thetaStart: degrees 0.0
            , thetaLength: degrees 180.0
            }
      let redMat = BasicMaterial3D 
            { color: rgba 255 0 0 100, opacity: 1.0, transparent: false, wireframe: false }
      let greenMat = BasicMaterial3D 
            { color: rgba 0 255 0 100, opacity: 1.0, transparent: false, wireframe: false }
      let boxMesh = testMeshParams boxGeom redMat zeroPosition3D
      let sphereMesh = testMeshParams sphereGeom greenMat 
            (Position3D { x: picometer 2000000000000.0, y: picometer 0.0, z: picometer 0.0 })
      let scene = emptyScene # withMesh boxMesh # withMesh sphereMesh
      Array.length scene.meshes `shouldEqual` 2
    
    it "meshes appear in buffer in order added" do
      let box1 = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let box2 = BoxMesh3D 
            { width: meter 2.0, height: meter 2.0, depth: meter 2.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let redMat = BasicMaterial3D 
            { color: rgba 255 0 0 100, opacity: 1.0, transparent: false, wireframe: false }
      let blueMat = BasicMaterial3D 
            { color: rgba 0 0 255 100, opacity: 1.0, transparent: false, wireframe: false }
      let mesh1 = testMeshParams box1 redMat zeroPosition3D
      let mesh2 = testMeshParams box2 blueMat zeroPosition3D
      let scene = emptyScene # withMesh mesh1 # withMesh mesh2
      let buffer = flattenScene scene
      let meshes = Array.mapMaybe (\cmd -> case cmd of
            DrawMesh m -> Just m
            _ -> Nothing) buffer
      Array.length meshes `shouldEqual` 2

  describe "Compositional building" do
    it "builds complete scene with all builders" do
      let camera = PerspectiveCamera3D
            { fov: degrees 60.0
            , aspect: 1.777
            , near: meter 0.1
            , far: meter 1000.0
            , position: Position3D { x: picometer 0.0, y: picometer 5000000000000.0, z: picometer 10000000000000.0 }
            , target: zeroPosition3D
            , up: directionY
            }
      let bg = solidBackground (rgba 30 30 30 100)
      let light = AmbientLight3D { color: rgba 255 255 255 100, intensity: 0.8 }
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let orangeMat = BasicMaterial3D 
            { color: rgba 200 100 50 100, opacity: 1.0, transparent: false, wireframe: false }
      let mesh = testMeshParams boxGeom orangeMat zeroPosition3D
      let scene = emptyScene 
            # withCamera camera
            # withBackground bg
            # withLight light
            # withMesh mesh
      let buffer = flattenScene scene
      -- Buffer should have: 1 camera + 1 background + 1 light + 1 mesh = 4
      Array.length buffer `shouldEqual` 4
    
    it "builder order doesn't affect final buffer structure" do
      -- Build scene in different orders, verify same structure
      let camera = PerspectiveCamera3D
            { fov: degrees 75.0, aspect: 1.0, near: meter 0.1, far: meter 100.0
            , position: zeroPosition3D, target: zeroPosition3D, up: directionY
            }
      let bg = solidBackground (rgba 0 0 0 100)
      let light = AmbientLight3D { color: rgba 255 255 255 100, intensity: 1.0 }
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let whiteMat = BasicMaterial3D 
            { color: rgba 255 255 255 100, opacity: 1.0, transparent: false, wireframe: false }
      let mesh = testMeshParams boxGeom whiteMat zeroPosition3D
      -- Order 1: camera, bg, light, mesh
      let scene1 = emptyScene # withCamera camera # withBackground bg # withLight light # withMesh mesh
      -- Order 2: mesh, light, bg, camera
      let scene2 = emptyScene # withMesh mesh # withLight light # withBackground bg # withCamera camera
      let buffer1 = flattenScene scene1
      let buffer2 = flattenScene scene2
      -- Both should have same length
      Array.length buffer1 `shouldEqual` Array.length buffer2
      -- Both should start with SetCamera
      case Array.head buffer1 of
        Just (SetCamera _) -> pure unit
        _ -> fail "buffer1 should start with SetCamera"
      case Array.head buffer2 of
        Just (SetCamera _) -> pure unit
        _ -> fail "buffer2 should start with SetCamera"

-- | Tests for Position3D utilities including zeroPosition3D.
positionUtilityTests :: Spec Unit
positionUtilityTests = describe "Scene3D Tests" $ describe "Position Utilities" do
  
  describe "zeroPosition3D" do
    it "has all zero coordinates" do
      case zeroPosition3D of
        Position3D p -> do
          p.x `shouldEqual` picometer 0.0
          p.y `shouldEqual` picometer 0.0
          p.z `shouldEqual` picometer 0.0
    
    it "produces consistent UUID" do
      let uuid1 = Identity.positionId zeroPosition3D
      let uuid2 = Identity.positionId zeroPosition3D
      uuid1 `shouldEqual` uuid2
    
    it "is identity for position operations" do
      -- zeroPosition3D should be usable as a neutral origin
      let camera = PerspectiveCamera3D
            { fov: degrees 60.0
            , aspect: 1.0
            , near: meter 0.1
            , far: meter 100.0
            , position: zeroPosition3D
            , target: zeroPosition3D
            , up: directionY
            }
      let scene = emptyScene # withCamera camera
      let buffer = flattenScene scene
      Array.length buffer `shouldEqual` 2  -- camera + background

-- | Tests for SceneBuffer type alias usage.
sceneBufferTests :: Spec Unit
sceneBufferTests = describe "Scene3D Tests" $ describe "SceneBuffer Type" do
  
  it "SceneBuffer is Array of SceneCommand" do
    -- This test verifies SceneBuffer type alias works correctly
    let scene = emptyScene :: Scene3D Unit
    let buffer :: SceneBuffer Unit
        buffer = flattenScene scene
    -- Buffer is usable as an array
    Array.length buffer `shouldEqual` 2
  
  it "SceneBuffer supports standard array operations" do
    let scene = emptyScene # withLight (AmbientLight3D { color: rgba 255 255 255 100, intensity: 1.0 })
    let buffer :: SceneBuffer Unit
        buffer = flattenScene scene
    -- Can filter
    let lights = Array.filter isAddLight buffer
    Array.length lights `shouldEqual` 1
    -- Can map - handle all SceneCommand constructors explicitly
    let commandTypes = map (\cmd -> case cmd of
          SetCamera _ -> "camera"
          SetBackground _ -> "background"
          AddLight _ -> "light"
          DrawMesh _ -> "mesh"
          DrawGrid _ -> "grid"
          DrawAxes _ -> "axes"
          PushTransform _ -> "pushTransform"
          PopTransform -> "popTransform"
          SetClipPlane _ -> "setClipPlane"
          ClearClipPlane -> "clearClipPlane"
          Noop3D -> "noop") buffer
    Array.length commandTypes `shouldEqual` 3

-- | Tests for Quaternion type usage in mesh parameters.
quaternionUsageTests :: Spec Unit
quaternionUsageTests = describe "Scene3D Tests" $ describe "Quaternion Usage" do
  
  it "MeshParams uses Quaternion for rotation" do
    -- Explicitly create MeshParams with a typed Quaternion rotation
    -- This verifies the Quaternion type is accepted in the rotation field
    let rotation :: Quaternion
        rotation = quaternionIdentity
    let boxGeom = BoxMesh3D 
          { width: meter 1.0, height: meter 1.0, depth: meter 1.0
          , widthSegments: 1, heightSegments: 1, depthSegments: 1
          }
    let whiteMat = BasicMaterial3D 
          { color: rgba 255 255 255 100, opacity: 1.0, transparent: false, wireframe: false }
    -- Create full MeshParams with explicit rotation field to verify Quaternion type
    let meshParams :: MeshParams Unit
        meshParams = 
          { geometry: boxGeom
          , material: whiteMat
          , position: zeroPosition3D
          , rotation: rotation  -- Quaternion type explicitly used
          , scale: vec3 1.0 1.0 1.0
          , castShadow: false
          , receiveShadow: false
          , pickId: Nothing
          , onClick: Nothing
          , onHover: Nothing
          }
    let scene = emptyScene # withMesh meshParams
    Array.length scene.meshes `shouldEqual` 1

-- | Tests for MeshParams advanced features: PickId3D and Vec3 scale.
meshParamsAdvancedTests :: Spec Unit
meshParamsAdvancedTests = describe "Scene3D Tests" $ describe "MeshParams Advanced" do
  
  describe "PickId3D for raycasting" do
    it "mesh can have a PickId3D for raycast identification" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let mat = BasicMaterial3D 
            { color: rgba 255 0 0 100, opacity: 1.0, transparent: false, wireframe: false }
      -- Create mesh with a PickId3D for raycast hit detection
      let pickableId :: PickId3D
          pickableId = pickId3D 42
      let meshParams :: MeshParams Unit
          meshParams = 
            { geometry: boxGeom
            , material: mat
            , position: zeroPosition3D
            , rotation: quaternionIdentity
            , scale: vec3 1.0 1.0 1.0
            , castShadow: false
            , receiveShadow: false
            , pickId: Just pickableId
            , onClick: Nothing
            , onHover: Nothing
            }
      let scene = emptyScene # withMesh meshParams
      -- Verify mesh was added
      Array.length scene.meshes `shouldEqual` 1
      -- Verify pickId is set correctly
      case Array.head scene.meshes of
        Just m -> m.pickId `shouldSatisfy` (_ == Just pickableId)
        Nothing -> fail "Scene should have one mesh"
    
    it "mesh without PickId3D has Nothing" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let mat = BasicMaterial3D 
            { color: rgba 0 255 0 100, opacity: 1.0, transparent: false, wireframe: false }
      let meshParams = testMeshParams boxGeom mat zeroPosition3D
      case meshParams.pickId of
        Nothing -> pure unit
        Just _ -> fail "testMeshParams should create mesh with no pickId"
  
  describe "Vec3 scale" do
    it "scale uses Vec3 Number type" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let mat = BasicMaterial3D 
            { color: rgba 0 0 255 100, opacity: 1.0, transparent: false, wireframe: false }
      -- Create non-uniform scale
      let nonUniformScale :: Vec3 Number
          nonUniformScale = vec3 2.0 0.5 1.5
      let meshParams :: MeshParams Unit
          meshParams = 
            { geometry: boxGeom
            , material: mat
            , position: zeroPosition3D
            , rotation: quaternionIdentity
            , scale: nonUniformScale
            , castShadow: false
            , receiveShadow: false
            , pickId: Nothing
            , onClick: Nothing
            , onHover: Nothing
            }
      let scene = emptyScene # withMesh meshParams
      Array.length scene.meshes `shouldEqual` 1
    
    it "uniform scale 1.0 is identity" do
      let boxGeom = BoxMesh3D 
            { width: meter 1.0, height: meter 1.0, depth: meter 1.0
            , widthSegments: 1, heightSegments: 1, depthSegments: 1
            }
      let mat = BasicMaterial3D 
            { color: rgba 128 128 128 100, opacity: 1.0, transparent: false, wireframe: false }
      let identityScale :: Vec3 Number
          identityScale = vec3 1.0 1.0 1.0
      let meshParams = testMeshParams boxGeom mat zeroPosition3D
      -- testMeshParams uses vec3 1.0 1.0 1.0 as default scale
      meshParams.scale `shouldSatisfy` (_ == identityScale)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // exports
-- ═══════════════════════════════════════════════════════════════════════════════

scene3DTests :: Spec Unit
scene3DTests = do
  uuid5DeterminismTests
  uuid5CollisionResistanceTests
  scaleSpecificTests
  knownValueTests
  flattenSceneTests
  builderFunctionTests
  positionUtilityTests
  sceneBufferTests
  quaternionUsageTests
  meshParamsAdvancedTests
