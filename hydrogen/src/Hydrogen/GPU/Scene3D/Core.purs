-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Scene3D Core — Commands, scene type, pick buffer, and buffer operations.
-- |
-- | ## SceneCommand
-- | Single GPU primitive operations. The interpreter batches by material/shader
-- | and dispatches draw calls.
-- |
-- | ## Scene3D
-- | High-level scene description (camera, background, lights, meshes).
-- |
-- | ## PickId3D
-- | Unique identifier for GPU-based hit testing via color-coded render pass.

module Hydrogen.GPU.Scene3D.Core
  ( -- * Core Types
    Scene3D
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
  , SceneBuffer
  
  -- * Scene Construction
  , emptyScene
  , withCamera
  , withBackground
  , withLight
  , withMesh
  
  -- * Command Construction
  , setCamera
  , setBackground
  , addLight
  , drawMesh
  , drawGrid
  , drawAxes
  , pushTransform
  , popTransform
  
  -- * Buffer Operations
  , emptyBuffer3D
  , singleton3D
  , append3D
  , concat3D
  
  -- * Scene Flattening
  , flattenScene
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude (map, (<>))

import Data.Array as Array

import Hydrogen.GPU.Scene3D.Position (directionY, position3D, zeroPosition3D)
import Hydrogen.GPU.Scene3D.Camera (Camera3D, perspectiveCamera)
import Hydrogen.GPU.Scene3D.Background (Background3D, solidBackground)
import Hydrogen.GPU.Scene3D.Light (Light3D)
import Hydrogen.GPU.Scene3D.Mesh (MeshParams)
import Hydrogen.GPU.Scene3D.Transform (Transform3DParams, ClipPlane3D)
import Hydrogen.GPU.Scene3D.Grid (Grid3D, Axes3D)

import Hydrogen.Schema.Dimension.Physical.Atomic (picometer)
import Hydrogen.Schema.Dimension.Physical.SI (meter)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Geometry.Angle (degrees)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scene command
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D scene command — single GPU primitive operation.
-- |
-- | The `msg` type parameter carries the message to dispatch when this
-- | element is interacted with (via pick buffer raycast).
data SceneCommand msg
  = SetCamera Camera3D
  | SetBackground Background3D
  | AddLight Light3D
  | DrawMesh (MeshParams msg)
  | DrawGrid Grid3D
  | DrawAxes Axes3D
  | PushTransform Transform3DParams
  | PopTransform
  | SetClipPlane ClipPlane3D
  | ClearClipPlane
  | Noop3D

-- | A command buffer — array of commands ready for GPU dispatch.
type SceneBuffer msg = Array (SceneCommand msg)

-- | High-level scene description (before flattening to commands).
type Scene3D msg =
  { camera :: Camera3D
  , background :: Background3D
  , lights :: Array Light3D
  , meshes :: Array (MeshParams msg)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // scene construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty scene with default camera and black background.
emptyScene :: forall msg. Scene3D msg
emptyScene =
  { camera: perspectiveCamera defaultPerspectiveCamera
  , background: solidBackground defaultBackground
  , lights: []
  , meshes: []
  }
  where
  defaultPerspectiveCamera =
    { position: position3D (picometer 0.0) (picometer 5.0e12) (picometer 10.0e12)
    , target: zeroPosition3D
    , up: directionY
    , fov: degrees 75.0
    , near: meter 0.1
    , far: meter 1000.0
    , aspect: 1.777  -- 16:9
    }
  defaultBackground = RGB.rgba 0 0 0 255

-- | Set the camera for a scene.
withCamera :: forall msg. Camera3D -> Scene3D msg -> Scene3D msg
withCamera camera scene = scene { camera = camera }

-- | Set the background for a scene.
withBackground :: forall msg. Background3D -> Scene3D msg -> Scene3D msg
withBackground bg scene = scene { background = bg }

-- | Add a light to a scene.
withLight :: forall msg. Light3D -> Scene3D msg -> Scene3D msg
withLight light scene = scene { lights = Array.snoc scene.lights light }

-- | Add a mesh to a scene.
withMesh :: forall msg. MeshParams msg -> Scene3D msg -> Scene3D msg
withMesh mesh scene = scene { meshes = Array.snoc scene.meshes mesh }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // command construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a SetCamera command.
setCamera :: forall msg. Camera3D -> SceneCommand msg
setCamera = SetCamera

-- | Create a SetBackground command.
setBackground :: forall msg. Background3D -> SceneCommand msg
setBackground = SetBackground

-- | Create an AddLight command.
addLight :: forall msg. Light3D -> SceneCommand msg
addLight = AddLight

-- | Create a DrawMesh command.
drawMesh :: forall msg. MeshParams msg -> SceneCommand msg
drawMesh = DrawMesh

-- | Create a DrawGrid command.
drawGrid :: forall msg. Grid3D -> SceneCommand msg
drawGrid = DrawGrid

-- | Create a DrawAxes command.
drawAxes :: forall msg. Axes3D -> SceneCommand msg
drawAxes = DrawAxes

-- | Push a transform onto the transform stack.
pushTransform :: forall msg. Transform3DParams -> SceneCommand msg
pushTransform = PushTransform

-- | Pop a transform from the transform stack.
popTransform :: forall msg. SceneCommand msg
popTransform = PopTransform

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // buffer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty scene buffer.
emptyBuffer3D :: forall msg. SceneBuffer msg
emptyBuffer3D = []

-- | Create a buffer with a single command.
singleton3D :: forall msg. SceneCommand msg -> SceneBuffer msg
singleton3D cmd = [cmd]

-- | Append a command to a buffer.
append3D :: forall msg. SceneCommand msg -> SceneBuffer msg -> SceneBuffer msg
append3D cmd buffer = Array.snoc buffer cmd

-- | Concatenate two buffers.
concat3D :: forall msg. SceneBuffer msg -> SceneBuffer msg -> SceneBuffer msg
concat3D a b = a <> b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scene flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Scene3D to a SceneBuffer ready for GPU dispatch.
-- |
-- | Converts the high-level scene description to a flat array of commands.
-- | The order is deterministic:
-- | 1. SetCamera
-- | 2. SetBackground
-- | 3. AddLight (for each light)
-- | 4. DrawMesh (for each mesh)
-- |
-- | ## Why Flat?
-- |
-- | Arrays can be concatenated and batched. Trees require traversal.
-- | The GPU wants draw calls, not scene graphs.
-- |
-- | ## Proof Reference
-- |
-- | Flattening preserves semantics: `proofs/Hydrogen/GPU/Flatten.lean`
flattenScene :: forall msg. Scene3D msg -> SceneBuffer msg
flattenScene scene =
  let
    cameraCmd = [SetCamera scene.camera]
    bgCmd = [SetBackground scene.background]
    lightCmds = map AddLight scene.lights
    meshCmds = map DrawMesh scene.meshes
  in
    cameraCmd <> bgCmd <> lightCmds <> meshCmds
