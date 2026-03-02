-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // runtime
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen WASM Runtime Bridge
-- |
-- | This module provides the PureScript interface to the Rust WASM runtime.
-- | It orchestrates the complete rendering pipeline:
-- |
-- | ```
-- | Element msg
-- |     ↓ flatten
-- | CommandBuffer (DrawCommand array)
-- |     ↓ serialize
-- | Bytes (binary wire format)
-- |     ↓ render (FFI to WASM)
-- | WebGPU → pixels
-- | ```
-- |
-- | ## Design Philosophy
-- |
-- | 1. **Pure core, effectful boundary**: Flatten and serialize are pure.
-- |    Only the actual WASM call is effectful.
-- |
-- | 2. **Single render path**: All Elements go through the same pipeline.
-- |    No special cases, no escape hatches.
-- |
-- | 3. **Deterministic output**: Same Element produces same binary output.
-- |    Enables caching, comparison, and reproducibility.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Runtime as Runtime
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Create runtime attached to canvas
-- | runtime <- Runtime.create canvasElement
-- |
-- | -- Render an element
-- | Runtime.renderElement runtime myElement
-- |
-- | -- Or for lower-level control:
-- | let bytes = Runtime.elementToBytes myElement
-- | Runtime.renderBytes runtime bytes
-- | ```

module Hydrogen.Runtime
  ( -- * Types
    Runtime
  , RenderResult
  , RuntimeError(..)
  
  -- * Runtime Lifecycle
  , create
  , resize
  
  -- * Rendering
  , renderElement
  , renderCommands
  , renderBytes
  
  -- * Pipeline Stages (pure)
  , elementToCommands
  , commandsToBytes
  , elementToBytes
  
  -- * Interaction
  , pick
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , Unit
  , bind
  , discard
  , map
  , pure
  , show
  , ($)
  , (<>)
  )

import Data.Either (Either(Left, Right))
import Data.Map (Map)
import Effect (Effect)
import Effect.Aff (Aff)

import Hydrogen.Render.Element (Element)
import Hydrogen.GPU.DrawCommand (DrawCommand, PickId)
import Hydrogen.GPU.Flatten as Flatten
import Hydrogen.GPU.Binary as Binary

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opaque handle to the WASM runtime instance.
-- |
-- | Created via `create`, used for all rendering operations.
-- | Each Runtime is bound to a specific canvas element.
foreign import data Runtime :: Type

-- | Result of a render operation.
type RenderResult msg =
  { pickMap :: Map PickId msg
  -- ^ Mapping from GPU pick IDs to application messages.
  --   Used to dispatch events when the pick buffer reports an interaction.
  }

-- | Errors that can occur during runtime operations.
data RuntimeError
  = WebGPUNotSupported
    -- ^ Browser doesn't support WebGPU
  | AdapterNotFound
    -- ^ No suitable GPU adapter found
  | DeviceCreationFailed String
    -- ^ Failed to create GPU device
  | CanvasConfigFailed String
    -- ^ Failed to configure canvas context
  | ParseError String
    -- ^ Failed to parse command buffer
  | RenderError String
    -- ^ Error during rendering

instance showRuntimeError :: Show RuntimeError where
  show WebGPUNotSupported = "WebGPU is not supported in this browser"
  show AdapterNotFound = "No suitable GPU adapter found"
  show (DeviceCreationFailed msg) = "Device creation failed: " <> msg
  show (CanvasConfigFailed msg) = "Canvas configuration failed: " <> msg
  show (ParseError msg) = "Parse error: " <> msg
  show (RenderError msg) = "Render error: " <> msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // runtime lifecycle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a new runtime attached to a canvas element.
-- |
-- | This initializes WebGPU, creates the render pipeline, and configures
-- | the canvas for rendering. Returns an error if WebGPU is not available
-- | or initialization fails.
-- |
-- | ```purescript
-- | result <- Runtime.create canvasElement
-- | case result of
-- |   Left err -> log $ "Failed: " <> show err
-- |   Right runtime -> -- ready to render
-- | ```
create :: HtmlCanvasElement -> Aff (Either RuntimeError Runtime)
create canvas = createRuntimeImpl canvas

-- | Resize the runtime's render target.
-- |
-- | Call this when the canvas size changes (e.g., window resize).
-- | The runtime will reconfigure its swap chain to match.
resize :: Runtime -> Int -> Int -> Effect Unit
resize = resizeImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render an Element tree.
-- |
-- | This is the main entry point for rendering. It:
-- | 1. Flattens the Element tree to DrawCommands
-- | 2. Serializes to binary format
-- | 3. Passes to the WASM runtime for GPU execution
-- |
-- | Returns the pick map for event dispatch.
renderElement :: forall msg. Runtime -> Element msg -> Effect (Either RuntimeError (RenderResult msg))
renderElement runtime element = do
  let flattened = Flatten.flatten element
  let bytes = Binary.serialize flattened.commands
  result <- renderBytesImpl runtime (Binary.toByteArray bytes)
  pure $ map (\_ -> { pickMap: flattened.pickMap }) result

-- | Render pre-flattened DrawCommands.
-- |
-- | Use this when you've already flattened and want to serialize/render.
-- | Useful for caching the flatten step.
renderCommands :: forall msg. Runtime -> Array (DrawCommand msg) -> Map PickId msg -> Effect (Either RuntimeError (RenderResult msg))
renderCommands runtime commands pickMap = do
  let bytes = Binary.serialize commands
  result <- renderBytesImpl runtime (Binary.toByteArray bytes)
  pure $ map (\_ -> { pickMap }) result

-- | Render pre-serialized bytes.
-- |
-- | Use this when you have cached or pre-computed binary command buffers.
-- | Lowest-level render function.
renderBytes :: Runtime -> Array Int -> Effect (Either RuntimeError Unit)
renderBytes = renderBytesImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pipeline stages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Element to DrawCommands (pure).
-- |
-- | First stage of the pipeline. Returns the command array and pick map.
elementToCommands :: forall msg. Element msg -> Flatten.FlattenResult msg
elementToCommands = Flatten.flatten

-- | Convert DrawCommands to binary bytes (pure).
-- |
-- | Second stage of the pipeline. Serializes to wire format.
commandsToBytes :: forall msg. Array (DrawCommand msg) -> Array Int
commandsToBytes commands = Binary.toByteArray (Binary.serialize commands)

-- | Convert Element directly to binary bytes (pure).
-- |
-- | Convenience function combining flatten and serialize.
elementToBytes :: forall msg. Element msg -> { bytes :: Array Int, pickMap :: Map PickId msg }
elementToBytes element =
  let flattened = Flatten.flatten element
  in { bytes: Binary.toByteArray (Binary.serialize flattened.commands)
     , pickMap: flattened.pickMap
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // interaction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Query the pick buffer at screen coordinates.
-- |
-- | Returns the PickId at the given position, or 0 if no interactive
-- | element is at that location. Use with the pick map from renderElement
-- | to dispatch messages.
-- |
-- | ```purescript
-- | pickId <- Runtime.pick runtime mouseX mouseY
-- | case Map.lookup (pickId pickId) pickMap of
-- |   Just msg -> dispatch msg
-- |   Nothing -> pure unit  -- No interactive element
-- | ```
pick :: Runtime -> Int -> Int -> Effect Int
pick = pickImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // ffi imports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canvas element type (from web-html).
foreign import data HtmlCanvasElement :: Type

-- | Create runtime - async because WebGPU init is async.
foreign import createRuntimeImpl 
  :: HtmlCanvasElement 
  -> Aff (Either RuntimeError Runtime)

-- | Resize the runtime's render target.
foreign import resizeImpl 
  :: Runtime 
  -> Int 
  -> Int 
  -> Effect Unit

-- | Render bytes to the canvas.
foreign import renderBytesImpl 
  :: Runtime 
  -> Array Int 
  -> Effect (Either RuntimeError Unit)

-- | Query pick buffer.
foreign import pickImpl 
  :: Runtime 
  -> Int 
  -> Int 
  -> Effect Int
