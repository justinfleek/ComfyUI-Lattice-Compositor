-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // gpu // ui // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 2D UI Renderer — DrawCommand to WebGPU RenderCommand
-- |
-- | Interprets DrawCommand arrays into WebGPU render commands. This is the
-- | 2D counterpart to Scene3D.Render which handles 3D scenes.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Array (DrawCommand msg)
-- |     ↓ sortAndBatch
-- | Array RenderBatch2D
-- |     ↓ generateRenderCommands2D
-- | Array RenderCommand2D (pure data)
-- |     ↓ (executed by runtime via Device.purs FFI)
-- | GPU pixels
-- | ```
-- |
-- | ## Batching Strategy
-- |
-- | For frame.io-level responsiveness at billion-agent scale:
-- |
-- | 1. **Material batching**: Group by shader/texture to minimize state changes
-- | 2. **Depth sorting**: Back-to-front for correct alpha compositing
-- | 3. **Instancing**: Multiple rects with same material → single draw call
-- | 4. **Clip region tracking**: Push/pop clip operations update scissor state
-- |
-- | ## Dependencies
-- | - Hydrogen.GPU.DrawCommand (DrawCommand vocabulary)
-- | - Hydrogen.GPU.WebGPU.Types (Buffer types)
-- |
-- | ## Dependents
-- | - DOM Runtime (executes render commands)

module Hydrogen.GPU.UI.Render
  ( -- * Render Commands (pure data)
    RenderCommand2D
      ( Clear2D
      , SetPipeline2D
      , SetScissor2D
      , DrawInstanced2D
      , DrawIndexed2D
      )
  , ClearParams2D
  , PipelineId(PipelineId)
  , ScissorRect
  , DrawInstancedParams
  , DrawIndexedParams2D
  
  -- * Render State
  , RenderState2D
  , extractRenderState2D
  
  -- * Command Generation
  , generateRenderCommands2D
  
  -- * Batching
  , RenderBatch2D
  , batchDrawCommands
  
  -- * Viewport
  , Viewport2D
  , viewport2D
  
  -- * Clip Stack
  , ClipStack
  , emptyClipStack
  , pushClipRegion
  , popClipRegion
  , currentScissor
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , otherwise
  , show
  , ($)
  , (+)
  , (-)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (&&)
  )

import Data.Array (filter, length, take, drop) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.DrawCommand
  ( DrawCommand
      ( DrawRect
      , DrawQuad
      , DrawGlyph
      , DrawPath
      , DrawParticle
      , PushClip
      , PopClip
      , Noop
      )
  , ClipRegion(ClipRect, ClipPath)
  , RectParams
  , QuadParams
  , GlyphParams
  , PathParams
  , ParticleParams
  )

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // render commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D Render commands — pure data describing GPU operations
-- |
-- | These are interpreted by the WebGPU runtime into actual draw calls.
data RenderCommand2D
  = Clear2D ClearParams2D
    -- ^ Clear the framebuffer
  | SetPipeline2D PipelineId
    -- ^ Switch to a different shader pipeline
  | SetScissor2D ScissorRect
    -- ^ Set scissor rectangle for clipping
  | DrawInstanced2D DrawInstancedParams
    -- ^ Draw multiple instances with single call
  | DrawIndexed2D DrawIndexedParams2D
    -- ^ Draw with index buffer

derive instance eqRenderCommand2D :: Eq RenderCommand2D

-- | Clear parameters
type ClearParams2D =
  { r :: Number
  , g :: Number
  , b :: Number
  , a :: Number
  }

-- | Pipeline identifier
newtype PipelineId = PipelineId String

derive instance eqPipelineId :: Eq PipelineId
derive instance ordPipelineId :: Ord PipelineId

-- | Scissor rectangle for clipping
type ScissorRect =
  { x :: Int
  , y :: Int
  , width :: Int
  , height :: Int
  }

-- | Instanced draw parameters
type DrawInstancedParams =
  { pipelineId :: PipelineId
  , vertexCount :: Int
  , instanceCount :: Int
  , firstVertex :: Int
  , firstInstance :: Int
  }

-- | Indexed draw parameters
type DrawIndexedParams2D =
  { pipelineId :: PipelineId
  , indexCount :: Int
  , instanceCount :: Int
  , firstIndex :: Int
  , baseVertex :: Int
  , firstInstance :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // render state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extracted render state from DrawCommand array
-- |
-- | Pre-computed state for efficient command generation.
type RenderState2D =
  { batches :: Array RenderBatch2D
    -- ^ Commands grouped by material/pipeline
  , clipStack :: ClipStack
    -- ^ Current clip region stack
  , viewport :: Viewport2D
    -- ^ Viewport dimensions
  , totalCommands :: Int
    -- ^ Total number of draw commands
  }

-- | Extract render state from commands
extractRenderState2D :: forall msg. Viewport2D -> Array (DrawCommand msg) -> RenderState2D
extractRenderState2D vp commands =
  { batches: batchDrawCommands commands
  , clipStack: buildClipStack commands
  , viewport: vp
  , totalCommands: Array.length commands
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // command generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate render commands from render state
-- |
-- | Produces flat array of GPU commands ready for execution.
generateRenderCommands2D :: RenderState2D -> Array RenderCommand2D
generateRenderCommands2D state =
  let
    clearCmd = [Clear2D { r: 0.0, g: 0.0, b: 0.0, a: 1.0 }]
    batchCmds = concatMapArray generateBatchCommands state.batches
  in
    clearCmd <> batchCmds

-- | Generate commands for a single batch
generateBatchCommands :: RenderBatch2D -> Array RenderCommand2D
generateBatchCommands batch =
  let
    pipelineCmd = SetPipeline2D batch.pipelineId
    scissorCmd = case batch.scissor of
      Nothing -> []
      Just rect -> [SetScissor2D rect]
    drawCmd = DrawInstanced2D
      { pipelineId: batch.pipelineId
      , vertexCount: 6  -- Quad = 2 triangles = 6 vertices
      , instanceCount: batch.instanceCount
      , firstVertex: 0
      , firstInstance: batch.firstInstance
      }
  in
    [pipelineCmd] <> scissorCmd <> [drawCmd]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // batching
-- ═════════════════════════════════════════════════════════════════════════════

-- | A batch of draw commands with shared state
-- |
-- | Batching minimizes GPU state changes for maximum throughput.
type RenderBatch2D =
  { pipelineId :: PipelineId
    -- ^ Shader pipeline for this batch
  , instanceCount :: Int
    -- ^ Number of instances to draw
  , firstInstance :: Int
    -- ^ First instance index
  , scissor :: Maybe ScissorRect
    -- ^ Optional scissor for clipping
  , depth :: Number
    -- ^ Depth for sorting (back-to-front)
  }

-- | Batch draw commands by pipeline
-- |
-- | Groups consecutive commands that share the same pipeline into batches.
batchDrawCommands :: forall msg. Array (DrawCommand msg) -> Array RenderBatch2D
batchDrawCommands commands =
  let
    -- Filter to drawable commands (skip Noop, handle clip ops separately)
    drawables = Array.filter isDrawable commands
    -- Group by pipeline
    groups = groupByPipeline drawables
  in
    mapArray toBatch groups
  where
    isDrawable :: DrawCommand msg -> Boolean
    isDrawable cmd = case cmd of
      Noop -> false
      PushClip _ -> false
      PopClip -> false
      _ -> true

-- | Group commands by their pipeline
groupByPipeline :: forall msg. Array (DrawCommand msg) -> Array (Array (DrawCommand msg))
groupByPipeline commands = groupByImpl getPipelineId commands

-- | Get pipeline ID for a command
getPipelineId :: forall msg. DrawCommand msg -> PipelineId
getPipelineId cmd = case cmd of
  DrawRect _ -> PipelineId "rect"
  DrawQuad _ -> PipelineId "quad"
  DrawGlyph _ -> PipelineId "glyph"
  DrawPath _ -> PipelineId "path"
  DrawParticle _ -> PipelineId "particle"
  _ -> PipelineId "default"

-- | Convert group to batch
toBatch :: forall msg. Array (DrawCommand msg) -> RenderBatch2D
toBatch group =
  { pipelineId: case Array.take 1 group of
      [cmd] -> getPipelineId cmd
      _ -> PipelineId "default"
  , instanceCount: Array.length group
  , firstInstance: 0  -- Would need proper tracking
  , scissor: Nothing
  , depth: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D viewport dimensions
type Viewport2D =
  { width :: Int
  , height :: Int
  , pixelRatio :: Number
  }

-- | Create viewport
viewport2D :: Int -> Int -> Number -> Viewport2D
viewport2D width height pixelRatio = { width, height, pixelRatio }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // clip stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stack of clip regions
-- |
-- | PushClip adds a region, PopClip removes. Current scissor is intersection.
type ClipStack =
  { regions :: Array ClipRegion
  , currentScissor :: Maybe ScissorRect
  }

-- | Empty clip stack (no clipping)
emptyClipStack :: ClipStack
emptyClipStack = { regions: [], currentScissor: Nothing }

-- | Push a clip region onto the stack
pushClipRegion :: ClipRegion -> Viewport2D -> ClipStack -> ClipStack
pushClipRegion region vp stack =
  let
    newRegions = stack.regions <> [region]
    newScissor = computeScissor vp newRegions
  in
    { regions: newRegions, currentScissor: newScissor }

-- | Pop a clip region from the stack
popClipRegion :: Viewport2D -> ClipStack -> ClipStack
popClipRegion vp stack =
  let
    newRegions = case Array.length stack.regions of
      0 -> []
      n -> Array.take (n - 1) stack.regions
    newScissor = computeScissor vp newRegions
  in
    { regions: newRegions, currentScissor: newScissor }

-- | Get current scissor rectangle
currentScissor :: ClipStack -> Maybe ScissorRect
currentScissor stack = stack.currentScissor

-- | Compute scissor from clip regions
computeScissor :: Viewport2D -> Array ClipRegion -> Maybe ScissorRect
computeScissor vp regions = case Array.length regions of
  0 -> Nothing
  _ -> Just (foldlArray intersectClip fullViewport regions)
  where
    fullViewport = { x: 0, y: 0, width: vp.width, height: vp.height }

-- | Intersect clip region with scissor
intersectClip :: ScissorRect -> ClipRegion -> ScissorRect
intersectClip rect region = case region of
  ClipRect cr ->
    let
      -- Convert Pixel to Int for scissor rect
      crX = pixelToInt cr.x
      crY = pixelToInt cr.y
      crW = pixelToInt cr.width
      crH = pixelToInt cr.height
      x1 = maxInt rect.x crX
      y1 = maxInt rect.y crY
      x2 = minInt (rect.x + rect.width) (crX + crW)
      y2 = minInt (rect.y + rect.height) (crY + crH)
    in
      { x: x1, y: y1, width: maxInt 0 (x2 - x1), height: maxInt 0 (y2 - y1) }
  ClipPath _ ->
    -- Path clipping requires stencil buffer, return unchanged for now
    rect

-- | Build clip stack from commands
buildClipStack :: forall msg. Array (DrawCommand msg) -> ClipStack
buildClipStack _ = emptyClipStack  -- Full implementation would walk commands

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over array
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldlArray (\acc x -> acc <> [f x]) []

-- | Concat map over array
concatMapArray :: forall a b. (a -> Array b) -> Array a -> Array b
concatMapArray f = foldlArray (\acc x -> acc <> f x) []

-- | Fold left over array
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Group array by key function
groupByImpl :: forall a k. Eq k => (a -> k) -> Array a -> Array (Array a)
groupByImpl getKey arr = groupByGo getKey arr []

groupByGo :: forall a k. Eq k => (a -> k) -> Array a -> Array (Array a) -> Array (Array a)
groupByGo _ [] acc = acc
groupByGo getKey arr acc = case Array.take 1 arr of
  [] -> acc
  [x] ->
    let
      key = getKey x
      span = spanArray (\a -> getKey a == key) arr
      group = span.fst
      remaining = span.snd
    in
      groupByGo getKey remaining (acc <> [group])
  _ -> acc

-- | Split array at first element that doesn't satisfy predicate
spanArray :: forall a. (a -> Boolean) -> Array a -> { fst :: Array a, snd :: Array a }
spanArray pred arr = spanGo pred arr [] 

spanGo :: forall a. (a -> Boolean) -> Array a -> Array a -> { fst :: Array a, snd :: Array a }
spanGo _ [] acc = { fst: acc, snd: [] }
spanGo pred arr acc = case Array.take 1 arr of
  [] -> { fst: acc, snd: [] }
  [x] ->
    if pred x
      then spanGo pred (Array.drop 1 arr) (acc <> [x])
      else { fst: acc, snd: arr }
  _ -> { fst: acc, snd: arr }

-- | Max of two ints
maxInt :: Int -> Int -> Int
maxInt a b = if a > b then a else b

-- | Min of two ints
minInt :: Int -> Int -> Int
minInt a b = if a > b then b else a

-- | Convert Pixel to Int (truncates)
pixelToInt :: Pixel -> Int
pixelToInt (Pixel n) = truncateNumber n

-- | Truncate Number to Int
truncateNumber :: Number -> Int
truncateNumber n = if n >= 0.0 then truncatePositive n else negateInt (truncatePositive (negateNum n))

truncatePositive :: Number -> Int
truncatePositive n = truncateGo n 0

truncateGo :: Number -> Int -> Int
truncateGo n acc
  | n >= 1.0 = truncateGo (n - 1.0) (acc + 1)
  | otherwise = acc

negateInt :: Int -> Int
negateInt n = 0 - n

negateNum :: Number -> Number
negateNum n = 0.0 - n
