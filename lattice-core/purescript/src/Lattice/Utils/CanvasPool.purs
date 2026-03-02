-- | Lattice.Utils.CanvasPool - Canvas buffer pool for effect processing
-- |
-- | @module Lattice.Utils.CanvasPool
-- | @description Reuses canvas elements to reduce allocation overhead and
-- | prevent memory leaks. Used by effect processors and layer style renderers.
-- |
-- | ## Architecture
-- |
-- | The pool maintains a fixed-size collection of canvas elements that can be
-- | borrowed and returned. When a canvas is requested:
-- |
-- | 1. Check if an unused canvas with matching dimensions exists
-- | 2. If yes, mark it in-use and return it
-- | 3. If no matching canvas exists, return Nothing (canvas must be provided externally)
-- | 4. Old unused canvases are periodically cleaned up
-- |
-- | ## Canvas Creation
-- |
-- | This module does NOT create canvas elements - canvas creation requires
-- | DOM access which should be handled by the rendering system. Use `register`
-- | to add externally-created canvases to the pool.
-- |
-- | Source: ui/src/utils/canvasPool.ts

module Lattice.Utils.CanvasPool
  ( -- * Types
    CanvasResult
  , PooledCanvas
  , CanvasPool
  , PoolStats
    -- * Pool Operations
  , mkCanvasPool
  , register
  , acquire
  , release
  , cleanup
  , clear
  , getStats
  ) where

import Prelude

import Data.Array (filter, length, snoc, index, updateAt)
import Data.Array as Array
import Data.DateTime.Instant (unInstant)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Now (now)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Graphics.Canvas as Canvas
import Unsafe.Reference (unsafeRefEq)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Result of acquiring a canvas from the pool
-- |
-- | @field canvas The canvas element to draw on
-- | @field ctx The 2D rendering context for drawing operations
type CanvasResult =
  { canvas :: Canvas.CanvasElement
  , ctx :: Canvas.Context2D
  }

-- | Internal pooled canvas record
-- |
-- | @field canvas The canvas element
-- | @field ctx The rendering context
-- | @field width Canvas width in pixels
-- | @field height Canvas height in pixels
-- | @field inUse Whether the canvas is currently borrowed
-- | @field lastUsed Timestamp of last use (for cleanup)
type PooledCanvas =
  { canvas :: Canvas.CanvasElement
  , ctx :: Canvas.Context2D
  , width :: Int
  , height :: Int
  , inUse :: Boolean
  , lastUsed :: Number
  }

-- | Pool statistics for monitoring
-- |
-- | @field total Total canvases in pool
-- | @field inUse Number currently borrowed
-- | @field available Number available for borrowing
type PoolStats =
  { total :: Int
  , inUse :: Int
  , available :: Int
  }

-- | Canvas pool configuration
-- |
-- | @field maxSize Maximum number of canvases to pool
-- | @field maxAge Maximum age in milliseconds before cleanup
type PoolConfig =
  { maxSize :: Int
  , maxAge :: Number
  }

-- | Canvas pool state
-- |
-- | Wraps a mutable reference to the pool array plus configuration.
newtype CanvasPool = CanvasPool
  { pool :: Ref (Array PooledCanvas)
  , config :: PoolConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Pool Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Default pool configuration
-- |
-- | - maxSize: 20 canvases
-- | - maxAge: 60 seconds before cleanup
defaultConfig :: PoolConfig
defaultConfig =
  { maxSize: 20
  , maxAge: 60000.0
  }

-- | Create a new canvas pool
-- |
-- | @returns A new empty pool with default configuration
mkCanvasPool :: Effect CanvasPool
mkCanvasPool = do
  poolRef <- Ref.new []
  pure $ CanvasPool { pool: poolRef, config: defaultConfig }

-- | Get current timestamp in milliseconds
-- |
-- | @returns Current time as milliseconds since epoch
nowMs :: Effect Number
nowMs = do
  instant <- now
  let (Milliseconds ms) = unInstant instant
  pure ms

-- | Register an externally-created canvas with the pool
-- |
-- | Since canvas creation requires DOM access, canvases must be created
-- | externally (e.g., via Halogen refs or document.createElement) and then
-- | registered with the pool for reuse.
-- |
-- | @param pool The pool to register with
-- | @param canvas The canvas element to add
-- | @param ctx The 2D context for the canvas
-- | @param width Canvas width in pixels
-- | @param height Canvas height in pixels
-- |
-- | @postcondition Canvas is added to pool and marked as available
register :: CanvasPool -> Canvas.CanvasElement -> Canvas.Context2D -> Int -> Int -> Effect Unit
register (CanvasPool { pool: poolRef, config }) canvas ctx width height = do
  timestamp <- nowMs
  items <- Ref.read poolRef
  -- Only add if under max size
  when (length items < config.maxSize) do
    let entry = 
          { canvas
          , ctx
          , width
          , height
          , inUse: false
          , lastUsed: timestamp
          }
    Ref.modify_ (\arr -> snoc arr entry) poolRef

-- | Acquire a canvas of specified dimensions
-- |
-- | Looks for an available canvas in the pool with matching dimensions.
-- | If no matching canvas is available, returns Nothing.
-- |
-- | To use this effectively:
-- | 1. Call acquire with desired dimensions
-- | 2. If Nothing, create a canvas externally and register it
-- | 3. Call acquire again to get the newly registered canvas
-- |
-- | @param pool The canvas pool to borrow from
-- | @param width Desired canvas width in pixels
-- | @param height Desired canvas height in pixels
-- | @returns A canvas result with the element and context, or Nothing if none available
-- |
-- | @postcondition If Just, canvas is cleared before returning
-- | @postcondition If Just, canvas is marked as in-use in the pool
acquire :: CanvasPool -> Int -> Int -> Effect (Maybe CanvasResult)
acquire (CanvasPool { pool: poolRef }) width height = do
  timestamp <- nowMs
  items <- Ref.read poolRef

  -- Try to find matching canvas using safe index
  case findAvailableIndex items width height of
    Just idx -> do
      -- Safely access the item at index
      case index items idx of
        Just item -> do
          -- Mark as in use
          Ref.modify_ (markInUseAt idx timestamp) poolRef
          -- Clear the canvas
          Canvas.clearRect item.ctx 
            { x: 0.0, y: 0.0, width: Int.toNumber width, height: Int.toNumber height }
          pure $ Just { canvas: item.canvas, ctx: item.ctx }
        Nothing ->
          -- Index was valid but item not found (shouldn't happen)
          pure Nothing

    Nothing ->
      -- No matching canvas available - caller should create one externally
      pure Nothing

-- | Find index of available canvas with matching dimensions
-- |
-- | Uses Data.Array.findIndex for safe access.
-- |
-- | @param items Array of pooled canvases
-- | @param targetWidth Required width
-- | @param targetHeight Required height
-- | @returns Index of matching available canvas, if any
findAvailableIndex :: Array PooledCanvas -> Int -> Int -> Maybe Int
findAvailableIndex items targetWidth targetHeight =
  Array.findIndex isMatch items
  where
    isMatch item =
      not item.inUse &&
      item.width == targetWidth &&
      item.height == targetHeight

-- | Mark item at index as in use
-- |
-- | Uses Data.Array.updateAt for safe modification.
-- |
-- | @param idx Index to update
-- | @param timestamp Current timestamp
-- | @param arr Array to modify
-- | @returns Modified array (unchanged if index out of bounds)
markInUseAt :: Int -> Number -> Array PooledCanvas -> Array PooledCanvas
markInUseAt idx timestamp arr =
  case index arr idx of
    Nothing -> arr
    Just item ->
      case updateAt idx (item { inUse = true, lastUsed = timestamp }) arr of
        Nothing -> arr
        Just updated -> updated

-- | Release a canvas back to the pool
-- |
-- | @param pool The pool the canvas belongs to
-- | @param canvas The canvas to release
-- |
-- | @postcondition Canvas is marked as not in-use
-- | @postcondition lastUsed is updated to current time
release :: CanvasPool -> Canvas.CanvasElement -> Effect Unit
release (CanvasPool { pool: poolRef }) canvas = do
  timestamp <- nowMs
  Ref.modify_ (map \item ->
    if unsafeRefEq item.canvas canvas
      then item { inUse = false, lastUsed = timestamp }
      else item
  ) poolRef

-- | Clean up old unused canvases
-- |
-- | Removes canvases that have been unused for longer than maxAge.
-- |
-- | @param pool The pool to clean up
-- | @postcondition Old unused canvases are removed
cleanup :: CanvasPool -> Effect Unit
cleanup (CanvasPool { pool: poolRef, config }) = do
  timestamp <- nowMs
  Ref.modify_ (filter \item ->
    item.inUse || (timestamp - item.lastUsed <= config.maxAge)
  ) poolRef

-- | Clear all pooled canvases
-- |
-- | Removes all canvases from the pool. Use when shutting down
-- | or when memory pressure requires releasing all resources.
-- |
-- | @param pool The pool to clear
-- | @postcondition Pool is empty
clear :: CanvasPool -> Effect Unit
clear (CanvasPool { pool: poolRef }) =
  Ref.write [] poolRef

-- | Get pool statistics
-- |
-- | @param pool The pool to inspect
-- | @returns Statistics about pool state
getStats :: CanvasPool -> Effect PoolStats
getStats (CanvasPool { pool: poolRef }) = do
  items <- Ref.read poolRef
  let total = length items
  let inUseCount = length (filter _.inUse items)
  pure
    { total
    , inUse: inUseCount
    , available: total - inUseCount
    }
