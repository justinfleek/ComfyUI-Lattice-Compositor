-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // debounce
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rate limiting utilities
-- |
-- | Debounce and throttle functions for controlling execution frequency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Debounce as Debounce
-- |
-- | -- Debounce search input (trailing edge by default)
-- | debouncedSearch <- Debounce.debounce (Milliseconds 300.0) \query ->
-- |   performSearch query
-- |
-- | -- Now use debouncedSearch instead of performSearch
-- | debouncedSearch "hello"  -- Called after 300ms of inactivity
-- |
-- | -- Throttle scroll handler
-- | throttledScroll <- Debounce.throttle (Milliseconds 100.0) \_ ->
-- |   updateScrollPosition
-- |
-- | -- Leading edge debounce (execute immediately, then debounce)
-- | immediate <- Debounce.debounceLeading (Milliseconds 300.0) \_ ->
-- |   doSomething
-- |
-- | -- Cancel pending calls
-- | cancelFn <- Debounce.debounceWithCancel (Milliseconds 300.0) handler
-- | cancelFn.cancel  -- Cancel any pending execution
-- | ```
module Hydrogen.Util.Debounce
  ( -- * Core Functions
    debounce
  , throttle
    -- * Edge Options
  , debounceLeading
  , debounceTrailing
  , debounceBoth
  , throttleLeading
  , throttleTrailing
    -- * With Cancel
  , debounceWithCancel
  , throttleWithCancel
  , Cancellable
    -- * Types
  , Milliseconds(..)
  ) where

import Prelude

import Effect (Effect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duration in milliseconds
newtype Milliseconds = Milliseconds Number

derive instance eqMilliseconds :: Eq Milliseconds
derive instance ordMilliseconds :: Ord Milliseconds

instance showMilliseconds :: Show Milliseconds where
  show (Milliseconds n) = show n <> "ms"

-- | Cancellable debounced/throttled function
type Cancellable a =
  { call :: a -> Effect Unit
  , cancel :: Effect Unit
  , flush :: Effect Unit
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import debounceImpl
  :: forall a
   . Number
  -> Boolean  -- leading
  -> Boolean  -- trailing
  -> (a -> Effect Unit)
  -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }

foreign import throttleImpl
  :: forall a
   . Number
  -> Boolean  -- leading
  -> Boolean  -- trailing
  -> (a -> Effect Unit)
  -> Effect { call :: a -> Effect Unit, cancel :: Effect Unit, flush :: Effect Unit }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // core functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debounce a function (trailing edge)
-- |
-- | The function will only be called after the specified time has passed
-- | without any new calls.
-- |
-- | ```purescript
-- | debouncedFn <- debounce (Milliseconds 300.0) myHandler
-- | debouncedFn "a"  -- Ignored
-- | debouncedFn "b"  -- Ignored
-- | debouncedFn "c"  -- Called with "c" after 300ms of no calls
-- | ```
debounce :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
debounce (Milliseconds ms) fn = do
  result <- debounceImpl ms false true fn
  pure result.call

-- | Throttle a function
-- |
-- | The function will be called at most once per time period.
-- |
-- | ```purescript
-- | throttledFn <- throttle (Milliseconds 100.0) myHandler
-- | -- Even if called rapidly, executes at most once per 100ms
-- | ```
throttle :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
throttle (Milliseconds ms) fn = do
  result <- throttleImpl ms true true fn
  pure result.call

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // edge options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debounce with leading edge
-- |
-- | Executes immediately on first call, then debounces subsequent calls.
debounceLeading :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
debounceLeading (Milliseconds ms) fn = do
  result <- debounceImpl ms true false fn
  pure result.call

-- | Debounce with trailing edge (same as debounce)
debounceTrailing :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
debounceTrailing = debounce

-- | Debounce with both leading and trailing edges
-- |
-- | Executes immediately and also after the debounce period.
debounceBoth :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
debounceBoth (Milliseconds ms) fn = do
  result <- debounceImpl ms true true fn
  pure result.call

-- | Throttle with leading edge only
-- |
-- | Executes immediately, ignores calls during the throttle period.
throttleLeading :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
throttleLeading (Milliseconds ms) fn = do
  result <- throttleImpl ms true false fn
  pure result.call

-- | Throttle with trailing edge only
-- |
-- | Queues one call to execute after the throttle period.
throttleTrailing :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (a -> Effect Unit)
throttleTrailing (Milliseconds ms) fn = do
  result <- throttleImpl ms false true fn
  pure result.call

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // with cancel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debounce with cancel and flush capabilities
-- |
-- | ```purescript
-- | fns <- debounceWithCancel (Milliseconds 300.0) myHandler
-- | fns.call "value"  -- Queue a call
-- | fns.cancel        -- Cancel pending call
-- | fns.flush         -- Execute pending call immediately
-- | ```
debounceWithCancel :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (Cancellable a)
debounceWithCancel (Milliseconds ms) fn = debounceImpl ms false true fn

-- | Throttle with cancel and flush capabilities
throttleWithCancel :: forall a. Milliseconds -> (a -> Effect Unit) -> Effect (Cancellable a)
throttleWithCancel (Milliseconds ms) fn = throttleImpl ms true true fn
