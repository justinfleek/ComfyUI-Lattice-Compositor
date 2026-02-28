-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // state // atom
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Atomic state management inspired by Jotai/Recoil
-- |
-- | Atoms are the smallest unit of state. They can be read, written, and
-- | subscribed to. Derived atoms compute values from other atoms.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.State.Atom as Atom
-- |
-- | -- Create an atom
-- | countAtom <- Atom.atom 0
-- |
-- | -- Read value
-- | count <- Atom.get countAtom
-- |
-- | -- Update value
-- | Atom.set countAtom 5
-- | Atom.modify countAtom (_ + 1)
-- |
-- | -- Subscribe to changes
-- | unsubscribe <- Atom.subscribe countAtom \newValue ->
-- |   Console.log $ "Count changed to: " <> show newValue
-- |
-- | -- Derived atoms
-- | doubledAtom <- Atom.derived countAtom (\n -> n * 2)
-- | ```
module Hydrogen.State.Atom
  ( -- * Atom Types
    Atom
  , ReadOnlyAtom
  , AtomStore
    -- * Atom Creation
  , atom
  , atomWithKey
  , derived
  , derivedFrom2
  , derivedFrom3
  , asyncAtom
    -- * Atom Operations
  , get
  , set
  , modify
  , reset
    -- * Subscriptions
  , subscribe
  , subscribeWithPrevious
    -- * Store Management
  , newStore
  , snapshot
  , restore
    -- * Utilities
  , toReadOnly
  , onChange
  ) where

import Prelude

import Data.Array as Array
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Tuple (Tuple(Tuple))
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subscriber with ID for tracking
type AtomSubscriber a = { id :: Int, callback :: a -> Effect Unit }

-- | An atom holds a single piece of state
newtype Atom a = Atom
  { ref :: Ref a
  , initial :: a
  , key :: Maybe String
  , subscribers :: Ref (Array (AtomSubscriber a))
  , nextId :: Ref Int
  }

-- | A read-only view of an atom (for derived atoms exposed publicly)
newtype ReadOnlyAtom a = ReadOnlyAtom (Atom a)

-- | A store holds multiple atoms and enables snapshots
newtype AtomStore = AtomStore
  { atoms :: Ref (Map.Map String (Ref String))  -- Serialized snapshots
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // atom creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a new atom with an initial value
atom :: forall a. a -> Effect (Atom a)
atom initial = do
  ref <- Ref.new initial
  subscribers <- Ref.new []
  nextId <- Ref.new 0
  pure $ Atom { ref, initial, key: Nothing, subscribers, nextId }

-- | Create an atom with a key for persistence/debugging
atomWithKey :: forall a. String -> a -> Effect (Atom a)
atomWithKey key initial = do
  ref <- Ref.new initial
  subscribers <- Ref.new []
  nextId <- Ref.new 0
  pure $ Atom { ref, initial, key: Just key, subscribers, nextId }

-- | Create a derived atom that computes from another atom
derived :: forall a b. Atom a -> (a -> b) -> Effect (ReadOnlyAtom b)
derived (Atom source) f = do
  -- Get initial derived value
  sourceVal <- Ref.read source.ref
  let initialDerived = f sourceVal
  
  -- Create the derived atom
  derivedRef <- Ref.new initialDerived
  derivedSubs <- Ref.new []
  derivedNextId <- Ref.new 0
  
  -- Subscribe to source changes
  let updateDerived newSource = do
        let newDerived = f newSource
        Ref.write newDerived derivedRef
        subs <- Ref.read derivedSubs
        for_ subs \sub -> sub.callback newDerived
  
  -- Add subscription to source
  sourceId <- Ref.read source.nextId
  Ref.write (sourceId + 1) source.nextId
  Ref.modify_ (Array.cons { id: sourceId, callback: updateDerived }) source.subscribers
  
  pure $ ReadOnlyAtom $ Atom
    { ref: derivedRef
    , initial: initialDerived
    , key: Nothing
    , subscribers: derivedSubs
    , nextId: derivedNextId
    }
  where
  for_ arr f' = void $ Array.foldM (\_ x -> f' x) unit arr

-- | Create a derived atom from two source atoms
derivedFrom2 :: forall a b c. Atom a -> Atom b -> (a -> b -> c) -> Effect (ReadOnlyAtom c)
derivedFrom2 (Atom s1) (Atom s2) f = do
  v1 <- Ref.read s1.ref
  v2 <- Ref.read s2.ref
  let initialDerived = f v1 v2
  
  derivedRef <- Ref.new initialDerived
  derivedSubs <- Ref.new []
  derivedNextId <- Ref.new 0
  
  let doUpdate = do
        newV1 <- Ref.read s1.ref
        newV2 <- Ref.read s2.ref
        let newDerived = f newV1 newV2
        Ref.write newDerived derivedRef
        subs <- Ref.read derivedSubs
        for_ subs \sub -> sub.callback newDerived
  
  -- Subscribe to both sources with typed callbacks
  id1 <- Ref.read s1.nextId
  Ref.write (id1 + 1) s1.nextId
  Ref.modify_ (Array.cons { id: id1, callback: \(_ :: a) -> doUpdate }) s1.subscribers
  
  id2 <- Ref.read s2.nextId
  Ref.write (id2 + 1) s2.nextId
  Ref.modify_ (Array.cons { id: id2, callback: \(_ :: b) -> doUpdate }) s2.subscribers
  
  pure $ ReadOnlyAtom $ Atom
    { ref: derivedRef
    , initial: initialDerived
    , key: Nothing
    , subscribers: derivedSubs
    , nextId: derivedNextId
    }
  where
  for_ arr f' = void $ Array.foldM (\_ x -> f' x) unit arr

-- | Create a derived atom from three source atoms
derivedFrom3 :: forall a b c d. Atom a -> Atom b -> Atom c -> (a -> b -> c -> d) -> Effect (ReadOnlyAtom d)
derivedFrom3 (Atom s1) (Atom s2) (Atom s3) f = do
  v1 <- Ref.read s1.ref
  v2 <- Ref.read s2.ref
  v3 <- Ref.read s3.ref
  let initialDerived = f v1 v2 v3
  
  derivedRef <- Ref.new initialDerived
  derivedSubs <- Ref.new []
  derivedNextId <- Ref.new 0
  
  let doUpdate = do
        newV1 <- Ref.read s1.ref
        newV2 <- Ref.read s2.ref
        newV3 <- Ref.read s3.ref
        let newDerived = f newV1 newV2 newV3
        Ref.write newDerived derivedRef
        subs <- Ref.read derivedSubs
        for_ subs \sub -> sub.callback newDerived
  
  -- Subscribe to all three sources with typed callbacks
  id1 <- Ref.read s1.nextId
  Ref.write (id1 + 1) s1.nextId
  Ref.modify_ (Array.cons { id: id1, callback: \(_ :: a) -> doUpdate }) s1.subscribers
  
  id2 <- Ref.read s2.nextId
  Ref.write (id2 + 1) s2.nextId
  Ref.modify_ (Array.cons { id: id2, callback: \(_ :: b) -> doUpdate }) s2.subscribers
  
  id3 <- Ref.read s3.nextId
  Ref.write (id3 + 1) s3.nextId
  Ref.modify_ (Array.cons { id: id3, callback: \(_ :: c) -> doUpdate }) s3.subscribers
  
  pure $ ReadOnlyAtom $ Atom
    { ref: derivedRef
    , initial: initialDerived
    , key: Nothing
    , subscribers: derivedSubs
    , nextId: derivedNextId
    }
  where
  for_ arr f' = void $ Array.foldM (\_ x -> f' x) unit arr

-- | Create an async atom that fetches data
asyncAtom :: forall a. a -> Aff a -> Effect (Atom a)
asyncAtom initial fetchFn = do
  atomRef <- atom initial
  -- Kick off the fetch
  launchAff_ do
    result <- fetchFn
    liftEffect $ set atomRef result
  pure atomRef

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // atom operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value of an atom
get :: forall a. Atom a -> Effect a
get (Atom { ref }) = Ref.read ref

-- | Set the value of an atom
set :: forall a. Atom a -> a -> Effect Unit
set (Atom { ref, subscribers }) newValue = do
  Ref.write newValue ref
  subs <- Ref.read subscribers
  for_ subs \sub -> sub.callback newValue
  where
  for_ arr f = void $ Array.foldM (\_ x -> f x) unit arr

-- | Modify the value of an atom with a function
modify :: forall a. Atom a -> (a -> a) -> Effect Unit
modify a@(Atom { ref }) f = do
  current <- Ref.read ref
  set a (f current)

-- | Reset an atom to its initial value
reset :: forall a. Atom a -> Effect Unit
reset a@(Atom { initial }) = set a initial

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // subscriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subscribe to atom changes, returns unsubscribe function
subscribe :: forall a. Atom a -> (a -> Effect Unit) -> Effect (Effect Unit)
subscribe (Atom { subscribers, nextId }) callback = do
  id <- Ref.read nextId
  Ref.write (id + 1) nextId
  let sub = { id, callback }
  Ref.modify_ (Array.cons sub) subscribers
  -- Return unsubscribe function
  pure $ Ref.modify_ (Array.filter (\s -> s.id /= id)) subscribers

-- | Subscribe with access to previous value
subscribeWithPrevious :: forall a. Atom a -> (a -> a -> Effect Unit) -> Effect (Effect Unit)
subscribeWithPrevious (Atom { ref, subscribers, nextId }) callback = do
  prevRef <- Ref.new =<< Ref.read ref
  id <- Ref.read nextId
  Ref.write (id + 1) nextId
  let wrappedCallback newVal = do
        prev <- Ref.read prevRef
        Ref.write newVal prevRef
        callback prev newVal
  let sub = { id, callback: wrappedCallback }
  Ref.modify_ (Array.cons sub) subscribers
  pure $ Ref.modify_ (Array.filter (\s -> s.id /= id)) subscribers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // store management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a new atom store
newStore :: Effect AtomStore
newStore = do
  atoms <- Ref.new Map.empty
  pure $ AtomStore { atoms }

-- | Take a snapshot of an atom's value (requires Show instance)
snapshot :: forall a. Show a => AtomStore -> Atom a -> Effect Unit
snapshot (AtomStore { atoms }) (Atom { ref, key }) = do
  case key of
    Nothing -> pure unit
    Just k -> do
      val <- Ref.read ref
      snapshotRef <- Ref.new (show val)
      Ref.modify_ (Map.insert k snapshotRef) atoms

-- | Restore atom from snapshot (requires Read instance - simplified here)
restore :: forall a. AtomStore -> Atom a -> (String -> Maybe a) -> Effect Unit
restore (AtomStore { atoms }) a@(Atom { key }) parse = do
  case key of
    Nothing -> pure unit
    Just k -> do
      atomMap <- Ref.read atoms
      case Map.lookup k atomMap of
        Nothing -> pure unit
        Just snapshotRef -> do
          serialized <- Ref.read snapshotRef
          case parse serialized of
            Nothing -> pure unit
            Just val -> set a val

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert an atom to read-only
toReadOnly :: forall a. Atom a -> ReadOnlyAtom a
toReadOnly = ReadOnlyAtom

-- | Helper to run effect when atom changes (returns cleanup)
onChange :: forall a. Atom a -> (a -> Effect Unit) -> Effect (Effect Unit)
onChange = subscribe
