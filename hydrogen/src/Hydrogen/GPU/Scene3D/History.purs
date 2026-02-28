-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // scene3d // history
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | History — Undo/Redo system using command pattern.
-- |
-- | ## Design
-- |
-- | The history system stores reversible commands:
-- | - Each command knows how to apply and unapply itself
-- | - Undo pops from undo stack, pushes to redo stack
-- | - Redo pops from redo stack, pushes to undo stack
-- | - New commands clear the redo stack (branch point)
-- |
-- | ## Command Pattern Benefits
-- |
-- | - Commands are pure data (serializable, debuggable)
-- | - Full history is inspectable
-- | - Can compress/coalesce similar commands
-- | - Supports selective undo (future)
-- |
-- | ## Three.js / Cinema4D Parity
-- |
-- | Cinema4D undo system features:
-- | - Grouped operations (begin/end group)
-- | - Named undo entries
-- | - Undo limit (memory management)
-- |
-- | ## Proof Reference
-- |
-- | - undo (apply command) >> redo = identity
-- | - Commands form a monoid under composition

module Hydrogen.GPU.Scene3D.History
  ( -- * Types
    Command
  , History
  , CommandGroup
  
  -- * Command Construction
  , command
  , commandNamed
  
  -- * History Construction
  , emptyHistory
  , historyWithLimit
  
  -- * History Operations
  , pushCommand
  , undo
  , redo
  , canUndo
  , canRedo
  
  -- * Command Groups
  , beginGroup
  , endGroup
  , inGroup
  
  -- * Inspection
  , undoStackSize
  , redoStackSize
  , lastCommandName
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , not
  , map
  , (<>)
  , (-)
  , (>)
  , (>=)
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array as Array
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // command
-- ═════════════════════════════════════════════════════════════════════════════

-- | A reversible command that can be applied and unapplied.
-- |
-- | The `state` type parameter is the state being modified (e.g., SceneGraph).
-- |
-- | Commands are pure: they describe the transformation without performing it.
-- | The actual application happens in the history operations.
type Command state =
  { name :: String
  , apply :: state -> state      -- Forward operation
  , unapply :: state -> state    -- Reverse operation
  }

-- | Create a command with apply/unapply functions.
command :: forall state. (state -> state) -> (state -> state) -> Command state
command applyFn unapplyFn =
  { name: "Command"
  , apply: applyFn
  , unapply: unapplyFn
  }

-- | Create a named command.
commandNamed :: forall state. String -> (state -> state) -> (state -> state) -> Command state
commandNamed name applyFn unapplyFn =
  { name: name
  , apply: applyFn
  , unapply: unapplyFn
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // command group
-- ═════════════════════════════════════════════════════════════════════════════

-- | A group of commands that undo/redo together as one unit.
type CommandGroup state =
  { name :: String
  , commands :: Array (Command state)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // history
-- ═════════════════════════════════════════════════════════════════════════════

-- | The undo/redo history state.
-- |
-- | - undoStack: Commands that can be undone (most recent first)
-- | - redoStack: Commands that can be redone (most recent first)
-- | - currentGroup: Commands being collected into a group
-- | - maxSize: Maximum undo stack size (0 = unlimited)
type History state =
  { undoStack :: Array (Command state)
  , redoStack :: Array (Command state)
  , currentGroup :: Maybe (CommandGroup state)
  , maxSize :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // history construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an empty history with no undo limit.
emptyHistory :: forall state. History state
emptyHistory =
  { undoStack: []
  , redoStack: []
  , currentGroup: Nothing
  , maxSize: 0  -- 0 means unlimited
  }

-- | Create an empty history with a maximum undo stack size.
historyWithLimit :: forall state. Int -> History state
historyWithLimit limit =
  { undoStack: []
  , redoStack: []
  , currentGroup: Nothing
  , maxSize: limit
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // history operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Push a command onto the history and apply it to the state.
-- |
-- | - If in a group, adds to current group instead of undo stack
-- | - Clears the redo stack (new branch point)
-- | - Enforces max stack size if set
pushCommand :: forall state. Command state -> History state -> state -> Tuple (History state) state
pushCommand cmd history state =
  let
    -- Apply the command
    newState = cmd.apply state
    
    -- Update history based on grouping state
    newHistory = case history.currentGroup of
      -- In a group: add to current group
      Just group ->
        history { currentGroup = Just (group { commands = Array.snoc group.commands cmd }) }
      
      -- Not in a group: add to undo stack
      Nothing ->
        let
          -- Push to undo stack
          newUndoStack = Array.cons cmd history.undoStack
          
          -- Enforce size limit
          limitedStack = if history.maxSize > 0 && Array.length newUndoStack > history.maxSize
            then Array.take history.maxSize newUndoStack
            else newUndoStack
        in
          history
            { undoStack = limitedStack
            , redoStack = []  -- Clear redo on new command
            }
  in
    Tuple newHistory newState

-- | Undo the last command.
-- |
-- | Returns Nothing if no commands to undo.
undo :: forall state. History state -> state -> Maybe (Tuple (History state) state)
undo history state =
  case Array.uncons history.undoStack of
    Nothing -> Nothing
    Just { head: cmd, tail: rest } ->
      let
        newState = cmd.unapply state
        newHistory = history
          { undoStack = rest
          , redoStack = Array.cons cmd history.redoStack
          }
      in
        Just (Tuple newHistory newState)

-- | Redo the last undone command.
-- |
-- | Returns Nothing if no commands to redo.
redo :: forall state. History state -> state -> Maybe (Tuple (History state) state)
redo history state =
  case Array.uncons history.redoStack of
    Nothing -> Nothing
    Just { head: cmd, tail: rest } ->
      let
        newState = cmd.apply state
        newHistory = history
          { undoStack = Array.cons cmd history.undoStack
          , redoStack = rest
          }
      in
        Just (Tuple newHistory newState)

-- | Check if undo is available.
canUndo :: forall state. History state -> Boolean
canUndo history = not (Array.null history.undoStack)

-- | Check if redo is available.
canRedo :: forall state. History state -> Boolean
canRedo history = not (Array.null history.redoStack)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // command groups
-- ═════════════════════════════════════════════════════════════════════════════

-- | Begin a command group.
-- |
-- | All commands pushed until endGroup are collected into one undo entry.
beginGroup :: forall state. String -> History state -> History state
beginGroup name history =
  history { currentGroup = Just { name: name, commands: [] } }

-- | End a command group and push it to the undo stack.
-- |
-- | The group becomes a single undo entry that undoes all contained commands.
endGroup :: forall state. History state -> History state
endGroup history =
  case history.currentGroup of
    Nothing -> history  -- Not in a group
    Just group ->
      if Array.null group.commands
        then history { currentGroup = Nothing }  -- Empty group, discard
        else
          let
            -- Create a compound command that applies/unapplies all in sequence
            compoundCmd = compoundCommand group.name group.commands
            
            newUndoStack = Array.cons compoundCmd history.undoStack
            
            limitedStack = if history.maxSize > 0 && Array.length newUndoStack > history.maxSize
              then Array.take history.maxSize newUndoStack
              else newUndoStack
          in
            history
              { undoStack = limitedStack
              , redoStack = []
              , currentGroup = Nothing
              }

-- | Check if currently in a group.
inGroup :: forall state. History state -> Boolean
inGroup history = case history.currentGroup of
  Nothing -> false
  Just _ -> true

-- | Create a compound command from a list of commands.
-- |
-- | Apply: executes commands in order
-- | Unapply: executes unapply in reverse order
compoundCommand :: forall state. String -> Array (Command state) -> Command state
compoundCommand name cmds =
  { name: name
  , apply: \state -> Array.foldl (\s cmd -> cmd.apply s) state cmds
  , unapply: \state -> Array.foldr (\cmd s -> cmd.unapply s) state cmds
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // inspection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the size of the undo stack.
undoStackSize :: forall state. History state -> Int
undoStackSize history = Array.length history.undoStack

-- | Get the size of the redo stack.
redoStackSize :: forall state. History state -> Int
redoStackSize history = Array.length history.redoStack

-- | Get the name of the last command (for UI display).
lastCommandName :: forall state. History state -> Maybe String
lastCommandName history = 
  map (\cmd -> cmd.name) (Array.head history.undoStack)

