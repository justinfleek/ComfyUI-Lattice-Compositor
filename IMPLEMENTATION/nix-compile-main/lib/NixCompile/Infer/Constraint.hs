{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : NixCompile.Infer.Constraint
-- Description : Generate type constraints from facts
--
-- Transforms observations (Facts) into equality constraints for unification.
-- Constraints carry source locations for error reporting.
module NixCompile.Infer.Constraint
  ( factsToConstraints,
    factToConstraints,
    factsToLocatedConstraints,
    factToLocatedConstraints,
  )
where

import NixCompile.Bash.Builtins (lookupArgType, lookupPositionalType)
import NixCompile.Types

-- | Convert all facts to located constraints (preferred API)
factsToLocatedConstraints :: [Fact] -> [LocatedConstraint]
factsToLocatedConstraints = concatMap factToLocatedConstraints

-- | Convert a single fact to located constraints
factToLocatedConstraints :: Fact -> [LocatedConstraint]
factToLocatedConstraints = \case
  --                                                                       // var
  DefaultIs var lit sp ->
    [LocatedConstraint (TVar (TypeVar var) :~: literalType lit) sp]
  --                                                                       // var
  DefaultFrom var other sp ->
    [LocatedConstraint (TVar (TypeVar var) :~: TVar (TypeVar other)) sp]
  --                                                                       // var
  Required _ _ ->
    []
  --                                                                       // var
  AssignFrom var other sp ->
    [LocatedConstraint (TVar (TypeVar var) :~: TVar (TypeVar other)) sp]
  --                                                                       // var
  AssignLit var lit sp ->
    [LocatedConstraint (TVar (TypeVar var) :~: literalType lit) sp]
  -- config.x.y = $VAR or "$VAR": no type constraint on VAR
  ConfigAssign _ _ _ _ ->
    []
  -- config.x.y = literal: no variable constraint
  ConfigLit _ _ _ ->
    []
  -- Command arg with known type: look up in builtins
  CmdArg cmd argName varName sp ->
    case lookupArgType cmd argName of
      Just ty -> [LocatedConstraint (TVar (TypeVar varName) :~: ty) sp]
      Nothing -> []
  -- Command positional arg with known type: look up in builtins
  CmdPositional cmd pos varName sp ->
    case lookupPositionalType cmd pos of
      Just ty -> [LocatedConstraint (TVar (TypeVar varName) :~: ty) sp]
      Nothing -> []
  -- Store path usage: no type constraint
  UsesStorePath _ _ ->
    []
  -- Bare command: no type constraint
  BareCommand _ _ ->
    []
  -- Dynamic command: no type constraint
  DynamicCommand _ _ ->
    []
  -- Observed variable: no type constraint
  Observed _ _ ->
    []

-- | Legacy API: Convert all facts to unlocated constraints
factsToConstraints :: [Fact] -> [Constraint]
factsToConstraints = concatMap factToConstraints

-- | Legacy API: Convert a single fact to unlocated constraints
factToConstraints :: Fact -> [Constraint]
factToConstraints fact =
  map lcConstraint (factToLocatedConstraints fact)
