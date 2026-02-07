/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.CoreM
public import Lean.Data.NameMap
public import Lean.Environment
public import Lean.Util.FoldConsts
import Batteries.Data.NameSet

public section

namespace Lean

/-- Return the name of the module in which a declaration was defined. -/
def Environment.getModuleFor? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | none =>
    if env.constants.map₂.contains declName then
      env.header.mainModule
    else
      none
  | some idx => env.header.moduleNames[idx.toNat]!

open Lean

/--
Return the names of the modules in which constants used in the specified declaration were defined.

Note that this will *not* account for tactics and syntax used in the declaration,
so the results may not suffice as imports.
-/
def Name.requiredModules (n : Name) : CoreM NameSet := do
  let env ← getEnv
  let mut requiredModules : NameSet := {}
  let ci ← getConstInfo n
  for n in ci.getUsedConstantsAsSet do
    match env.getModuleFor? n with
    | some m =>
      if ¬ (`Init).isPrefixOf m then
        requiredModules := requiredModules.insert m
    | none => pure ()
  return requiredModules

/--
Return the names of the constants used in the specified declarations,
and the constants they use transitively.
-/
def NameSet.transitivelyUsedConstants (s : NameSet) : CoreM NameSet := do
  let mut usedConstants : NameSet := {}
  let mut toProcess : NameSet := s
  while !toProcess.isEmpty do
    let arr := toProcess.toArray
    if arr.isEmpty then break
    let mut current := arr[0]!
    for i in [1:arr.size] do
      if (arr[i]!.cmp current).isLT then
        current := arr[i]!
    toProcess := toProcess.erase current
    usedConstants := usedConstants.insert current
    for m in (← getConstInfo current).getUsedConstantsAsSet do
      if !usedConstants.contains m then
        toProcess := toProcess.insert m
  return usedConstants

/--
Return the names of the constants used in the specified declaration,
and the constants they use transitively.
-/
def Name.transitivelyUsedConstants (n : Name) : CoreM NameSet :=
  NameSet.transitivelyUsedConstants {n}

/--
Return the names of the modules in which constants used transitively
in the specified declarations were defined.

Note that this will *not* account for tactics and syntax used in the declaration,
so the results may not suffice as imports.
-/
def NameSet.transitivelyRequiredModules (s : NameSet) (env : Environment) : CoreM NameSet := do
  let mut requiredModules : NameSet := {}
  for m in (← s.transitivelyUsedConstants) do
    match env.getModuleFor? m with
    | some module => requiredModules := requiredModules.insert module
    | none => pure ()
  return requiredModules

/--
Return the names of the modules in which constants used transitively
in the specified declaration were defined.

Note that this will *not* account for tactics and syntax used in the declaration,
so the results may not suffice as imports.
-/
def Name.transitivelyRequiredModules (n : Name) (env : Environment) : CoreM NameSet :=
  NameSet.transitivelyRequiredModules {n} env

/--
Finds all constants defined in the specified module,
and identifies all modules containing constants which are transitively required by those constants.
-/
def Environment.transitivelyRequiredModules (env : Environment) (module : Name) : CoreM NameSet := do
  let constants := env.constants.map₁.values.map (·.name)
    |>.filter (! ·.isInternal)
    |>.filter (fun n => env.getModuleFor? n == some module)
  (NameSet.ofList constants).transitivelyRequiredModules env

/--
Computes all the modules transitively required by the specified modules.
Should be equivalent to calling `transitivelyRequiredModules` on each module, but shares more of the work.
-/
partial def Environment.transitivelyRequiredModules' (env : Environment) (modules : List Name) (verbose : Bool := false) :
    CoreM (NameMap NameSet) := do
  let N := env.header.moduleNames.size
  let mut c2m : NameMap (BitVec N) := {}
  let mut pushed : NameSet := {}
  let mut result : NameMap NameSet := {}
  for m in modules do
    if verbose then
      IO.println s!"Processing module {m}"
    match env.header.moduleNames.idxOf? m with
    | none =>
      -- Module not found, skip with empty result
      result := result.insert m {}
    | some moduleIdx =>
      let mut r : BitVec N := 0
      for n in env.header.moduleData[moduleIdx]!.constNames do
        if ! n.isInternal then
        -- This is messy: Mathlib is big enough that writing a recursive function causes a stack overflow.
        -- So we use an explicit stack instead. We visit each constant twice:
        -- once to record the constants transitively used by it,
        -- and again to record the modules which defined those constants.
        let mut stack : List (Name × NameSet) := [⟨n, {}⟩]
        pushed := pushed.insert n
        while !stack.isEmpty do
          match stack with
          | [] => 
            -- Unreachable: stack.isEmpty check prevents this, but compiler requires exhaustive match
            break
          | (c, used) :: tail =>
            stack := tail
            if used.isEmpty then
              -- First visit: collect used constants
              if !c2m.contains c then
                let usedConstants := (← getConstInfo c).getUsedConstantsAsSet
                stack := ⟨c, usedConstants⟩ :: stack
                for u in usedConstants do
                  if !pushed.contains u then
                    stack := ⟨u, {}⟩ :: stack
                    pushed := pushed.insert u
            else
              -- Second visit: compute modules and transitive dependencies
              let usedModules : NameSet :=
                used.foldl (init := {}) (fun s u => 
                  match env.getModuleFor? u with
                  | some m => s.insert m
                  | none => s)
              let transitivelyUsed : BitVec N :=
                used.foldl (init := toBitVec usedModules) (fun s u => 
                  s ||| ((c2m.find? u).getD (0 : BitVec N)))
              c2m := c2m.insert c transitivelyUsed
        r := r ||| ((c2m.find? n).getD (0 : BitVec N))
      result := result.insert m (toNameSet r)
  return result
where
  toBitVec {N : Nat} (s : NameSet) : BitVec N :=
    s.foldl (init := (0 : BitVec N)) (fun b n => 
      match env.header.moduleNames.idxOf? n with
      | some idx => b ||| BitVec.twoPow _ idx
      | none => b)
  toNameSet {N : Nat} (b : BitVec N) : NameSet :=
    env.header.moduleNames.zipIdx.foldl (init := {}) (fun s (n, i) => if b.getLsbD i then s.insert n else s)

/--
Return the names of the modules in which constants used in the current file were defined.

Note that this will *not* account for tactics and syntax used in the file,
so the results may not suffice as imports.
-/
def Environment.requiredModules (env : Environment) : NameSet := Id.run do
  let localConstantInfos := env.constants.map₂
  let mut requiredModules : NameSet := {}
  for (_, ci) in localConstantInfos do
    for n in ci.getUsedConstantsAsSet do
      match env.getModuleFor? n with
      | some m =>
        if ¬ (`Init).isPrefixOf m then
          requiredModules := requiredModules.insert m
      | none => pure ()
  return requiredModules

end Lean

end section
