/-
Toolchain Types - Continuity Build System
==========================================

Typed toolchain definitions from continuity.lean Section 3.
NO STRING-TYPED FLAGS. All configuration is typed.

Reference: NEWSYSTEM/continuity.lean lines 226-275
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic

namespace Continuity.Toolchain

/-!
## Hash and StorePath (Atoms from Section 1)
-/

/-- A SHA256 hash. The basis of content-addressing. -/
structure Hash where
  bytes : Fin 32 -> UInt8
  deriving DecidableEq, Repr

/-- Content-addressed store path -/
structure StorePath where
  hash : Hash
  name : String
  deriving DecidableEq

instance : Inhabited StorePath where
  default := { hash := { bytes := fun _ => 0 }, name := "" }

/-!
## CPU Architecture
-/

/-- CPU architecture -/
inductive Arch where
  | x86_64   -- Intel/AMD 64-bit
  | aarch64  -- ARM 64-bit
  | wasm32   -- WebAssembly 32-bit
  | riscv64  -- RISC-V 64-bit
  deriving DecidableEq, Repr, Inhabited

/-- Convert architecture to string representation -/
def Arch.toString : Arch -> String
  | .x86_64  => "x86_64"
  | .aarch64 => "aarch64"
  | .wasm32  => "wasm32"
  | .riscv64 => "riscv64"

/-- Parse architecture from string -/
def Arch.fromString (s : String) : Option Arch :=
  match s with
  | "x86_64"  => some .x86_64
  | "aarch64" => some .aarch64
  | "wasm32"  => some .wasm32
  | "riscv64" => some .riscv64
  | _         => none

/-!
## Operating System
-/

/-- Operating system -/
inductive OS where
  | linux   -- Linux kernel
  | darwin  -- macOS/iOS
  | wasi    -- WebAssembly System Interface
  | none    -- Bare metal / freestanding
  deriving DecidableEq, Repr, Inhabited

/-- Convert OS to string representation -/
def OS.toString : OS -> String
  | .linux  => "linux"
  | .darwin => "darwin"
  | .wasi   => "wasi"
  | .none   => "none"

/-- Parse OS from string -/
def OS.fromString (s : String) : Option OS :=
  match s with
  | "linux"  => some .linux
  | "darwin" => some .darwin
  | "wasi"   => some .wasi
  | "none"   => some .none
  | _        => none

/-!
## Target Triple
-/

/-- Target triple: arch-os-abi -/
structure Triple where
  arch : Arch
  os : OS
  abi : String
  deriving DecidableEq

instance : Inhabited Triple where
  default := { arch := .x86_64, os := .linux, abi := "gnu" }

/-- Convert triple to string (e.g., "x86_64-linux-gnu") -/
def Triple.toString (t : Triple) : String :=
  s!"{t.arch.toString}-{t.os.toString}-{t.abi}"

/-- Common host triple for Linux x86_64 -/
def Triple.linuxX86_64 : Triple :=
  { arch := .x86_64, os := .linux, abi := "gnu" }

/-- Common host triple for macOS ARM -/
def Triple.darwinAarch64 : Triple :=
  { arch := .aarch64, os := .darwin, abi := "" }

/-- Common target triple for WASM -/
def Triple.wasm32Wasi : Triple :=
  { arch := .wasm32, os := .wasi, abi := "" }

/-!
## Optimization Level
-/

/-- Optimization level -/
inductive OptLevel where
  | O0  -- No optimization (debug)
  | O1  -- Basic optimization
  | O2  -- Standard optimization
  | O3  -- Aggressive optimization
  | Oz  -- Optimize for size (aggressive)
  | Os  -- Optimize for size
  deriving DecidableEq, Repr, Inhabited

/-- Convert optimization level to compiler flag string -/
def OptLevel.toFlag : OptLevel -> String
  | .O0 => "-O0"
  | .O1 => "-O1"
  | .O2 => "-O2"
  | .O3 => "-O3"
  | .Oz => "-Oz"
  | .Os => "-Os"

/-- Parse optimization level from string -/
def OptLevel.fromString (s : String) : Option OptLevel :=
  match s with
  | "-O0" | "O0" | "0" => some .O0
  | "-O1" | "O1" | "1" => some .O1
  | "-O2" | "O2" | "2" => some .O2
  | "-O3" | "O3" | "3" => some .O3
  | "-Oz" | "Oz" | "z" => some .Oz
  | "-Os" | "Os" | "s" => some .Os
  | _                  => none

/-!
## Link-Time Optimization Mode
-/

/-- Link-time optimization mode -/
inductive LTOMode where
  | off   -- No LTO
  | thin  -- ThinLTO (faster, parallel)
  | fat   -- Full LTO (slower, better optimization)
  deriving DecidableEq, Repr, Inhabited

/-- Convert LTO mode to compiler flag string -/
def LTOMode.toFlag : LTOMode -> String
  | .off  => ""
  | .thin => "-flto=thin"
  | .fat  => "-flto=full"

/-- Parse LTO mode from string -/
def LTOMode.fromString (s : String) : Option LTOMode :=
  match s with
  | "off" | "" | "none"       => some .off
  | "thin" | "-flto=thin"     => some .thin
  | "fat" | "full" | "-flto=full" | "-flto" => some .fat
  | _                         => none

/-!
## Typed Compiler Flags

NO STRING-TYPED FLAGS. Every flag is a typed union.
-/

/-- Typed compiler flags -/
inductive Flag where
  | optLevel : OptLevel -> Flag     -- Optimization level
  | lto : LTOMode -> Flag           -- Link-time optimization
  | targetCpu : String -> Flag      -- Target CPU (e.g., "native", "skylake")
  | debug : Bool -> Flag            -- Debug symbols
  | pic : Bool -> Flag              -- Position-independent code
  deriving DecidableEq, Repr

/-- Convert flag to compiler argument(s) -/
def Flag.toArgs : Flag -> List String
  | .optLevel opt => [opt.toFlag]
  | .lto mode     => if mode.toFlag.isEmpty then [] else [mode.toFlag]
  | .targetCpu cpu => [s!"-mcpu={cpu}"]
  | .debug true   => ["-g"]
  | .debug false  => []
  | .pic true     => ["-fPIC"]
  | .pic false    => ["-fno-PIC"]

/-- Extract optimization level from flags if present -/
def Flag.getOptLevel : Flag -> Option OptLevel
  | .optLevel opt => some opt
  | _             => none

/-- Extract LTO mode from flags if present -/
def Flag.getLTO : Flag -> Option LTOMode
  | .lto mode => some mode
  | _         => none

/-- Check if flag enables debug symbols -/
def Flag.isDebug : Flag -> Bool
  | .debug b => b
  | _        => false

/-!
## Toolchain

Compiler + target + flags = toolchain.
-/

/-- A toolchain: compiler + target + flags -/
structure Toolchain where
  compiler : StorePath
  host : Triple
  target : Triple
  flags : List Flag
  sysroot : Option StorePath
  deriving DecidableEq

instance : Inhabited Toolchain where
  default := {
    compiler := default,
    host := Triple.linuxX86_64,
    target := Triple.linuxX86_64,
    flags := [],
    sysroot := none
  }

/-!
## Toolchain Utilities
-/

/-- Get all compiler arguments from toolchain flags -/
def Toolchain.getCompilerArgs (t : Toolchain) : List String :=
  t.flags.flatMap Flag.toArgs

/-- Check if toolchain is cross-compiling -/
def Toolchain.isCrossCompile (t : Toolchain) : Bool :=
  t.host != t.target

/-- Check if toolchain has debug symbols enabled -/
def Toolchain.hasDebug (t : Toolchain) : Bool :=
  t.flags.any Flag.isDebug

/-- Get optimization level from toolchain (defaults to O0) -/
def Toolchain.getOptLevel (t : Toolchain) : OptLevel :=
  t.flags.filterMap Flag.getOptLevel |>.head? |>.getD .O0

/-- Get LTO mode from toolchain (defaults to off) -/
def Toolchain.getLTOMode (t : Toolchain) : LTOMode :=
  t.flags.filterMap Flag.getLTO |>.head? |>.getD .off

/-!
## Validation
-/

/-- Validation result -/
inductive ValidationResult where
  | valid
  | invalid : String -> ValidationResult
  deriving DecidableEq, Repr

/-- Validate toolchain configuration -/
def Toolchain.validate (t : Toolchain) : ValidationResult :=
  -- Check for conflicting optimization flags
  let optLevels := t.flags.filterMap Flag.getOptLevel
  if optLevels.length > 1 then
    .invalid "Multiple optimization levels specified"
  -- Check for conflicting LTO modes
  else
    let ltoModes := t.flags.filterMap Flag.getLTO
    if ltoModes.length > 1 then
      .invalid "Multiple LTO modes specified"
    -- WASM targets can't use PIC
    else if t.target.arch == .wasm32 && t.flags.any (fun f => match f with | .pic true => true | _ => false) then
      .invalid "WASM targets do not support position-independent code"
    else
      .valid

/-- Check if toolchain is valid -/
def Toolchain.isValid (t : Toolchain) : Bool :=
  match t.validate with
  | .valid => true
  | .invalid _ => false

/-!
## Theorems
-/

/-- Arch parsing roundtrip -/
theorem arch_roundtrip (a : Arch) : Arch.fromString (Arch.toString a) = some a := by
  cases a <;> rfl

/-- OS parsing roundtrip -/
theorem os_roundtrip (o : OS) : OS.fromString (OS.toString o) = some o := by
  cases o <;> rfl

/-- OptLevel parsing roundtrip (using flag format) -/
theorem optlevel_roundtrip (opt : OptLevel) : OptLevel.fromString (opt.toFlag) = some opt := by
  cases opt <;> rfl

end Continuity.Toolchain
