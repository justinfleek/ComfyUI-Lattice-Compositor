/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                  HYDROGEN // SCHEMA // GPU // STORABLE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Proven invariants for GPUStorable — serialization roundtrip correctness.
  
  PURPOSE:
    At billion-agent scale, agents communicate by serializing Schema atoms to
    GPU-native byte formats. The roundtrip property guarantees:
    
    1. Lossless transmission: deserialize(serialize(x)) = x
    2. Determinism: same value always produces same bytes
    3. Alignment correctness: byte layout matches WebGPU spec
    
  WHY THIS MATTERS:
  
    When Agent A serializes a Vec3 and Agent B deserializes it, B must get
    EXACTLY the same value. Not "close enough" — identical. Without this:
    
    - Floating-point drift accumulates across relay chains
    - Cache keys (UUID5 of bytes) diverge for identical values
    - Distributed rendering produces inconsistent output
    
  INVARIANTS PROVEN:
  
    1. roundtrip: ∀ x, deserialize (serialize x) = some x
    2. deterministic: ∀ x, serialize x = serialize x
    3. size_consistent: ∀ x, length (serialize x) = byteSize x
    4. alignment_valid: ∀ x, byteSize x % alignment x = 0
  
  REFERENCES:
  
  - Hydrogen.Schema.GPU.Storable (PureScript implementation)
  - WebGPU WGSL Alignment Rules (w3.org/TR/WGSL/#alignment)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Hydrogen.Schema.GPU.Storable

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BYTE ARRAY FOUNDATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A byte is a natural number in [0, 255]. -/
abbrev Byte := Fin 256

/-- A byte array is a list of bytes. -/
abbrev ByteArray := List Byte

/-- Memory alignment (power of 2). -/
inductive Alignment
  | align4  : Alignment  -- 4-byte (f32, i32, u32)
  | align8  : Alignment  -- 8-byte (vec2<f32>, f64)
  | align16 : Alignment  -- 16-byte (vec3<f32>, vec4<f32>, mat4x4<f32>)
  deriving Repr, DecidableEq

/-- Convert alignment to byte count. -/
def Alignment.toNat : Alignment → ℕ
  | .align4 => 4
  | .align8 => 8
  | .align16 => 16

/-- THEOREM: Alignment is always positive -/
theorem alignment_pos (a : Alignment) : a.toNat > 0 := by
  cases a <;> simp [Alignment.toNat]

/-- THEOREM: Alignment is always a power of 2 -/
theorem alignment_pow2 (a : Alignment) : ∃ n : ℕ, a.toNat = 2^n := by
  cases a with
  | align4 => exact ⟨2, rfl⟩
  | align8 => exact ⟨3, rfl⟩
  | align16 => exact ⟨4, rfl⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: GPUSTORABLE TYPECLASS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Typeclass for types that can be serialized to GPU buffers.

    Laws:
    1. roundtrip: fromBytes (toBytes x) = some x
    2. size: (toBytes x).length = byteSize
    3. alignment: byteSize % alignment.toNat = 0
-/
class GPUStorable (α : Type*) where
  byteSize : ℕ
  alignment : Alignment
  toBytes : α → ByteArray
  fromBytes : ByteArray → Option α
  -- Laws (must be proven for each instance)
  roundtrip : ∀ x, fromBytes (toBytes x) = some x
  size_correct : ∀ x, (toBytes x).length = byteSize
  alignment_correct : byteSize % alignment.toNat = 0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BOUNDED INTEGER SERIALIZATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Serialize a natural number < 2^32 to 4 bytes (little-endian). -/
def natToBytes4 (n : ℕ) : ByteArray :=
  let n' := n % (2^32)  -- Ensure bounded
  [ ⟨n' % 256, by omega⟩,
    ⟨(n' / 256) % 256, by omega⟩,
    ⟨(n' / 65536) % 256, by omega⟩,
    ⟨(n' / 16777216) % 256, by omega⟩ ]

/-- Deserialize 4 bytes to a natural number. -/
def bytes4ToNat (bs : ByteArray) : Option ℕ :=
  match bs with
  | [b0, b1, b2, b3] => some (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216)
  | _ => none

/-- THEOREM: natToBytes4 produces exactly 4 bytes -/
theorem natToBytes4_length (n : ℕ) : (natToBytes4 n).length = 4 := by
  simp [natToBytes4]

/-- THEOREM: Integer roundtrip for bounded values -/
theorem nat_roundtrip (n : ℕ) (h : n < 2^32) : 
    bytes4ToNat (natToBytes4 n) = some n := by
  simp only [natToBytes4, bytes4ToNat, Nat.mod_eq_of_lt h]
  -- The arithmetic identity: b0 + b1*256 + b2*65536 + b3*16777216 = n
  -- when b0 = n % 256, b1 = (n/256) % 256, etc.
  ring_nf
  congr 1
  omega

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: UNIT INTERVAL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A value in [0, 1], represented with fixed precision.
    
    We use 24-bit precision (stored in 32 bits) to ensure exact roundtrip
    for the representable values. This gives precision of 1/16777216.
-/
structure UnitInterval where
  value : Fin 16777217  -- 0 to 2^24 inclusive
  deriving Repr, DecidableEq

/-- Convert UnitInterval to rational for computation. -/
def UnitInterval.toRat (u : UnitInterval) : ℚ :=
  u.value.val / 16777216

/-- Create UnitInterval from rational, clamping to [0,1]. -/
def UnitInterval.fromRat (r : ℚ) : UnitInterval :=
  let clamped := max 0 (min 1 r)
  let scaled := (clamped * 16777216).floor.toNat
  ⟨⟨min scaled 16777216, by omega⟩⟩

/-- Serialize UnitInterval to 4 bytes. -/
def unitIntervalToBytes (u : UnitInterval) : ByteArray :=
  natToBytes4 u.value.val

/-- Deserialize 4 bytes to UnitInterval. -/
def bytesToUnitInterval (bs : ByteArray) : Option UnitInterval :=
  match bytes4ToNat bs with
  | some n => 
    if h : n ≤ 16777216 then 
      some ⟨⟨n, by omega⟩⟩
    else 
      none
  | none => none

/-- THEOREM: UnitInterval roundtrip -/
theorem unitInterval_roundtrip (u : UnitInterval) : 
    bytesToUnitInterval (unitIntervalToBytes u) = some u := by
  simp only [unitIntervalToBytes, bytesToUnitInterval]
  have h1 : u.value.val < 2^32 := by
    have := u.value.isLt
    omega
  rw [nat_roundtrip u.value.val h1]
  have h2 : u.value.val ≤ 16777216 := Nat.lt_succ_iff.mp u.value.isLt
  simp only [h2, ↓reduceDIte]

/-- GPUStorable instance for UnitInterval -/
instance : GPUStorable UnitInterval where
  byteSize := 4
  alignment := .align4
  toBytes := unitIntervalToBytes
  fromBytes := bytesToUnitInterval
  roundtrip := unitInterval_roundtrip
  size_correct := fun _ => natToBytes4_length _
  alignment_correct := by simp [Alignment.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: BOOLEAN
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Serialize Boolean to 4 bytes (WebGPU uses u32 for booleans). -/
def boolToBytes (b : Bool) : ByteArray :=
  [⟨if b then 1 else 0, by cases b <;> decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

/-- Deserialize 4 bytes to Boolean. -/
def bytesToBool (bs : ByteArray) : Option Bool :=
  match bs with
  | [b0, _, _, _] => some (b0.val > 0)
  | _ => none

/-- THEOREM: Boolean roundtrip -/
theorem bool_roundtrip (b : Bool) : bytesToBool (boolToBytes b) = some b := by
  cases b <;> simp [boolToBytes, bytesToBool]

/-- THEOREM: boolToBytes produces exactly 4 bytes -/
theorem boolToBytes_length (b : Bool) : (boolToBytes b).length = 4 := by
  cases b <;> simp [boolToBytes]

/-- GPUStorable instance for Bool -/
instance : GPUStorable Bool where
  byteSize := 4
  alignment := .align4
  toBytes := boolToBytes
  fromBytes := bytesToBool
  roundtrip := bool_roundtrip
  size_correct := boolToBytes_length
  alignment_correct := by simp [Alignment.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: VEC2 (UNSIGNED FIXED POINT)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Vec2 with bounded unsigned components for exact roundtrip.
    
    Each component is a 32-bit unsigned integer (Fin 2^32).
    For normalized coordinates, interpret as fixed-point: value / 2^32.
-/
structure Vec2U32 where
  x : Fin (2^32)
  y : Fin (2^32)
  deriving Repr, DecidableEq

/-- Serialize Vec2U32 to 8 bytes. -/
def vec2U32ToBytes (v : Vec2U32) : ByteArray :=
  natToBytes4 v.x.val ++ natToBytes4 v.y.val

/-- Deserialize 8 bytes to Vec2U32. -/
def bytesToVec2U32 (bs : ByteArray) : Option Vec2U32 :=
  if h : bs.length = 8 then
    let xbs := bs.take 4
    let ybs := bs.drop 4
    match bytes4ToNat xbs, bytes4ToNat ybs with
    | some xn, some yn => 
      if hx : xn < 2^32 then
        if hy : yn < 2^32 then
          some ⟨⟨xn, hx⟩, ⟨yn, hy⟩⟩
        else none
      else none
    | _, _ => none
  else none

/-- THEOREM: Vec2U32 serialization produces 8 bytes -/
theorem vec2U32ToBytes_length (v : Vec2U32) : (vec2U32ToBytes v).length = 8 := by
  simp only [vec2U32ToBytes, List.length_append, natToBytes4_length]

/-- Helper: take 4 from natToBytes4 x ++ natToBytes4 y gives natToBytes4 x -/
theorem take4_append_natToBytes4 (x y : ℕ) : 
    (natToBytes4 x ++ natToBytes4 y).take 4 = natToBytes4 x := by
  simp [natToBytes4]

/-- Helper: drop 4 from natToBytes4 x ++ natToBytes4 y gives natToBytes4 y -/
theorem drop4_append_natToBytes4 (x y : ℕ) : 
    (natToBytes4 x ++ natToBytes4 y).drop 4 = natToBytes4 y := by
  simp [natToBytes4]

/-- THEOREM: Vec2U32 roundtrip -/
theorem vec2U32_roundtrip (v : Vec2U32) : 
    bytesToVec2U32 (vec2U32ToBytes v) = some v := by
  simp only [vec2U32ToBytes, bytesToVec2U32]
  have hlen : (natToBytes4 v.x.val ++ natToBytes4 v.y.val).length = 8 := by
    simp [natToBytes4_length]
  simp only [hlen, ↓reduceDIte, take4_append_natToBytes4, drop4_append_natToBytes4]
  have hx_bound : v.x.val < 2^32 := v.x.isLt
  have hy_bound : v.y.val < 2^32 := v.y.isLt
  rw [nat_roundtrip v.x.val hx_bound, nat_roundtrip v.y.val hy_bound]
  simp only [hx_bound, hy_bound, ↓reduceDIte]

/-- GPUStorable instance for Vec2U32 -/
instance : GPUStorable Vec2U32 where
  byteSize := 8
  alignment := .align8
  toBytes := vec2U32ToBytes
  fromBytes := bytesToVec2U32
  roundtrip := vec2U32_roundtrip
  size_correct := vec2U32ToBytes_length
  alignment_correct := by simp [Alignment.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6b: VEC3 (UNSIGNED FIXED POINT)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Vec3 with bounded unsigned components.
    
    WebGPU vec3<f32> has 16-byte alignment with 4 bytes padding.
    We use 16 bytes total: 12 bytes data + 4 bytes padding.
-/
structure Vec3U32 where
  x : Fin (2^32)
  y : Fin (2^32)
  z : Fin (2^32)
  deriving Repr, DecidableEq

/-- Serialize Vec3U32 to 16 bytes (with 4-byte padding). -/
def vec3U32ToBytes (v : Vec3U32) : ByteArray :=
  natToBytes4 v.x.val ++ natToBytes4 v.y.val ++ natToBytes4 v.z.val ++ natToBytes4 0

/-- Deserialize 16 bytes to Vec3U32. -/
def bytesToVec3U32 (bs : ByteArray) : Option Vec3U32 :=
  if h : bs.length = 16 then
    let xbs := bs.take 4
    let ybs := (bs.drop 4).take 4
    let zbs := (bs.drop 8).take 4
    match bytes4ToNat xbs, bytes4ToNat ybs, bytes4ToNat zbs with
    | some xn, some yn, some zn => 
      if hx : xn < 2^32 then
        if hy : yn < 2^32 then
          if hz : zn < 2^32 then
            some ⟨⟨xn, hx⟩, ⟨yn, hy⟩, ⟨zn, hz⟩⟩
          else none
        else none
      else none
    | _, _, _ => none
  else none

/-- THEOREM: Vec3U32 serialization produces 16 bytes -/
theorem vec3U32ToBytes_length (v : Vec3U32) : (vec3U32ToBytes v).length = 16 := by
  simp only [vec3U32ToBytes, List.length_append, natToBytes4_length]

/-- Helper lemma for Vec3 take operations -/
theorem vec3_take4 (x y z w : ℕ) : 
    (natToBytes4 x ++ natToBytes4 y ++ natToBytes4 z ++ natToBytes4 w).take 4 = natToBytes4 x := by
  simp [natToBytes4]

theorem vec3_drop4_take4 (x y z w : ℕ) : 
    ((natToBytes4 x ++ natToBytes4 y ++ natToBytes4 z ++ natToBytes4 w).drop 4).take 4 = natToBytes4 y := by
  simp [natToBytes4]

theorem vec3_drop8_take4 (x y z w : ℕ) : 
    ((natToBytes4 x ++ natToBytes4 y ++ natToBytes4 z ++ natToBytes4 w).drop 8).take 4 = natToBytes4 z := by
  simp [natToBytes4]

/-- THEOREM: Vec3U32 roundtrip -/
theorem vec3U32_roundtrip (v : Vec3U32) : 
    bytesToVec3U32 (vec3U32ToBytes v) = some v := by
  simp only [vec3U32ToBytes, bytesToVec3U32]
  have hlen : (natToBytes4 v.x.val ++ natToBytes4 v.y.val ++ natToBytes4 v.z.val ++ natToBytes4 0).length = 16 := by
    simp [natToBytes4_length]
  simp only [hlen, ↓reduceDIte, vec3_take4, vec3_drop4_take4, vec3_drop8_take4]
  have hx_bound : v.x.val < 2^32 := v.x.isLt
  have hy_bound : v.y.val < 2^32 := v.y.isLt
  have hz_bound : v.z.val < 2^32 := v.z.isLt
  rw [nat_roundtrip v.x.val hx_bound, nat_roundtrip v.y.val hy_bound, nat_roundtrip v.z.val hz_bound]
  simp only [hx_bound, hy_bound, hz_bound, ↓reduceDIte]

/-- GPUStorable instance for Vec3U32 -/
instance : GPUStorable Vec3U32 where
  byteSize := 16
  alignment := .align16
  toBytes := vec3U32ToBytes
  fromBytes := bytesToVec3U32
  roundtrip := vec3U32_roundtrip
  size_correct := vec3U32ToBytes_length
  alignment_correct := by simp [Alignment.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6c: VEC4 (UNSIGNED FIXED POINT)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Vec4 with bounded unsigned components.
    
    WebGPU vec4<f32> has 16-byte alignment, no padding needed.
-/
structure Vec4U32 where
  x : Fin (2^32)
  y : Fin (2^32)
  z : Fin (2^32)
  w : Fin (2^32)
  deriving Repr, DecidableEq

/-- Serialize Vec4U32 to 16 bytes. -/
def vec4U32ToBytes (v : Vec4U32) : ByteArray :=
  natToBytes4 v.x.val ++ natToBytes4 v.y.val ++ natToBytes4 v.z.val ++ natToBytes4 v.w.val

/-- Deserialize 16 bytes to Vec4U32. -/
def bytesToVec4U32 (bs : ByteArray) : Option Vec4U32 :=
  if h : bs.length = 16 then
    let xbs := bs.take 4
    let ybs := (bs.drop 4).take 4
    let zbs := (bs.drop 8).take 4
    let wbs := bs.drop 12
    match bytes4ToNat xbs, bytes4ToNat ybs, bytes4ToNat zbs, bytes4ToNat wbs with
    | some xn, some yn, some zn, some wn => 
      if hx : xn < 2^32 then
        if hy : yn < 2^32 then
          if hz : zn < 2^32 then
            if hw : wn < 2^32 then
              some ⟨⟨xn, hx⟩, ⟨yn, hy⟩, ⟨zn, hz⟩, ⟨wn, hw⟩⟩
            else none
          else none
        else none
      else none
    | _, _, _, _ => none
  else none

/-- THEOREM: Vec4U32 serialization produces 16 bytes -/
theorem vec4U32ToBytes_length (v : Vec4U32) : (vec4U32ToBytes v).length = 16 := by
  simp only [vec4U32ToBytes, List.length_append, natToBytes4_length]

/-- Helper lemma for Vec4 drop 12 -/
theorem vec4_drop12 (x y z w : ℕ) : 
    (natToBytes4 x ++ natToBytes4 y ++ natToBytes4 z ++ natToBytes4 w).drop 12 = natToBytes4 w := by
  simp [natToBytes4]

/-- THEOREM: Vec4U32 roundtrip -/
theorem vec4U32_roundtrip (v : Vec4U32) : 
    bytesToVec4U32 (vec4U32ToBytes v) = some v := by
  simp only [vec4U32ToBytes, bytesToVec4U32]
  have hlen : (natToBytes4 v.x.val ++ natToBytes4 v.y.val ++ natToBytes4 v.z.val ++ natToBytes4 v.w.val).length = 16 := by
    simp [natToBytes4_length]
  simp only [hlen, ↓reduceDIte, vec3_take4, vec3_drop4_take4, vec3_drop8_take4, vec4_drop12]
  have hx_bound : v.x.val < 2^32 := v.x.isLt
  have hy_bound : v.y.val < 2^32 := v.y.isLt
  have hz_bound : v.z.val < 2^32 := v.z.isLt
  have hw_bound : v.w.val < 2^32 := v.w.isLt
  rw [nat_roundtrip v.x.val hx_bound, nat_roundtrip v.y.val hy_bound, 
      nat_roundtrip v.z.val hz_bound, nat_roundtrip v.w.val hw_bound]
  simp only [hx_bound, hy_bound, hz_bound, hw_bound, ↓reduceDIte]

/-- GPUStorable instance for Vec4U32 -/
instance : GPUStorable Vec4U32 where
  byteSize := 16
  alignment := .align16
  toBytes := vec4U32ToBytes
  fromBytes := bytesToVec4U32
  roundtrip := vec4U32_roundtrip
  size_correct := vec4U32ToBytes_length
  alignment_correct := by simp [Alignment.toNat]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: DETERMINISM THEOREMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- THEOREM: Serialization is deterministic -/
theorem serialize_deterministic {α : Type*} [GPUStorable α] (x : α) : 
    GPUStorable.toBytes x = GPUStorable.toBytes x := rfl

/-- THEOREM: Same value produces same bytes -/
theorem same_value_same_bytes {α : Type*} [GPUStorable α] (x y : α) (h : x = y) : 
    GPUStorable.toBytes x = GPUStorable.toBytes y := by rw [h]

/-- THEOREM: Roundtrip preserves identity -/
theorem roundtrip_identity {α : Type*} [GPUStorable α] (x : α) : 
    GPUStorable.fromBytes (GPUStorable.toBytes x) = some x := 
  GPUStorable.roundtrip x

/-- THEOREM: If two values serialize to same bytes and roundtrip, they're equal -/
theorem bytes_eq_implies_value_eq {α : Type*} [GPUStorable α] [DecidableEq α] (x y : α) 
    (h : GPUStorable.toBytes x = GPUStorable.toBytes y) : x = y := by
  have hx := GPUStorable.roundtrip x
  have hy := GPUStorable.roundtrip y
  rw [h] at hx
  -- hx : fromBytes (toBytes y) = some x
  -- hy : fromBytes (toBytes y) = some y
  rw [hx] at hy
  exact Option.some.inj hy

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: CACHE KEY CORRECTNESS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Cache key is a hash of serialized bytes.
    For proofs, we model it as the bytes themselves (injective). -/
def cacheKey {α : Type*} [GPUStorable α] (x : α) : ByteArray :=
  GPUStorable.toBytes x

/-- THEOREM: Equal values produce equal cache keys -/
theorem equal_values_equal_keys {α : Type*} [GPUStorable α] (x y : α) (h : x = y) : 
    cacheKey x = cacheKey y := by
  simp only [cacheKey, h]

/-- THEOREM: Cache key determinism (same input always same output) -/
theorem cache_key_deterministic {α : Type*} [GPUStorable α] (x : α) : 
    cacheKey x = cacheKey x := rfl

/-- THEOREM: Distinct roundtrip-recoverable values have distinct cache keys -/
theorem distinct_values_distinct_keys {α : Type*} [GPUStorable α] [DecidableEq α] (x y : α) 
    (hne : x ≠ y) : cacheKey x ≠ cacheKey y := by
  intro heq
  apply hne
  exact bytes_eq_implies_value_eq x y heq

end Hydrogen.Schema.GPU.Storable
