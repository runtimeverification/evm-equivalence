import EvmYul.UInt256
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.StateMap

/-! # KEVM Interface

This file provides a proving interface for the KEVM function definitions.
Some of the contents of this file may be ported to a utils file in the future.
 -/

open EvmYul
open StateMap

namespace KEVMInterface

-- Some functions are uninterpreted for now, so we have to axiomatize the behavior
-- For functions that are defined, the axioms are theorems

section

variable {m n : SortInt}

/-! ## Simple function behavior

Behavioral results about simple functions like arithmetic or boolean operations.
 -/

-- Behavior for `«_?Int_»`
@[simp]
theorem plusIntIsSome : «_+Int_» n m = some (n + m) := rfl

@[simp]
theorem subIntIsSome : «_-Int_» n m = some (n - m) := rfl

theorem mulIntIsSome : «_*Int_» n m = some (n * m) := rfl

-- Behavior for `chop`
theorem chopIsSome : chop n = some (n % UInt256.size) := rfl

end

-- Behavior of `«_==K_»` and `«_=/=K_»`
axiom Axioms.Keq_def (k₁ k₂ : SortK) : «_==K_» k₁ k₂ = some (k₁ == k₂)
axiom Axioms.Kneq_def (k₁ k₂ : SortK) : «_=/=K_» k₁ k₂ = some (k₁ != k₂)

-- Behavior of `_orBool_`, `_andBool_` and `notBool_`
@[simp]
theorem orBool_def (b₁ b₂ : SortBool) : _orBool_ b₁ b₂ = some (b₁ || b₂) := by
  aesop (add simp [_orBool_, _7174452])
@[simp]
theorem andBool_def (b₁ b₂ : SortBool) : _andBool_ b₁ b₂ = some (b₁ && b₂) := by
  aesop (add simp [_andBool_, _5b9db8d])
@[simp]
theorem notBool_def (b : SortBool) : notBool_ b = some (!b) := by
  aesop (add simp [notBool_, _17ebc68])

-- Behavior of boolean Int comparisons
@[simp]
theorem eqInt_def (n m : SortInt) : «_==Int_» n m = some (n == m) := rfl
@[simp]
theorem neqInt_def (n m : SortInt) : «_=/=Int_» n m = some (n != m) := by
  aesop (add simp [«_=/=Int_», _4de6e05, Option.bind, not])
@[simp]
theorem ltInt_def (n m : SortInt) : «_<Int_» n m = some (decide (n < m)) := rfl

-- Behavior of `kite`
@[simp]
theorem kite_def {SortSort : Type} (cnd : SortBool) (true_branch false_branch: SortSort) :
  kite cnd true_branch false_branch = ite cnd true_branch false_branch := by
  aesop

/-! ## Behavior of `«#sizeWordStack»`

Equating `#sizeWordStack` to `List.length`.
-/

def wsLength (ws : SortWordStack) : ℕ :=
  match ws with
  | .«.WordStack_EVM-TYPES_WordStack» => 0
  | .«_:__EVM-TYPES_WordStack_Int_WordStack» _ ws => wsLength ws + 1

theorem sizeWordStackNotEmpty {n w : SortInt} {ws : SortWordStack} :
  sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n =
  sizeWordStackAux ws (n + 1) := by
  simp [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]

theorem sizeWordStack_add_one {w n : SortInt} {ws : SortWordStack} :
  sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n = do
  let val0 ← sizeWordStackAux ws n
  let val1 ← «_+Int_» val0 1
  return val1 := by
  revert n
  induction ws <;> simp_all [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]

theorem sizeWordStackAuxAdd {n : SortInt} {ws : SortWordStack} :
  sizeWordStackAux ws (n + 1) = do
  let a ← sizeWordStackAux ws n
  let b ← «_+Int_» a 1
  return b := by
  rw [←sizeWordStackNotEmpty (w := 0), sizeWordStack_add_one]

theorem sizeWordStackIsSome {ws : SortWordStack} :
  sizeWordStackAux ws 0 = some (wsLength ws) := by
  unfold sizeWordStackAux
  induction' ws
  . aesop (add simp [sizeWordStackAux, _432555e])
  . simp_all [sizeWordStack_add_one, wsLength]; rewrite [←sizeWordStackAux] at *
    aesop (add simp [sizeWordStack_add_one])

theorem wsLength_eq_length_wordStackMap {ws : SortWordStack} :
  wsLength ws = List.length (wordStackMap ws) := by
  induction ws <;> simp_all [wsLength]

theorem sizeWordStack_def {ws : SortWordStack} :
  sizeWordStackAux ws 0 = some (List.length (wordStackMap ws)) :=
  wsLength_eq_length_wordStackMap ▸ sizeWordStackIsSome

/-! ## Behavior of K's `in_keys` function

Axiomatically asserting `in_keys` behavior.

NOTE: These functions depend on the dummy implementation as maps
being `List (Key × Value)`.
-/

def keys {K V : Type} (l : List (K × V)) : List K :=
  List.map (λ pair => pair.1) l

def inKeys_compute (map : SortMap) (key : SortInt) : Bool :=
  List.elem (inj key) (keys map.coll)

@[simp]
axiom Axioms.inKeys_def (map : SortMap) (key : SortInt) :
  «_in_keys(_)_MAP_Bool_KItem_Map» (inj ((inj key) : SortAccount)) map =
  some (inKeys_compute map key)

/-! ### Behavior of `#inStorage` function

This definition of `#inStorage` depends on the above `inKeys_compute`.
-/

noncomputable def inStorage_compute (map : SortMap) (acc key : SortInt) : Bool :=
  match «Map:lookup» map (inj ((@inj SortInt SortAccount) acc)) with
  | none => false
  | some a => match «#inStorageAux1» a key with
    | none => false
    | some b => if inKeys_compute map acc then b else false

@[simp]
theorem inStorage_def {ACCESSEDSTORAGE_CELL : SortMap} {ID_CELL W0 : SortInt} :
  «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some (inStorage_compute ACCESSEDSTORAGE_CELL ID_CELL W0) := by
  aesop (add simp [«#inStorage», _dbb1f9e, _8d90a32, Option.bind, inStorage_compute])

/-! ## Memory results

Results that have to do with memory-related operations.
 -/

attribute [local simp] «_<Int_» «_+Int_» «_<=Int_» «_-Int_» «_/Int_» «_=/=Int_» «_==Int_»

/--
  Explicit account for `«#memoryUsageUpdate»` with positive `width`.
 -/
theorem memoryUsageUpdate_rw
  (MEMORYUSED_CELL offset width : SortInt)
  (width_pos : 0 < width):
  «#memoryUsageUpdate» MEMORYUSED_CELL offset width =
  some (MEMORYUSED_CELL ⊔ Int.tdiv (offset + width + 31) 32) := by
  simp [«#memoryUsageUpdate», _8096892, _86ca6df, notBool_def, Option.bind]
  simp [«maxInt(_,_)_INT-COMMON_Int_Int_Int», «_up/Int__EVM-TYPES_Int_Int_Int»]
  simp [_091b7da, _50d266e, _e985b28, _5321d80 ]
  aesop (add simp [Int.max_def, failure]) (add safe (by linarith))

/--
  Explicit account for `mapWriteRange`.
-/
theorem mapWriteRange_rw (mem content : SortBytes) (index : SortInt) :
  mapWriteRange mem index content =
  if _ : index < 0 then some .empty else
  if _ : content.size = 0 then some mem else
  let padded :=
    «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» mem (index + content.size) 0
    |>.get (rfl)
  «replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes» padded index content
  := by
  split <;> simp [mapWriteRange, _8391694, _4de6e05, _a656ca7, _f03fd7e] <;>
  simp [«lengthBytes(_)_BYTES-HOOKED_Int_Bytes»] <;>
  simp [«.Bytes_BYTES-HOOKED_Bytes»] <;>
  simp [«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»] <;>
  simp [«replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes»]
  aesop; split; aesop; simp [Option.bind, notBool_def, andBool_def]
  aesop (add simp [ByteArray.size]) (add safe (by linarith)) (add safe (by omega))

/-! ## Bytes manipulation

Results to ease the reasoning about `SortBytes` manipulation functions.
-/

/--
Explicit account for `«#padToWidth»`.
-/
theorem padToWidth_rw (len : SortInt) (b : SortBytes) :
  «#padToWidth» len b =
  if len < 0 then some b else some { data := Array.leftpad len.toNat 0 b.data} := by
  aesop (add simp [«#padToWidth», _67678cd, _ebfe294, notBool_def])
  (add simp [«padLeftBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», Option.bind])

/--
This axiom states the following:

`Int2Bytes` behaves as `BE` for positive integers and big endian representation.

Note that the first parameter of `Int2Bytes` is the length of the
corresponding encoding sequence.
-/
axiom Axioms.BE_IntToBytes_eq (n : ℕ) :
  «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» (Int.tdiv (↑(n + 1).log2 + 8) 8) (n + 1) .bigEndianBytes = some (BE (n + 1))

/--
Explicit account for `«#asByteStack»`.

This result notoriously depends on `Axioms.BE_IntToBytes_eq`, which
should be a theorem at some point.
-/
theorem asByteStack_rw {n : ℕ} : «#asByteStack» n = some (BE n) := by
  simp [«#asByteStack», _fdd6ce1, Int2BytesNoLen, _20f05d9, _43f856e, _6c109c0, _ea9648a]
  simp [«.Bytes_BYTES-HOOKED_Bytes», Option.bind, guard]
  cases n <;> simp [_e9743d5, «_>Int_», «log2Int(_)_INT-COMMON_Int_Int», BE_zero]
  refine Axioms.BE_IntToBytes_eq _

/--
Given `n : ℕ` with `n < UInt256.size`, converting it to `byteStack`
and padding the result to width 32, is the same as
`UInt256.toByteArray (n : UInt256)`.
-/
theorem padToWidth32_asByteStack_rw
  {n : ℕ} {b : SortBytes}
  (n_small : n < UInt256.size)
  (asByteStack_def : «#asByteStack» n = some b) :
  «#padToWidth» 32 b = some
  (ffi.ByteArray.zeroes { toBitVec := 32#System.Platform.numBits - BitVec.ofNat System.Platform.numBits (BE n).size } ++ BE n)
   := by
  simp [Axioms.ffi_zeroes, «#padToWidth», _67678cd, _ebfe294, notBool_def, failure]
  simp [«padLeftBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  rw [zeroes_size_eq_sub n_small, ByteArray.append_array_data]; congr
  -- To have a clearer view of the goal:
  all_goals rw [←List.toByteArray]; have: (toBytesBigEndian n).toByteArray = BE n := rfl; rw [this]
  all_goals rw [asByteStack_rw] at *; aesop

/--
For any ByteArray `b`, `Bytes2Int b .bigEndianBytes .unsignedBytes`
computes the same as `fromByteArrayBigEndian b`.

This should be proved at some point.
-/
theorem Bytes2Int_fromByteArrayBigEndian_eq  (b : ByteArray) :
  «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» b .bigEndianBytes .unsignedBytes =
  Int.ofNat (fromByteArrayBigEndian b) := by
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness»
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».unsigned
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».res
  rcases b with ⟨⟨l⟩⟩; simp
  induction l; simp [ByteArray.toList_empty, fromByteArrayBigEndian]; rfl
  rename_i h t ih
  rw [Axioms.ByteArray.toList_eq, List.foldr] at *
  simp [Axioms.ByteArray.toList_eq, List.foldr]
  sorry

/--
Friendlier interface for `#range`.

This should be proven at some point.
-/
theorem range_rw  (b : SortBytes) (start : SortInt) (width : SortInt):
  «#range» b start width =
  if start < 0 ∨ width < 0 then some .empty else
  if 0 ≤ start ∧ 0 ≤ width ∧ start < b.size then
  let len := Int.ofNat b.size
  let pad :=
    «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» b len 0
    |>.get rfl
  «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» pad start len
  else some .empty := by sorry

/--
Converting a 32-byte chunk of memory into an unsigned integer never
overflows `chop`.
-/
theorem chop_self_eq
  {LM b : SortBytes}
  {start n: SortInt}
  (defn_b : «#range» LM start 32 = some b)
  (defn_n : «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» b .bigEndianBytes .unsignedBytes = some n):
  chop n = n := by sorry

@[simp]
theorem asWord_empty : asWord .empty = some 0 := by
  simp [asWord, _ef5332a]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness»]
  simp [chop, _85aa67b, _modInt_]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».unsigned]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».res]
  simp [ByteArray.empty, ByteArray.mkEmpty, ByteArray.toList_empty, ByteArray.toList_empty]
  aesop

/-! ## Misc

Miscellaneous and helpful results.
 -/

/--
Explicit account for the `SortInt` → `SortAccount` injection instance.
-/
@[simp]
theorem inj_ID_CELL (ID_CELL : SortInt) : @inj SortInt SortAccount instInjSortIntSortAccount ID_CELL = .inj_SortInt ID_CELL := rfl

end KEVMInterface
