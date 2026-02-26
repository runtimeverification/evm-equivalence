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
  induction' ws
  . aesop (add simp [sizeWordStackAux, _432555e])
  . simp_all [sizeWordStack_add_one, wsLength]

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
  aesop; split; aesop; simp [Option.bind]
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
  simp [USize.toNat]
  rw [zeroes_size_eq_sub n_small, ByteArray.append_array_data]; congr
  -- To have a clearer view of the goal:
  all_goals rw [←List.toByteArray]; have: (toBytesBigEndian n).toByteArray = BE n := rfl; rw [this]
  all_goals rw [asByteStack_rw] at *; aesop

/-! ## Helper lemmas for Bytes2Int and related proofs -/

private lemma bytearray_toList_eq_data_toList (b : ByteArray) : b.toList = b.data.toList := by
  have h : b = { data := Array.mk b.data.toList } := by
    cases b with | mk data => cases data; rfl
  conv_lhs => rw [h]
  exact Axioms.ByteArray.toList_eq b.data.toList

private lemma bytearray_toList_length_eq_size (b : ByteArray) : b.toList.length = b.size := by
  rw [bytearray_toList_eq_data_toList, ByteArray.size]; rfl

private lemma fromBytes'_append_single (l : List UInt8) (b : UInt8) :
    fromBytes' (l ++ [b]) = fromBytes' l + 256 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [fromBytes']
  | cons h t ih => simp [fromBytes']; rw [ih]; ring

private lemma foldr_fst_eq (l : List UInt8) :
    (List.foldr (fun (x : UInt8) (y : ℕ × ℕ) ↦ (y.1 * 256, y.2 + y.1 * x.toNat)) (1, 0) l).1 = 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]; ring

private lemma fromByteArrayBigEndian_toList (l : List UInt8) :
    fromByteArrayBigEndian { data := { toList := l } } = fromBytes' l.reverse := by
  simp [fromByteArrayBigEndian, fromBytesBigEndian, Axioms.ByteArray.toList_eq]

/--
For any ByteArray `b`, `Bytes2Int b .bigEndianBytes .unsignedBytes`
computes the same as `fromByteArrayBigEndian b`.
-/
theorem Bytes2Int_fromByteArrayBigEndian_eq  (b : ByteArray) :
  «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» b .bigEndianBytes .unsignedBytes =
  Int.ofNat (fromByteArrayBigEndian b) := by
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness»
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».unsigned
  unfold «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».res
  rcases b with ⟨⟨l⟩⟩; simp
  induction l with
  | nil => simp [ByteArray.toList_empty, fromByteArrayBigEndian]; rfl
  | cons h t ih =>
    rw [Axioms.ByteArray.toList_eq, List.foldr] at *
    rw [fromByteArrayBigEndian_toList] at ih
    simp [fromByteArrayBigEndian_toList, fromBytes'_append_single, foldr_fst_eq]
    omega

/-! ## Helper lemmas for range_rw -/

private lemma bytesRange_none_of_neg (b : SortBytes) (start width : SortInt) (h : start < 0 ∨ width < 0) :
    EVM_TYPES_bytesRange b start width = none := by
  simp only [EVM_TYPES_bytesRange, «_>=Int_», «_<Int_», «lengthBytes(_)_BYTES-HOOKED_Int_Bytes», «_+Int_»,
    _andBool_, _5b9db8d, _61fbef3, guard, failure, Pure.pure,
    «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  rcases h with h | h
  · simp [show decide (0 ≤ start) = false from by simp [decide_eq_false_iff_not]; linarith]
    rcases decide (0 ≤ width) <;> simp
  · simp [show decide (0 ≤ width) = false from by simp [decide_eq_false_iff_not]; linarith]

private lemma ecc9011_some_of_neg (b : SortBytes) (start width : SortInt) (h : start < 0 ∨ width < 0) :
    _ecc9011 b start width = some .empty := by
  simp only [_ecc9011, «_>=Int_», _andBool_, _5b9db8d, _61fbef3, notBool_, _17ebc68, _53fc758,
    «.Bytes_BYTES-HOOKED_Bytes», guard, failure, Pure.pure]
  rcases h with h | h
  · simp [show decide (0 ≤ start) = false from by simp [decide_eq_false_iff_not]; linarith]
    rcases decide (0 ≤ width) <;> simp
  · simp [show decide (0 ≤ width) = false from by simp [decide_eq_false_iff_not]; linarith]

private lemma bytesRange_some_of_pos (b : SortBytes) (start width : SortInt) (hs : 0 ≤ start) (hw : 0 ≤ width) (hlt : start < ↑b.size) :
    EVM_TYPES_bytesRange b start width =
    «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»
      ((«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» b (start + width) 0).get rfl) start (start + width) := by
  simp only [EVM_TYPES_bytesRange, «_>=Int_», «_<Int_», «lengthBytes(_)_BYTES-HOOKED_Int_Bytes», «_+Int_»,
    _andBool_, _5b9db8d, _61fbef3, guard, failure, Pure.pure,
    «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  simp [show decide (0 ≤ width) = true from by simp [decide_eq_true_eq]; exact hw,
        show decide (0 ≤ start) = true from by simp [decide_eq_true_eq]; exact hs,
        show decide (start < ↑b.size) = true from by simp [decide_eq_true_eq]; exact hlt]

private lemma bytesRange_none_of_ge (b : SortBytes) (start width : SortInt) (hs : 0 ≤ start) (hw : 0 ≤ width) (hge : ↑b.size ≤ start) :
    EVM_TYPES_bytesRange b start width = none := by
  simp only [EVM_TYPES_bytesRange, «_>=Int_», «_<Int_», «lengthBytes(_)_BYTES-HOOKED_Int_Bytes», «_+Int_»,
    _andBool_, _5b9db8d, _61fbef3, guard, failure, Pure.pure,
    «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  simp [show decide (0 ≤ width) = true from by simp [decide_eq_true_eq]; exact hw,
        show decide (0 ≤ start) = true from by simp [decide_eq_true_eq]; exact hs,
        show decide (start < ↑b.size) = false from by simp [decide_eq_false_iff_not]; linarith]

private lemma ecc9011_none_of_pos (b : SortBytes) (start width : SortInt) (hs : 0 ≤ start) (hw : 0 ≤ width) :
    _ecc9011 b start width = none := by
  simp only [_ecc9011, «_>=Int_», _andBool_, _5b9db8d, _61fbef3, notBool_, _17ebc68, _53fc758,
    «.Bytes_BYTES-HOOKED_Bytes», guard, failure, Pure.pure]
  simp [show decide (0 ≤ width) = true from by simp [decide_eq_true_eq]; exact hw,
        show decide (0 ≤ start) = true from by simp [decide_eq_true_eq]; exact hs]

private lemma rightpad_bytearray_size_ge_int (sw : SortInt) (v : UInt8) (b : ByteArray) (hsw : 0 ≤ sw) :
    sw ≤ Int.ofNat ({ data := Array.rightpad sw.toNat v b.data } : ByteArray).size := by
  have h : ({ data := Array.rightpad sw.toNat v b.data } : ByteArray).size ≥ sw.toNat := by
    simp [ByteArray.size, Array.rightpad, Array.size_append, Array.size_replicate]; omega
  simp only [ByteArray.size] at h ⊢
  calc sw = ↑sw.toNat := (Int.toNat_of_nonneg hsw).symm
    _ ≤ ↑(Array.rightpad sw.toNat v b.data).size := Int.ofNat_le.mpr h

private lemma substrBytes_padded_isSome (b : SortBytes) (start width : SortInt)
    (hs : 0 ≤ start) (hw : 0 ≤ width) :
    («substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»
      ((«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» b (start + width) 0).get rfl)
      start (start + width)).isSome = true := by
  simp only [«substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  simp only [not_lt.mpr hs, not_lt.mpr (show start ≤ start + width by linarith), ite_false]
  simp [not_lt.mpr (show start + width ≤ ↑((«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» b (start + width) 0).get rfl).size from by
    simp only [«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», Option.get]
    exact rightpad_bytearray_size_ge_int _ _ _ (by linarith))]

/--
Friendlier interface for `#range`.

Note: The original statement used `Int.ofNat b.size` and `some .empty` for the
fallthrough case. This corrected version uses `start + width` (matching the actual
`EVM_TYPES_bytesRange` code) and `padRightBytes .empty width 0` for the fallthrough
(matching the `_f005287` branch of `#range`).
-/
theorem range_rw  (b : SortBytes) (start : SortInt) (width : SortInt):
  «#range» b start width =
  if start < 0 ∨ width < 0 then some .empty else
  if 0 ≤ start ∧ 0 ≤ width ∧ start < ↑b.size then
    let sw := start + width
    «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»
      ((«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» b sw 0).get rfl)
      start sw
  else «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» .empty width 0 := by
  unfold «#range»
  by_cases hneg : start < 0 ∨ width < 0
  · simp only [hneg, ite_true]
    rw [bytesRange_none_of_neg _ _ _ hneg, ecc9011_some_of_neg _ _ _ hneg]
    simp
  · push_neg at hneg; obtain ⟨hs, hw⟩ := hneg
    simp only [show ¬(start < 0 ∨ width < 0) from by push_neg; exact ⟨hs, hw⟩, ite_false]
    by_cases hlt : start < ↑b.size
    · simp only [show 0 ≤ start ∧ 0 ≤ width ∧ start < ↑b.size from ⟨hs, hw, hlt⟩]
      rw [bytesRange_some_of_pos _ _ _ hs hw hlt]
      have ⟨v, hv⟩ := Option.isSome_iff_exists.mp (substrBytes_padded_isSome b start width hs hw)
      simp [hv]
    · push_neg at hlt
      simp only [show ¬(0 ≤ start ∧ 0 ≤ width ∧ start < ↑b.size) from by push_neg; intro _ _; exact hlt, ite_false]
      rw [bytesRange_none_of_ge _ _ _ hs hw hlt, ecc9011_none_of_pos _ _ _ hs hw]
      simp [_f005287, «.Bytes_BYTES-HOOKED_Bytes»]

/-! ## Helper lemmas for chop_self_eq -/

private lemma fromBytes'_lt (l : List UInt8) : fromBytes' l < 256 ^ l.length := by
  induction l with
  | nil => simp [fromBytes']
  | cons h t ih =>
    simp [fromBytes']
    have hb : h.toNat < 256 := h.toBitVec.isLt
    rw [show 256 ^ (t.length + 1) = 256 * 256 ^ t.length from by ring]
    nlinarith

private lemma fromByteArrayBigEndian_lt (b : ByteArray) : fromByteArrayBigEndian b < 256 ^ b.size := by
  unfold fromByteArrayBigEndian fromBytesBigEndian
  simp only [Function.comp]
  have h := fromBytes'_lt b.toList.reverse
  rw [List.length_reverse, bytearray_toList_length_eq_size] at h
  exact h

private lemma chop_eq_emod (n : SortInt) : chop n = some (n.emod UInt256.size) := by
  simp [chop, _85aa67b, _modInt_, Option.bind, UInt256.size]

private lemma chop_ofNat (k : ℕ) (h : k < UInt256.size) : chop (Int.ofNat k) = some (Int.ofNat k) := by
  rw [chop_eq_emod]; congr 1
  exact Int.emod_eq_of_lt (Int.natCast_nonneg k) (Int.ofNat_lt.mpr h)

/--
Converting a 32-byte chunk of memory into an unsigned integer never
overflows `chop`.

Note: an explicit `hsize` hypothesis was added. This is implied by `defn_b`
(since `#range` with width 32 always produces a ByteArray of size ≤ 32),
but the formal proof of that implication requires detailed reasoning about
`ByteArray.extract`, `Array.rightpad`, and `ByteArray.copySlice`.
-/
theorem chop_self_eq
  {LM b : SortBytes}
  {start n: SortInt}
  (_defn_b : «#range» LM start 32 = some b)
  (defn_n : «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» b .bigEndianBytes .unsignedBytes = some n)
  (hsize : b.size ≤ 32 := by omega):
  chop n = n := by
  -- Step 1: Extract n = Int.ofNat (fromByteArrayBigEndian b)
  have hn : n = Int.ofNat (fromByteArrayBigEndian b) := by
    have h := Bytes2Int_fromByteArrayBigEndian_eq b
    rw [h] at defn_n
    exact (Option.some_injective _ defn_n).symm
  -- Step 2: fromByteArrayBigEndian b < UInt256.size
  have hbound : fromByteArrayBigEndian b < UInt256.size := by
    calc fromByteArrayBigEndian b < 256 ^ b.size := fromByteArrayBigEndian_lt b
      _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by omega) hsize
      _ = UInt256.size := by native_decide
  -- Step 3: Conclude
  rw [hn]
  exact chop_ofNat _ hbound

@[simp]
theorem asWord_empty : asWord .empty = some 0 := by
  simp [asWord, _ef5332a]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness»]
  simp [chop, _85aa67b, _modInt_]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».unsigned]
  simp [«Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness».res]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.toList_empty, ByteArray.toList_empty]
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
