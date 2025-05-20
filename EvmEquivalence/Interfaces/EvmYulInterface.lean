import EvmYul.EVM.Semantics
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Utils.IntUtils
import EvmEquivalence.Utils.ListByteArrayUtils


open EvmYul
open EVM

namespace USize

theorem toNat_ofNat_le (n : ℕ) :
  toNat (@OfNat.ofNat USize n instOfNat) ≤ n := by
  cases System.Platform.numBits_eq <;> aesop (add simp [toNat]) (add safe (by omega))

theorem toNat_ofNat_eq (n : ℕ) (n_small : n < UInt32.size) :
  toNat (@OfNat.ofNat USize n instOfNat) = n := by
  cases System.Platform.numBits_eq <;>
  aesop (add simp [toNat, UInt32.size]) (add safe (by omega))

end USize

namespace UInt256

section

set_option linter.deprecated false

variable {n : ℕ}
variable {p : ℤ}

-- Conversions

theorem val_eq (h : n < UInt256.size): ↑(UInt256.ofNat n).1 = n := by
  aesop (add simp [UInt256.ofNat, Id.run, Fin.ofNat])
        (add safe (by omega))

theorem ofNat_eq: UInt256.ofNat n = ⟨Fin.ofNat n⟩ := by
  aesop (add simp [UInt256.ofNat])

theorem ofNat_toNat (n_le_size : n < UInt256.size) :
  (UInt256.ofNat n).toNat = n := by
  aesop (add simp [UInt256.ofNat, UInt256.toNat, Id.run, dbgTrace, Fin.ofNat])

theorem ofNat_toSigned {n : ℕ} {p : ℤ} (h : ↑n = p) :
  UInt256.ofNat n = .toSigned p := by aesop

-- Arithmetic

@[simp]
theorem sub_0 {n : UInt256} : n - .ofNat 0 = n := by
  match n with
  | UInt256.mk (Fin.mk val isLT) =>
  simp [UInt256.ofNat, Id.run, HSub.hSub, Sub.sub, UInt256.sub]
  simp [UInt256.size, Fin.ofNat, Fin.sub]; assumption
  -- Alternatively:
  /- simp [UInt256.ofNat]; split; try contradiction
  simp [Id.run, HSub.hSub, Sub.sub, UInt256.sub]
  simp [Fin.sub]; rw [Nat.mod_eq_iff_lt]; assumption; simp [UInt256.size] -/

@[simp]
theorem zero_add: .ofNat 0 + .ofNat n = UInt256.ofNat n := by
  simp [UInt256.ofNat, Id.run, dbgTrace, Fin.ofNat, HAdd.hAdd]
  simp [Add.add, UInt256.add, Fin.add_def]

theorem add_succ_mod_size (pos : 0 ≤ p) (size_ok : p + 1 < UInt256.size) : (p + 1) % UInt256.size = p + 1 := by
        rw [Int.mod_cast, Int.toNat_ofNat, Nat.mod_eq_of_lt] <;> aesop (add safe (by omega))

theorem sub_to_fin (n m : UInt256) : n - m = { val := (n.val - m.val)} := rfl

theorem toNat_sub_dist (n m : UInt256) (le_ok : m ≤ n): (n - m).toNat = n.toNat - m.toNat := by
  rw [sub_to_fin]; simp [UInt256.toNat]; rw [←Fin.sub_val_of_le]; aesop

theorem ofNat_le (n m : UInt256) : (n ≤ m) = (n.toNat ≤ m.toNat) := by aesop

end

end UInt256

@[simp]
theorem isCreate_false {τ : OperationType} (opcode : Operation τ) (noCreate : opcode ≠ Operation.CREATE) (noCreate2 : opcode ≠ Operation.CREATE2):
  opcode.isCreate = false := by
  cases opc: opcode <;> rw [Operation.isCreate]; next op =>
  cases op <;> aesop

section

variable {gas gasCost : ℕ}

/--
Execution result of `X` for a single-opcode program when `pc` is set to 1
 -/
theorem X_bad_pc {opcode : UInt8}
                 {symValidJumps : Array UInt256}
                 {symState : EVM.State}
                 (gpos : 1 < gas)
                 (pc1 : symState.pc = .ofNat 1)
                 (opcode_single : symState.executionEnv.code = ⟨#[opcode]⟩)
                 (stack_ok : symState.stack.length < 1025):
  X gas symValidJumps symState =
  Except.ok (.success {symState with
      returnData := ByteArray.empty,
      execLength := symState.execLength + 1} ByteArray.empty) := by
  cases cgas: gas; rw [cgas] at gpos; contradiction
  simp_all [X, δ, α]; split; aesop (add safe (by contradiction)) (add safe (by linarith))
  dsimp [Except.instMonad, Except.bind]; rename_i n _ _ _ heq
  revert heq; split; aesop (add safe (by contradiction)) (add safe (by linarith))
  simp [pure, Except.pure]; intro evm_eq cost; subst evm_eq cost
  cases n; contradiction
  simp [StopSummary.EVM.step_stop_summary_simple]

end
