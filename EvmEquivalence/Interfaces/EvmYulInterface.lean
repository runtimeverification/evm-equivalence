import EvmYul.EVM.Semantics
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Utils.IntUtils


open EvmYul
open EVM

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
                 {symState : EVM.State}
                 (gpos : 1 < gas)
                 (pc1 : symState.pc = .ofNat 1)
                 (opcode_single : symState.executionEnv.code = ⟨#[opcode]⟩)
                 (stack_ok : symState.stack.length < 1025):
  X false gas symState =
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
