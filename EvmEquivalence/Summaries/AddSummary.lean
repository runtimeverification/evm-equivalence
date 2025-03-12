import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open StopSummary

namespace AddSummary

section

variable (word₁ word₂ : UInt256)
variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc : UInt256)
variable (symGasAvailable : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)

abbrev addEVM := @Operation.ADD .EVM

abbrev add_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨addEVM, none⟩

def EVM.step_add : Transformer :=
  EVM.step false gas gasCost add_instr

def EvmYul.step_add : Transformer :=
  @EvmYul.step OperationType.EVM false addEVM

theorem EvmYul.step_add_summary (symState : EVM.State):
  EvmYul.step_add {symState with
    stack := word₁ :: word₂ :: symStack,
    pc := symPc} =
  .ok {symState with
        stack := (word₁ + word₂) :: symStack
        pc := symPc + .ofNat 1} := rfl

theorem EVM.step_add_to_step_add (gpos : 0 < gas) (symState : EVM.State):
  EVM.step_add gas gasCost
    {symState with
      stack := word₁ :: word₂ :: symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength,
      executionEnv := {symState.executionEnv with code := symCode},
      returnData := symReturnData} =
  EvmYul.step_add
    {symState with
    stack := word₁ :: word₂ :: symStack
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc,
    executionEnv := {symState.executionEnv with code := symCode},
    returnData := symReturnData,
    execLength := symExecLength + 1} := by
      cases gas; contradiction
      simp [EVM.step_add, EVM.step]; rfl

theorem EVM.step_add_summary (gpos : 0 < gas) (symState : EVM.State):
  EVM.step_add gas gasCost
    {symState with
      stack := word₁ :: word₂ :: symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      returnData := symReturnData,
      executionEnv := {symState.executionEnv with code := symCode},
      execLength := symExecLength} =
    .ok {symState with
          stack := (word₁ + word₂) :: symStack,
          pc := UInt256.add symPc (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          returnData := symReturnData,
          executionEnv := {symState.executionEnv with code := symCode},
          execLength := symExecLength + 1} := by
  rw [EVM.step_add_to_step_add]; rfl; assumption

----
-- For having symbolic programs instead of singleton ones
/- abbrev addBytecode (preCode postCode : Array UInt8) : ByteArray :=
  ⟨preCode ++ #[(0x01 : UInt8)] ++ postCode⟩

abbrev addInstr (preCode postCode : Array UInt8) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
decode (addBytecode preCode postCode) (.ofNat preCode.size)

theorem array_append_size_comm {α : Type} (a1 a2 : Array α) :
  (a1 ++ a2).size <= (a2 ++ a1).size := by sorry

theorem array_append_size_le {α : Type} (a1 a2 : Array α) :
  a1.size <= (a1 ++ a2).size := by sorry -/

--set_option maxHeartbeats 3000000
/- theorem addInst_eq (preCode postCode : Array UInt8)
                   (preCode_size_ok : preCode.size < UInt256.size) : addInstr preCode postCode = add_instr := by
  simp [add_instr, addEVM, addInstr, addBytecode, decode] -/
  /- split
  case isTrue => sorry
    --simp [parseInstr]
    --rw [ofNat_toNat_eq]
  case isFalse fls =>
    have h_true : (UInt256.ofNat preCode.size).toNat < preCode.size + (1 + postCode.size) := sorry
    contradiction -/
----

@[simp]
theorem decode_singleton_add :
  decode ⟨#[0x1]⟩ (.ofNat 0) = some ⟨addEVM, none⟩ := rfl

@[simp]
theorem memoryExpansionCost_add (symState : EVM.State) :
  memoryExpansionCost symState addEVM = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp]
theorem C'_add (symState : EVM.State) :
  C' symState addEVM = GasConstants.Gverylow := rfl

@[simp]
theorem C'_stop (symState : EVM.State) :
  C' symState .STOP = 0 := rfl

theorem X_add_summary (enoughGas : GasConstants.Gverylow < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < 1024)
                      (symState : EVM.State):
  X false symGasAvailable.toNat
  {symState with
    stack := word₁ :: word₂ :: symStack,
    pc := .ofNat 0,
    execLength := symExecLength,
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with code := ⟨#[(0x1 : UInt8)]⟩}
    returnData := symReturnData} =
  Except.ok (.success {symState with
        stack := (word₁ + word₂) :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat GasConstants.Gverylow,
        executionEnv := {symState.executionEnv with code := ⟨#[(0x1 : UInt8)]⟩},
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  cases g_case: symGasAvailable.toNat
  case zero => rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  have ss_lt2_f  (n : ℕ) : (n + 1 + 1 < 2) = False := by simp
  simp [X, δ, ss_lt2_f]
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    aesop (add safe (by omega))
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gverylow) = False :=
    by aesop (add safe (by omega))
  simp [α, stack_ok_rw, enough_gas_rw]
  split; contradiction
  case h_2 evm _ stateOk =>
  have g_pos_gt_1 : (1 < g_pos) := by
    aesop (add simp [GasConstants.Gverylow]) (add safe (by omega))
  have gPos : (0 < g_pos) := by aesop (add safe (by omega))
  have step_rw := (EVM.step_add_summary word₁ word₂ g_pos GasConstants.Gverylow symStack (.ofNat 0) symGasAvailable symExecLength symReturnData ⟨#[(0x1 : UInt8)]⟩ gPos evm)
  cases stateOk; rw [←EVM.step_add, step_rw]
  dsimp [Except.instMonad, Except.bind]; rw [X.eq_def]
  cases cgp: g_pos; rw [cgp] at gPos; contradiction
  case succ n =>
  -- part of this could be a lemma
  simp [memoryExpansionCost, Cₘ, memoryExpansionCost.μᵢ', decode, ByteArray.get?]
  have bad_opcode : (((UInt256.ofNat 0).add (UInt256.ofNat 1)).toNat < ({data := #[1] } : ByteArray).size) = False :=
    by aesop
  simp [bad_opcode, δ, α, stack_ok_rw]; split <;> try contradiction
  case h_2 _ _ stateOk =>
  cases stateOk; aesop (add simp [EVM.step_stop_summary_simple])

end

end AddSummary
