import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Summaries.StopSummary

open EvmYul
open EVM

namespace Push0Summary

section

variable {gas gasCost : ℕ}
variable {symStack : Stack UInt256}
variable {symPc : UInt256}
variable {symGasAvailable : UInt256}
variable {symExecLength : ℕ}
variable {symReturnData symCode : ByteArray}

abbrev push0EVM := @Operation.PUSH0
abbrev push0_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨push0EVM, none⟩

def EVM.step_push0 : Transformer :=
  EVM.step false gas gasCost push0_instr

def EvmYul.step_push0 : Transformer :=
  @EvmYul.step OperationType.EVM false push0EVM

theorem EvmYul.step_push0_summary (symState : EVM.State):
  EvmYul.step_push0 {symState with
    stack := symStack,
    pc := symPc} = default := rfl

theorem EVM.step_push0_summary_simple (gpos : 0 < gas) (symState : EVM.State):
  @EVM.step_push0 gas gasCost symState =
    .ok {symState with
    stack := (.ofNat 0) :: symState.stack
    gasAvailable := symState.gasAvailable - UInt256.ofNat gasCost
    pc := symState.pc + .ofNat 1,
    execLength := symState.execLength + 1} := by
  cases gas; contradiction; rfl

theorem EVM.step_push0_summary (gpos : 0 < gas) (symState : EVM.State):
  @EVM.step_push0 gas gasCost
    {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength,
      executionEnv := {symState.executionEnv with code := symCode},
      returnData := symReturnData} =
    .ok {symState with
    stack := (.ofNat 0) :: symStack
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc + .ofNat 1,
    executionEnv := {symState.executionEnv with code := symCode},
    returnData := symReturnData,
    execLength := symExecLength + 1} := by
  cases gas; contradiction; rfl

@[simp]
theorem decode_singleton_push0 :
  decode ⟨#[0x5F]⟩ (.ofNat 0) = some ⟨push0EVM, none⟩ := rfl

@[simp]
theorem memoryExpansionCost_push0 (symState : EVM.State) :
  memoryExpansionCost symState push0EVM = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp]
theorem C'_push0 (symState : EVM.State) :
  C' symState push0EVM = GasConstants.Gbase := by rfl

theorem X_bad_pc {opcode : UInt8}
                 {symState : EVM.State}
                 (gpos : 2 <= gas)
                 (pc1 : symState.pc = .ofNat 1)
                 (opcode_single : symState.executionEnv.code = ⟨#[opcode]⟩)
                 (stack_ok : symState.stack.length < 1024)
                 (empty_output : symState.returnData = ByteArray.empty):
  X false gas symState =
  Except.ok (.success {symState with
      execLength := symState.execLength + 1} ByteArray.empty) := by
  cases cgas: gas; rw [cgas] at gpos; contradiction
  simp_all [X, δ, α]
  have stack_ok_rw : (1024 < List.length symState.stack) = False :=
    by aesop (add safe (by omega))
  split; aesop (add safe (by contradiction)) (add safe (by linarith))
  dsimp [Except.instMonad, Except.bind]
  rename_i n _ _ _ heq
  revert heq; split; aesop (add safe (by contradiction)) (add safe (by linarith))
  intro heq
  simp [pure, Except.pure] at heq; cases heq; case intro evm_eq cost =>
  subst cost evm_eq
  have npos : 0 < n := by omega
  cases cn : n; rw [cn] at npos; contradiction
  simp [StopSummary.EVM.step_stop_summary_simple]; congr; simp [empty_output]

theorem X_push0_summary (enoughGas : GasConstants.Gbase < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < 1023)
                      (symState : EVM.State):
  X false symGasAvailable.toNat
  {symState with
    stack := symStack,
    pc := .ofNat 0,
    execLength := symExecLength,
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with code := ⟨#[(0x5f : UInt8)]⟩}
    returnData := ByteArray.empty} =
  Except.ok (.success {symState with
        stack := (.ofNat 0) :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat GasConstants.Gbase,
        executionEnv := {symState.executionEnv with code := ⟨#[(0x5F : UInt8)]⟩},
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  cases g_case: symGasAvailable.toNat
  case zero => rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gbase) = False :=
    by aesop (add safe (by omega))
  have stack_ok_rw : (1024 < List.length symStack + (α push0EVM).getD 0) = False :=
    by simp [α]; omega
  have gPos : (0 < g_pos) := by aesop (add simp [GasConstants.Gbase]) (add safe (by omega))
  simp [X, δ, enough_gas_rw, stack_ok_rw]; split; contradiction
  case h_2 evm _ stateOk =>
  simp [pure, Except.pure] at stateOk; cases stateOk; case intro evm_eq cost=>
  subst cost evm_eq
  dsimp [Except.instMonad, Except.bind]
  have step_rw := (@EVM.step_push0_summary g_pos GasConstants.Gbase symStack (.ofNat 0) symGasAvailable symExecLength ByteArray.empty ⟨#[(0x5F : UInt8)]⟩ gPos)
  rw [EVM.step_push0, push0_instr] at step_rw; simp [step_rw]
  rw [X_bad_pc] <;> aesop (add simp [GasConstants.Gbase]) (add safe (by omega))

end

end Push0Summary
