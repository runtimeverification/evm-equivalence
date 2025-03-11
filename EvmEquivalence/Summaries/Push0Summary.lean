import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants

open EvmYul
open EVM

namespace Push0Summary

section

variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc : UInt256)
variable (symGasAvailable : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)

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

theorem EVM.step_push0_to_step_push0 (gpos : 0 < gas) (symState : EVM.State):
  EVM.step_push0 gas gasCost
    {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength,
      executionEnv := {symState.executionEnv with code := symCode},
      returnData := symReturnData} =
    .ok {symState with
    stack := (UInt256.ofNat 0) :: symStack
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc + .ofNat 1,
    executionEnv := {symState.executionEnv with code := symCode},
    returnData := symReturnData,
    execLength := symExecLength + 1} := by
  cases gas; contradiction; rfl

end

end Push0Summary
