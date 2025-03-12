import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants

open EvmYul
open EVM

namespace StopSummary

section

variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc : UInt256)
variable (symGasAvailable : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)

@[simp]
theorem C'_stop (symState : EVM.State) :
  C' symState .STOP = 0 := rfl

@[simp]
theorem memoryExpansionCost_stop (symState : EVM.State) :
  memoryExpansionCost symState .STOP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem EvmYul.step_stop_summary_simple (symState : EVM.State) :
  EvmYul.step false (@Operation.STOP .EVM) symState =
  .ok {symState with returnData := ByteArray.empty} := rfl

theorem EvmYul.step_stop_summary (symState : EVM.State) :
EvmYul.step false (@Operation.STOP .EVM)
  {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength}  =
  .ok {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength,
      returnData := ByteArray.empty} := rfl

theorem EVM.step_stop_summary_simple (gpos : 0 < gas) (symState : EVM.State) :
  EVM.step false gas gasCost (some (@Operation.STOP .EVM, none)) symState =
  .ok {symState with
    gasAvailable := symState.gasAvailable - UInt256.ofNat gasCost,
    returnData := ByteArray.empty
    execLength := symState.execLength + 1} := by
  cases cg: gas; rw [cg] at gpos; contradiction; rfl

theorem EVM.step_stop_summary (gpos : 0 < gas) (symState : EVM.State) :
  EVM.step false gas gasCost (some (@Operation.STOP .EVM, none))
    {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength} =
    .ok {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
      returnData := ByteArray.empty
      execLength := symExecLength + 1} := by
  cases cg: gas; rw [cg] at gpos; contradiction; rfl

end

end StopSummary
