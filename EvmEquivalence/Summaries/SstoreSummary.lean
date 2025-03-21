import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
--import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open EvmYul.State

namespace SstoreSummary

section

variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc : UInt256)
variable (symGasAvailable key value : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)

@[simp]
abbrev sstoreEVM := @Operation.SSTORE .EVM

@[simp]
abbrev sstore_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨sstoreEVM, none⟩

@[simp]
def EVM.step_sstore : Transformer :=
  EVM.step false gas gasCost sstore_instr

@[simp]
def EvmYul.step_sstore : Transformer :=
  EvmYul.step false sstoreEVM

/--
Theorem needed to bypass the `private` attribute of `EVM.dispatchBinaryStateOp`
 -/
theorem sstore_bypass_private {symState : EVM.State}:
  EvmYul.step_sstore symState =
  EVM.binaryStateOp false EvmYul.State.sstore symState := rfl

@[simp]
def accountMap_sstore (symState : EVM.State) (key value : UInt256) : AccountMap :=
  let Iₐ := symState.toState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState.toState Iₐ)
  match ownerAcc with
  | none => symState.toState.accountMap
  | some ownerAcc =>
    symState.accountMap.insert Iₐ (Account.updateStorage (ownerAcc) key value)

@[simp]
def accessedStorageKeys_sstore (symState : EVM.State) (key : UInt256) :=
  let Iₐ := symState.toState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState.toState Iₐ)
  match ownerAcc with
  | none => symState.substate.accessedStorageKeys
  | some _ => symState.substate.accessedStorageKeys.insert ⟨Iₐ, key⟩

theorem sstore_summary (symState : EVM.State) (key value : UInt256):
  ∃ Aᵣ: UInt256, State.sstore symState.toState key value =
    {symState with
      accountMap := accountMap_sstore symState key value
      substate.accessedStorageKeys := accessedStorageKeys_sstore symState key
      substate.refundBalance := Aᵣ
    } := by
  cases cco: (symState.lookupAccount symState.toState.executionEnv.codeOwner)
  all_goals aesop (add simp [sstore])

theorem EvmYul.step_sstore_summary (symState : EVM.State):
  ∃ Aᵣ: UInt256,
  EvmYul.step_sstore {symState with
    stack := key :: value :: symStack,
    pc := symPc} =
  .ok {symState with
    stack := symStack,
    accountMap := accountMap_sstore symState key value
    substate.accessedStorageKeys := accessedStorageKeys_sstore symState key
    substate.refundBalance := Aᵣ
    pc := symPc + .ofNat 1} := by
  rw [sstore_bypass_private]
  simp [binaryStateOp, Stack.pop2, Id.run, State.replaceStackAndIncrPC, State.incrPC]
  have _ := sstore_summary symState key value; aesop

end

end SstoreSummary
