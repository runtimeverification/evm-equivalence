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

/- This probably should be deleted -/
theorem sstore_rw {symState : EVM.State} {key value : UInt256}:
  ∃ Aᵣ: UInt256, State.sstore symState.toState key value =
  let Iₐ := symState.toState.executionEnv.codeOwner
  (Option.option symState.toState (λ acc ↦
    let self' :=
      symState.toState.setAccount Iₐ (Account.updateStorage acc key value)
        |>.addAccessedStorageKey (Iₐ, key)
    { self' with substate.refundBalance := Aᵣ}))
    (State.lookupAccount symState.toState Iₐ):= by aesop

theorem sstore_summary {symState : EVM.State} {key value : UInt256}:
  ∃ Aᵣ: UInt256, State.sstore symState.toState key value =
  let Iₐ := symState.toState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState.toState Iₐ)
  match ownerAcc with
  | none =>
    {symState with
      accountMap := symState.toState.accountMap
      substate.accessedStorageKeys := symState.substate.accessedStorageKeys
      substate.refundBalance := Aᵣ
    }
  | some ownerAcc =>
    {symState with
      accountMap := symState.accountMap.insert Iₐ (Account.updateStorage (ownerAcc) key value)
      substate.accessedStorageKeys := symState.substate.accessedStorageKeys.insert ⟨Iₐ, key⟩
      substate.refundBalance := Aᵣ
    } := by
  cases cco: (symState.lookupAccount symState.toState.executionEnv.codeOwner)
  all_goals aesop (add simp [sstore])

theorem EvmYul.step_sstore_summary (symState : EVM.State):
  EvmYul.step_sstore {symState with
    stack := key :: value :: symStack,
    pc := symPc} =
  .ok {symState with
    stack := symStack,
    pc := symPc + .ofNat 1} := by
  rw [sstore_bypass_private]
  simp [binaryStateOp, Stack.pop2, Id.run, State.replaceStackAndIncrPC, State.incrPC]
  have sstoreRw := @sstore_rw symState key value
  rcases sstoreRw; case intro gas ss_rw =>
  simp [ss_rw]
  rw [sstore_rw]
  simp [State.addAccessedStorageKey, Account.updateStorage, State.setAccount]
  cases value_default : (value == default) <;> simp
  case false =>


  simp [Batteries.RBMap.insert, Batteries.RBSet.insert, Batteries.RBNode.insert]
  --simp [EvmYul.step, Id.run]
  --simp [Id.run]
  rw [step_sstore_rw]


end

end SstoreSummary
