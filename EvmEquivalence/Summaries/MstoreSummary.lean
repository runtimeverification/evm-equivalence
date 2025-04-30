import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open EvmYul.State

namespace MstoreSummary

section

variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund offset value : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

@[simp]
abbrev mstoreEVM := @Operation.MSTORE .EVM

@[simp]
abbrev mstore_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨mstoreEVM, none⟩

@[simp]
abbrev EVM.step_mstore : Transformer :=
  EVM.step gas gasCost mstore_instr

@[simp]
abbrev EvmYul.step_mstore : Transformer :=
  EvmYul.step mstoreEVM

/--
Theorem needed to bypass the `private` attribute of `EVM.dispatchBinaryMachineStateOp`
 -/
theorem mstore_bypass_private (symState : EVM.State):
  let ss := {symState with
  stack := symStack,
  pc := symPc
  gasAvailable := symGasAvailable,
  executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner
                  perm := symPerm},
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength,
  accountMap := symAccounts}
  EvmYul.step_mstore ss =
  EVM.binaryMachineStateOp EvmYul.MachineState.mstore ss := rfl



theorem EvmYul.step_sstore_summary (symState : EVM.State):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner
                  perm := symPerm},
    accountMap := symAccounts,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EvmYul.step_mstore ss =
  .ok {ss with
    stack := symStack,
    pc := symPc + .ofNat 1} := by
  simp [mstore_bypass_private, binaryMachineStateOp, Stack.pop2, Id.run, State.replaceStackAndIncrPC, State.incrPC]
  aesop (add simp [MachineState.mstore, MachineState.memory, MachineState.M])
  simp [MachineState.writeWord, writeBytes]
  -- aesop (add simp [mstore_summary])

end

end MstoreSummary
