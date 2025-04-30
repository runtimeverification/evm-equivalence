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
variable (symActiveWords : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
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
  accountMap := symAccounts,
  activeWords := symActiveWords,
  memory := symMemory,
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength}
  EvmYul.step_mstore ss =
  EVM.binaryMachineStateOp EvmYul.MachineState.mstore ss := rfl

/--
The new amount of `activeWords` based after running `MSTORE` with `offset`
and `currentAC` amount of active words
-/
def mstore_activeWords :=
  UInt256.ofNat (symActiveWords.toNat ⊔ (offset.toNat + 32 + 31) / 32)

/--
Writing `value` to `symMemory` starting at `offset`
-/
def mstore_memory_write :=
value.toByteArray.write 0 symMemory offset.toNat 32

theorem EvmYul.step_mstore_summary (symState : EVM.State):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EvmYul.step_mstore ss =
  .ok {ss with
    stack := symStack,
    pc := symPc + .ofNat 1
    memory := mstore_memory_write offset value symMemory,
    activeWords := mstore_activeWords offset symActiveWords} := by
  aesop (add simp [mstore_bypass_private])

theorem EVM.step_mstore_summary (gas_pos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EVM.step_mstore gas gasCost ss =
    .ok {ss with
          stack := symStack,
          pc := symPc + (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          memory := mstore_memory_write offset value symMemory,
          activeWords := mstore_activeWords offset symActiveWords
          execLength := symExecLength + 1} := by
  cases gas; contradiction
  simp [step_mstore, EVM.step]
  have srw := EvmYul.step_mstore_summary symStack symPc (symGasAvailable - UInt256.ofNat gasCost) symRefund offset value symActiveWords (symExecLength + 1) symReturnData symCode symMemory
  simp [EvmYul.step_mstore, Operation.MSTORE] at srw; aesop

end

end MstoreSummary
