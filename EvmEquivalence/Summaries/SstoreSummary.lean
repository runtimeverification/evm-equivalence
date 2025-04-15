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
variable (symPc symGasAvailable symRefund key value : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner : AccountAddress)

@[simp]
abbrev sstoreEVM := @Operation.SSTORE .EVM

@[simp]
abbrev sstore_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨sstoreEVM, none⟩

@[simp]
abbrev EVM.step_sstore : Transformer :=
  EVM.step false gas gasCost sstore_instr

@[simp]
abbrev EvmYul.step_sstore : Transformer :=
  EvmYul.step false sstoreEVM

/--
Theorem needed to bypass the `private` attribute of `EVM.dispatchBinaryStateOp`
 -/
theorem sstore_bypass_private (symState : EVM.State):
  let ss := {symState with
  stack := key :: value :: symStack,
  pc := symPc
  gasAvailable := symGasAvailable,
  executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner},
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength,
  accountMap := symAccounts}
  EvmYul.step_sstore ss =
  EVM.binaryStateOp false EvmYul.State.sstore ss := rfl

@[simp]
def accountMap_sstore (symState : EvmYul.State) (key value : UInt256) : AccountMap :=
  let Iₐ := symState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState Iₐ)
  match ownerAcc with
  | none => symState.accountMap
  | some ownerAcc =>
    symState.accountMap.insert Iₐ (Account.updateStorage (ownerAcc) key value)

@[simp]
def accessedStorageKeys_sstore (symState : EvmYul.State) (key : UInt256) :=
  let Iₐ := symState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState Iₐ)
  match ownerAcc with
  | none => symState.substate.accessedStorageKeys
  | some _ => symState.substate.accessedStorageKeys.insert ⟨Iₐ, key⟩

-- From EvmYul.StateOps.sstore
@[local simp]
def Aᵣ_sstore (symState: EvmYul.State) (key val : UInt256) : UInt256 :=
    let Iₐ := symState.executionEnv.codeOwner
  let { storage := σ_Iₐ, .. } := symState.accountMap.find! Iₐ
  let { storage := σ₀_Iₐ, .. } := symState.σ₀.find! Iₐ
  let v₀ := σ₀_Iₐ.findD key ⟨0⟩
  let v := σ_Iₐ.findD key ⟨0⟩
  let v' := val

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let Iₐ := symState.executionEnv.codeOwner
  let ownerAcc := (State.lookupAccount symState Iₐ)
  match ownerAcc with
  | none => symState.substate.refundBalance
  | some _ =>
    match ΔAᵣ with
        | .ofNat n => symState.substate.refundBalance + .ofNat n
        | .negSucc n => symState.substate.refundBalance - .ofNat n - ⟨1⟩

theorem sstore_summary (symState : EvmYul.State) (key value : UInt256):
  let ss := {symState with
             executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner},
             substate := {symState.substate with
                          accessedStorageKeys :=  symAccessedStorageKeys
                          refundBalance := symRefund}
             accountMap := symAccounts}
  State.sstore ss key value =
  {ss with
    accountMap := accountMap_sstore ss key value,
    substate.accessedStorageKeys := accessedStorageKeys_sstore ss key,
    substate.refundBalance := Aᵣ_sstore ss key value} := by
  cases cco: (symState.lookupAccount symState.executionEnv.codeOwner)
  all_goals aesop (add simp [sstore, Aᵣ_sstore, Option.option, lookupAccount])

theorem EvmYul.step_sstore_summary (symState : EVM.State):
  let ss := {symState with
    stack := key :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner},
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength,
    accountMap := symAccounts}
  EvmYul.step_sstore ss =
  .ok {ss with
    stack := symStack,
    pc := symPc + .ofNat 1
    accountMap := accountMap_sstore ss.toState key value
    substate.accessedStorageKeys := accessedStorageKeys_sstore ss.toState key
    substate.refundBalance := Aᵣ_sstore ss.toState key value} := by
  simp [sstore_bypass_private, binaryStateOp, Stack.pop2, Id.run, State.replaceStackAndIncrPC, State.incrPC]
  aesop (add simp [sstore_summary])

theorem EVM.step_sstore_summary (gas_pos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := key :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner},
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength,
    accountMap := symAccounts}
  EVM.step_sstore gas gasCost ss =
    .ok {ss with
          stack := symStack,
          pc := symPc + (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          accountMap := accountMap_sstore ss.toState key value
          substate := {ss.substate with
            accessedStorageKeys := accessedStorageKeys_sstore ss.toState key
            refundBalance := Aᵣ_sstore ss.toState key value
           }
          execLength := symExecLength + 1} := by
  cases gas; contradiction
  simp [step_sstore, EVM.step]
  have srw := EvmYul.step_sstore_summary symStack symPc (symGasAvailable - UInt256.ofNat gasCost) symRefund key value (symExecLength + 1) symReturnData symCode
  simp [EvmYul.step_sstore, Operation.SSTORE] at srw; aesop

end

end SstoreSummary
