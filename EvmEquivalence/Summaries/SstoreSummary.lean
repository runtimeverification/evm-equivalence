import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
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
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

@[simp]
abbrev sstoreEVM := @Operation.SSTORE .EVM

@[simp]
abbrev sstore_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨sstoreEVM, none⟩

@[simp]
abbrev EVM.step_sstore : Transformer :=
  EVM.step gas gasCost sstore_instr

@[simp]
abbrev EvmYul.step_sstore : Transformer :=
  EvmYul.step sstoreEVM

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
                  codeOwner := symCodeOwner
                  perm := symPerm},
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength,
  accountMap := symAccounts}
  EvmYul.step_sstore ss =
  EVM.binaryStateOp EvmYul.State.sstore ss := rfl

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
                  codeOwner := symCodeOwner
                  perm := symPerm},
             substate := {symState.substate with
                          accessedStorageKeys :=  symAccessedStorageKeys
                          refundBalance := symRefund}
             accountMap := symAccounts}
  State.sstore ss key value =
  {ss with
    accountMap := accountMap_sstore ss key value,
    substate := {ss.substate with
      accessedStorageKeys :=
        accessedStorageKeys_sstore ss key
        --ss.substate.accessedStorageKeys.insert (symCodeOwner, key),
      refundBalance := Aᵣ_sstore ss key value}} := by
  simp [sstore, Option.option, lookupAccount]
  split <;> simp_all [setAccount, addAccessedStorageKey, Substate.addAccessedStorageKey]
  congr <;> (split <;> rw [σ₀] at * <;> simp_all [Batteries.RBMap.find!]; eq_refl)
  -- Before, this used to work
  /- cases cco: (symState.lookupAccount symState.executionEnv.codeOwner)
  all_goals aesop (add simp [sstore, Aᵣ_sstore, Option.option, lookupAccount]) -/

theorem EvmYul.step_sstore_summary (symState : EVM.State):
  let ss := {symState with
    stack := key :: value :: symStack,
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
                  codeOwner := symCodeOwner
                  perm := true},
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

@[simp]
theorem decode_singleton_sstore :
  decode ⟨#[0x55]⟩ (.ofNat 0) = some ⟨sstoreEVM, none⟩ := rfl

@[simp]
theorem memoryExpansionCost_sstore (symState : EVM.State) :
  memoryExpansionCost symState sstoreEVM = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

/-
TODO: Generalize to `C'`
 -/

theorem Csstore_pos (symState : EVM.State) : 99 < Csstore symState := by
  unfold Csstore GasConstants.Gcoldsload GasConstants.Gwarmaccess GasConstants.Gsset GasConstants.Gsreset
  split; split; split
  . simp; split
    . simp; split <;> first | simp | split <;> simp
    . split <;> first | simp | split <;> simp
  . simp; split <;> first | simp | split <;> try simp
    . split <;> first | simp | split <;> simp
    . split <;> simp
  -- Before this was enough
  -- aesop (add simp [Csstore, GasConstants.Gwarmaccess, GasConstants.Gsset, GasConstants.Gsreset])

theorem X_sstore_summary (symState : EVM.State)
                         (symStack_ok : symStack.length < 1024)
                         (gasStippend : GasConstants.Gcallstipend < symGasAvailable.toNat):
  let ss := {symState with
    stack := key :: value :: symStack,
    pc := .ofNat 0
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := ⟨#[(0x55 : UInt8)]⟩,
                  codeOwner := symCodeOwner
                  perm := true},
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength,
    accountMap := symAccounts}
  Csstore ss < symGasAvailable.toNat →
  X symGasAvailable.toNat symValidJumps ss =
  .ok (.success {ss with
          stack := symStack,
          pc := .ofNat 1,
          gasAvailable := symGasAvailable - (.ofNat (Csstore ss)),
          accountMap := accountMap_sstore ss.toState key value
          substate := {ss.substate with
            accessedStorageKeys := accessedStorageKeys_sstore ss.toState key
            refundBalance := Aᵣ_sstore ss.toState key value
           }
          returnData := .empty,
          execLength := symExecLength + 2} .empty) := by
  intro ss enoughGas
  have gavail_pos := Nat.lt_trans (Csstore_pos ss) enoughGas
  cases g_case : symGasAvailable.toNat; rw [g_case] at gavail_pos; contradiction
  case succ g_pos =>
  simp [X, C', δ]
  have lt_fls_rw {n m : ℕ} (_ : n < m) : (m < n) = False := by
    simp; apply Nat.ge_of_not_lt; simp; omega
  simp [ss, (lt_fls_rw enoughGas), α, (lt_fls_rw symStack_ok)]
  have g_rw : (symGasAvailable.toNat ≤ GasConstants.Gcallstipend) = False := by aesop
  simp [g_rw]; split; contradiction; next evm cost stateOk =>
  have step_rw := (EVM.step_sstore_summary g_pos (Csstore evm) symStack (.ofNat 0)
    symGasAvailable symRefund key value symExecLength symReturnData ⟨#[(0x55 : UInt8)]⟩
    symAccessedStorageKeys symAccounts symCodeOwner (by omega) evm)
  cases stateOk; simp at step_rw; rw [step_rw]; simp [Except.instMonad, Except.bind]
  rw [X_bad_pc] <;> aesop (add safe (by omega))

end

end SstoreSummary
