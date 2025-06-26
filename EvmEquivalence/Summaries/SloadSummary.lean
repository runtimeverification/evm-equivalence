import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open EvmYul.State

namespace SloadSummary

section

variable (gas gasCost symGasPrice symTimestamp : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund key value symActiveWords : UInt256)
variable (symPrevrandao : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner symSender symSource symCoinbase : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

@[simp]
abbrev sloadEVM := @Operation.SLOAD .EVM

@[simp]
abbrev sload_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨sloadEVM, none⟩

@[simp]
abbrev EVM.step_sload : Transformer :=
  EVM.step gas gasCost sload_instr

@[simp]
abbrev EvmYul.step_sload : Transformer :=
  EvmYul.step sloadEVM

@[simp]
def lookupStorage_sload (symState : EvmYul.State) (key : UInt256) : UInt256 :=
  let Iₐ := symState.executionEnv.codeOwner
  match symState.lookupAccount Iₐ with
  | none => ⟨0⟩
  | some acc => acc.lookupStorage key

theorem sload_summary (symState : EvmYul.State) (key : UInt256):
  let ss := {symState with
             executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    prevRandao := symPrevrandao
                  }
                  perm := symPerm},
             substate := {symState.substate with
                          accessedStorageKeys :=  symAccessedStorageKeys
                          refundBalance := symRefund}
             accountMap := symAccounts}
  State.sload ss key =
  (addAccessedStorageKey ss (symCodeOwner, key),
    lookupStorage_sload ss key) := by
  cases cco: (symState.lookupAccount symState.executionEnv.codeOwner)
  all_goals aesop (add simp [sload, Option.option, lookupAccount, Substate.addAccessedStorageKey])

/--
Theorem needed to bypass the `private` attribute of `EVM.dispatchBinaryStateOp`
 -/
theorem sload_bypass_private (symState : EVM.State):
  let ss := {symState with
  stack := symStack,
  pc := symPc
  gasAvailable := symGasAvailable,
  executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    prevRandao := symPrevrandao
                  }
                  perm := symPerm},
  accountMap := symAccounts,
  activeWords := symActiveWords,
  memory := symMemory,
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength}
  EvmYul.step_sload ss =
  EVM.unaryStateOp EvmYul.State.sload ss := rfl

theorem EvmYul.step_sload_summary (symState : EVM.State):
  let ss := {symState with
    stack := key :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    prevRandao := symPrevrandao
                  }
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EvmYul.step_sload ss =
  .ok {ss with
    stack := lookupStorage_sload ss.toState key :: symStack,
    pc := symPc + .ofNat 1
    substate.accessedStorageKeys := ss.substate.accessedStorageKeys.insert ⟨ss.executionEnv.codeOwner, key⟩} := by
  simp [sload_bypass_private, unaryStateOp, Stack.pop, Id.run, State.replaceStackAndIncrPC, State.incrPC, sload, lookupAccount]
  aesop (add simp [sload_summary, Substate.addAccessedStorageKey])

theorem EVM.step_sload_summary (gas_pos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := key :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    prevRandao := symPrevrandao
                  }
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EVM.step_sload gas gasCost ss =
    .ok {ss with
          stack := lookupStorage_sload ss.toState key :: symStack,
          pc := symPc + (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          substate := {ss.substate with
            accessedStorageKeys := ss.substate.accessedStorageKeys.insert ⟨ss.executionEnv.codeOwner, key⟩
           }
          execLength := symExecLength + 1} := by
  cases gas; contradiction
  simp [step_sload, EVM.step]
  have srw := EvmYul.step_sload_summary symGasPrice symTimestamp symStack symPc (symGasAvailable - UInt256.ofNat gasCost) symRefund key symActiveWords symPrevrandao (symExecLength + 1) symReturnData symCode symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm
  simp [EvmYul.step_sload, Operation.SLOAD] at srw; simp [srw]

@[simp]
theorem decode_singleton_sload :
  decode ⟨#[0x54]⟩ (.ofNat 0) = some ⟨sloadEVM, none⟩ := rfl

@[simp]
theorem memoryExpansionCost_sload (symState : EVM.State) :
  memoryExpansionCost symState sloadEVM = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

/--
TODO: Generalize to `C'`
 -/
theorem Csload_pos (symState : EVM.State) : 99 < Csload symState.stack symState.substate symState.executionEnv := by
  aesop (add simp [Csload, GasConstants.Gcoldsload, GasConstants.Gwarmaccess])

theorem X_sload_summary (symState : EVM.State)
                         (symStack_ok : symStack.length < 1024):
  let ss := {symState with
    stack := key :: symStack,
    pc := .ofNat 0
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := ⟨#[(0x54 : UInt8)]⟩,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    prevRandao := symPrevrandao
                  }
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  Csload ss.stack ss.substate ss.executionEnv < symGasAvailable.toNat →
  X symGasAvailable.toNat symValidJumps ss =
  .ok (.success {ss with
          stack := lookupStorage_sload ss.toState key :: symStack,
          pc := .ofNat 1,
          gasAvailable := symGasAvailable - (.ofNat (Csload ss.stack ss.substate ss.executionEnv)),
          substate := {ss.substate with
            accessedStorageKeys := ss.substate.accessedStorageKeys.insert ⟨ss.executionEnv.codeOwner, key⟩
           }
          returnData := .empty,
          execLength := symExecLength + 2} .empty) := by
  intro ss enoughGas
  have gavail_pos := Nat.lt_trans (Csload_pos ss) enoughGas
  cases g_case : symGasAvailable.toNat; rw [g_case] at gavail_pos; contradiction
  case succ g_pos =>
  simp [X, C', δ]
  have lt_fls_rw {n m : ℕ} (_ : n < m) : (m < n) = False := by
    simp; apply Nat.ge_of_not_lt; simp; omega
  simp [ss, (lt_fls_rw enoughGas), α, (lt_fls_rw symStack_ok)]
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    aesop (add safe (by linarith))
  simp [stack_ok_rw]; split; contradiction; next evm cost stateOk =>
  have step_rw := (EVM.step_sload_summary g_pos (Csload ss.stack ss.substate ss.executionEnv) symGasPrice symTimestamp symStack (.ofNat 0)
    symGasAvailable symRefund key  symActiveWords symPrevrandao symExecLength symReturnData ⟨#[(0x54 : UInt8)]⟩
    symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm (by omega) evm)
  cases stateOk; simp at step_rw; rw [step_rw]; simp [Except.instMonad, Except.bind]
  rw [X_bad_pc] <;> aesop (add safe (by omega))

end

end SloadSummary
