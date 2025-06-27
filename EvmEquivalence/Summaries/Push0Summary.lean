import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Summaries.StopSummary

open EvmYul
open EVM

namespace Push0Summary

section

variable (gas gasCost symGasPrice symTimestamp symNumber symGaslimit : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund symActiveWords : UInt256)
variable (symPrevrandao : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner symSender symSource symCoinbase : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

@[simp]
abbrev push0EVM := @Operation.PUSH0

@[simp]
abbrev push0_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨push0EVM, none⟩

@[simp]
def EVM.step_push0 : Transformer :=
  EVM.step gas gasCost push0_instr

@[simp]
def EvmYul.step_push0 : Transformer :=
  @EvmYul.step OperationType.EVM push0EVM

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
  let ss :=
  {symState with
      stack := symStack,
      pc := symPc,
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
                    number := symNumber,
                    prevRandao := symPrevrandao,
                    gasLimit := symGaslimit
                  }
                  perm := symPerm},
      accountMap := symAccounts,
      activeWords := symActiveWords,
      memory := symMemory,
      substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
      returnData := symReturnData,
      execLength := symExecLength}
  @EVM.step_push0 gas gasCost ss =
    .ok {ss with
    stack := (.ofNat 0) :: symStack
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc + .ofNat 1,
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

theorem X_push0_summary (enoughGas : GasConstants.Gbase < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < 1024)
                      (symState : EVM.State):
  let ss :=
  {symState with
    stack := symStack,
    pc := .ofNat 0,
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := ⟨#[(0x5F : UInt8)]⟩,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  gasPrice := symGasPrice,
                  header := {symState.executionEnv.header with
                    beneficiary := symCoinbase,
                    timestamp := symTimestamp,
                    number := symNumber,
                    prevRandao := symPrevrandao,
                    gasLimit := symGaslimit
                  }
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
      memory := symMemory,
    substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
    returnData := symReturnData,
    execLength := symExecLength}
  X symGasAvailable.toNat symValidJumps ss =
  Except.ok (.success {ss with
        stack := (.ofNat 0) :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat GasConstants.Gbase,
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  cases g_case: symGasAvailable.toNat; rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gbase) = False :=
    by aesop (add safe (by omega))
  have stack_ok_rw : (1024 < List.length symStack + (α push0EVM).getD 0) = False :=
    by simp [α]; omega
  have gPos : (0 < g_pos) := by aesop (add simp [GasConstants.Gbase]) (add safe (by omega))
  simp [X, δ, enough_gas_rw, stack_ok_rw]; split; contradiction
  rename_i evm _ stateOk; revert stateOk
  simp [pure, Except.pure]; intro evm_eq cost; subst cost evm_eq
  dsimp [Except.instMonad, Except.bind]
  have step_rw := (@EVM.step_push0_summary g_pos GasConstants.Gbase symGasPrice symTimestamp symNumber symGaslimit symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symPrevrandao symExecLength symReturnData ⟨#[(0x5F : UInt8)]⟩ symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm gPos)
  rw [EVM.step_push0, push0_instr] at step_rw; simp [step_rw]
  rw [X_bad_pc] <;> aesop (add simp [GasConstants.Gbase]) (add safe (by omega))

end

end Push0Summary
