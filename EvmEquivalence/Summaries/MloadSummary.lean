import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Summaries.MstoreSummary

open EvmYul
open EVM
open EvmYul.State

namespace MloadSummary

section

variable (gas gasCost symGasPrice symTimestamp symNumber symGaslimit : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund offset : UInt256)
variable (symActiveWords symPrevrandao : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner symSender symSource symCoinbase : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

@[simp]
abbrev mloadEVM := @Operation.MLOAD .EVM

@[simp]
abbrev mload_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨mloadEVM, none⟩

@[simp]
abbrev EVM.step_mload : Transformer :=
  EVM.step gas gasCost mload_instr

@[simp]
abbrev EvmYul.step_mload : Transformer :=
  EvmYul.step mloadEVM

abbrev activeWords_comp := MstoreSummary.activeWords_comp

theorem EvmYul.step_mload_summary (symState : EVM.State):
  let ss := {symState with
    stack := offset :: symStack,
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
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EvmYul.step_mload ss =
  .ok {ss with
    stack := (EvmYul.MachineState.lookupMemory ss.toMachineState offset) :: symStack,
    pc := symPc + .ofNat 1,
    activeWords := activeWords_comp offset symActiveWords 32} := by aesop

theorem EVM.step_mload_summary (gas_pos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := offset :: symStack,
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
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EVM.step_mload gas gasCost ss =
    .ok {ss with
          stack := (EvmYul.MachineState.lookupMemory ss.toMachineState offset) :: symStack
          pc := symPc + (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          activeWords := activeWords_comp offset symActiveWords 32
          execLength := symExecLength + 1} := by
  cases gas; contradiction
  simp [step_mload, EVM.step]
  have := EvmYul.step_mload_summary symGasPrice symTimestamp symNumber symGaslimit symStack symPc (symGasAvailable - UInt256.ofNat gasCost) symRefund offset symActiveWords symPrevrandao (symExecLength + 1) symReturnData symCode symMemory
  simp [EvmYul.step_mload, Operation.MLOAD] at this; aesop

@[simp]
theorem decode_singleton_mload :
  decode ⟨#[0x51]⟩ (.ofNat 0) = some ⟨mloadEVM, none⟩ := rfl

@[simp]
def value_and_activeWords_gas (s : EVM.State) :=
  UInt256.ofNat (MachineState.M symActiveWords.toNat s.stack[0]!.toNat 32)

@[simp]
theorem memoryExpansionCost_mload (symState : EVM.State)
  --(stack_ok : symState.stack = value :: symStack)
  (symWords_ok : symState.activeWords = symActiveWords):
  memoryExpansionCost symState mloadEVM =
  Cₘ (value_and_activeWords_gas symActiveWords symState) - Cₘ symActiveWords := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  simp [Cₘ, symWords_ok]

theorem X_mload_summary (symState : EVM.State)
                         (symStack_ok : symStack.length < 1024):
  let ss := {symState with
    stack := offset :: symStack,
    pc := .ofNat 0
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := ⟨#[(0x51 : UInt8)]⟩,
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
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  -- Assume we have enough gas
  GasConstants.Gverylow < symGasAvailable.toNat - (memoryExpansionCost ss Operation.MLOAD) →
  memoryExpansionCost ss Operation.MLOAD < UInt256.size →
  X symGasAvailable.toNat symValidJumps ss =
  .ok (.success {ss with
          stack := (EvmYul.MachineState.lookupMemory ss.toMachineState offset) :: symStack,
          pc := .ofNat 1,
          gasAvailable := symGasAvailable - .ofNat (memoryExpansionCost ss mloadEVM) - .ofNat GasConstants.Gverylow,
          activeWords := activeWords_comp offset symActiveWords 32
          returnData := .empty,
          execLength := symExecLength + 2} .empty) := by
  intro ss enoughGas mec_small
  have gavail_pos : 1 < symGasAvailable.toNat := by
    rw [GasConstants.Gverylow] at enoughGas; omega
  cases g_case : symGasAvailable.toNat; omega
  rename_i g_pos
  simp [X, C', δ]
  -- This result is not explicitly used but is needed for automation
  have lt_fls_rw {n m : ℕ} (_ : n < m) : (m < n) = False := by
    simp; apply Nat.ge_of_not_lt; simp; omega
  -- The many comments that are in the proof were put after upgrading
  -- to Lean 4.22.0. They should be removed once it's shown that the
  -- proof is stable w.r.t. future versions of Lean
  simp [/- (lt_fls_rw enoughGas), -/ α/- , (lt_fls_rw symStack_ok) -/]
  /- have fls1 : (symGasAvailable.toNat < memoryExpansionCost ss (@Operation.MLOAD .EVM)) = False :=  by
    rw [Nat.lt_sub_iff_add_lt] at enoughGas
    aesop (add safe (by omega)) (add safe (by linarith)) (add simp [Cₘ, MachineState.M]) -/
  have decode_rw : ((decode ss.executionEnv.code ss.pc).getD ⟨@Operation.STOP .EVM, none⟩).1 = Operation.MLOAD := rfl
  /- have gavail_rw1 : ss.gasAvailable.toNat = symGasAvailable.toNat := rfl -/
  have gavail_rw2 : ss.gasAvailable = symGasAvailable := rfl
  simp [decode_rw, /- gavail_rw1, -/ gavail_rw2/- , fls1 -/]
  simp [InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount,
  InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
  -- the following statement is needed for automation
  have fls2 : ((symGasAvailable - UInt256.ofNat (memoryExpansionCost ss Operation.MLOAD)).toNat < GasConstants.Gverylow) = False := by
    apply eq_false_intro; rw [Nat.not_lt]
    have fls1 : (symGasAvailable.toNat < memoryExpansionCost ss (@Operation.MLOAD .EVM)) = False :=  by
      rw [Nat.lt_sub_iff_add_lt] at enoughGas
      aesop (add safe (by omega)) (add safe (by linarith)) (add simp [Cₘ, MachineState.M])
    rw [UInt256.toNat_sub_dist, UInt256.ofNat_toNat] <;>
    aesop (add simp [UInt256.ofNat_le, UInt256.ofNat_toNat])
  --have ss_lt2_f  (n : ℕ) : (n + 1 + 1 < 2) = False := by simp
  simp [/- fls2,  -/ss/- , ss_lt2_f, Nat.not_lt_of_lt symStack_ok -/]
  /- simp [memoryExpansionCost_mload symActiveWords, value_and_activeWords_gas, ss] at fls1 -/
  split; aesop (add safe (by omega)) (add safe (by linarith)) (add safe (by contradiction))
  next state n state_ok =>
  repeat split at state_ok <;>
  -- It is known that `aesop` doesn't fully close the goal in the follwing line
  try aesop (add safe (by omega)) (add safe (by linarith)) (add safe (by contradiction))
  cases state_ok
  have g_pos_pos : 0 < g_pos := by omega
  have step_rw (g : UInt256) := (EVM.step_mload_summary g_pos GasConstants.Gverylow symGasPrice symTimestamp symNumber symGaslimit symStack (.ofNat 0) (symGasAvailable - g) symRefund offset symActiveWords symPrevrandao symExecLength symReturnData ⟨#[(0x51 : UInt8)]⟩ symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm g_pos_pos symState)
  simp [EVM.step_mload, mload_instr, mloadEVM/- , ss -/] at step_rw
  simp [step_rw, Except.instMonad, Except.bind]
  rw [X_bad_pc] <;> aesop (add simp [GasConstants.Gverylow]) (add safe (by omega))

end

end MloadSummary
