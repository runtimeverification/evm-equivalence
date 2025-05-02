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

@[simp]
theorem decode_singleton_sstore :
  decode ⟨#[0x52]⟩ (.ofNat 0) = some ⟨mstoreEVM, none⟩ := rfl

@[simp]
def value_and_activeWords_gas :=
  UInt256.ofNat (MachineState.M symActiveWords.toNat value.toNat 32)

@[simp]
theorem memoryExpansionCost_mstore (symState : EVM.State)
  (stack_ok : symState.stack = value :: symStack)
  (symWords_ok : symState.activeWords = symActiveWords):
  memoryExpansionCost symState mstoreEVM =
  Cₘ (value_and_activeWords_gas value symActiveWords) - Cₘ symActiveWords := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
  simp [Cₘ, stack_ok, symWords_ok]

/- This theorem is incorrect, needs more constraints to have a positive
 memory expansion gas cost -/
/-
Memory expansion cost for the `MSTORE` opcode is strictly positive
-/
/- theorem mec_mstore (symState : EVM.State)
  (stack_ok : symState.stack = value :: symStack)
  (words_ok : symState.activeWords = symActiveWords)
  (aw_gt_0 : 0 < symActiveWords.toNat)
  (value_big : symActiveWords.toNat < (value.toNat + 32 + 31) / 32)
  (enough_gas : symActiveWords.toNat ⊔ (value.toNat + 32 + 31) / 32 < UInt256.size):
  0 < memoryExpansionCost symState mstoreEVM := by
  simp [memoryExpansionCost, Cₘ, memoryExpansionCost.μᵢ', GasConstants.Gmemory, Cₘ.QuadraticCeofficient, MachineState.M]
  rw [UInt256.ofNat_toNat] <;> simp [words_ok, stack_ok] <;> try omega
  apply Nat.add_lt_add
  . aesop (add safe (by linarith))
  . simp [max_eq_right (Nat.le_of_lt value_big)] -/

theorem UInt256.sub_to_fin (n m : UInt256) : n - m = { val := (n.val - m.val)} := rfl

theorem UInt256.toNat_sub_dist (n m : UInt256) (le_ok : m ≤ n): (n - m).toNat = n.toNat - m.toNat := by
  rw [UInt256.sub_to_fin]
  simp [UInt256.toNat]
  rw [←Fin.sub_val_of_le]
  aesop

theorem UInt256.ofNat_le (n m : UInt256) : (n ≤ m) = (n.toNat ≤ m.toNat) := by
  sorry

theorem X_sstore_summary (symState : EVM.State)
                         (symStack_ok : symStack.length < 1024)/-
                         (gasStippend : GasConstants.Gcallstipend < symGasAvailable.toNat) -/:
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := .ofNat 0
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := ⟨#[(0x52 : UInt8)]⟩,
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
  -- Assume we have enough gas
  GasConstants.Gverylow < symGasAvailable.toNat - (memoryExpansionCost ss Operation.MSTORE) →
  memoryExpansionCost ss Operation.MSTORE < UInt256.size →
  X symGasAvailable.toNat symValidJumps ss =
  .ok (.success {ss with
          stack := symStack,
          pc := .ofNat 1,
          gasAvailable := symGasAvailable - .ofNat (memoryExpansionCost ss mstoreEVM) - .ofNat GasConstants.Gverylow
          memory := mstore_memory_write offset value symMemory,
          activeWords := mstore_activeWords offset symActiveWords
          returnData := .empty,
          execLength := symExecLength + 2} .empty) := by
  intro ss enoughGas mec_small
  have gavail_pos : 1 < symGasAvailable.toNat := by
    rw [GasConstants.Gverylow] at enoughGas; omega
  cases g_case : symGasAvailable.toNat; omega
  /- rw [g_case] at gavail_pos;  -/
  case succ g_pos =>
  simp [X, C', δ]
  have lt_fls_rw {n m : ℕ} (_ : n < m) : (m < n) = False := by
    simp; apply Nat.ge_of_not_lt; simp; omega
  simp [(lt_fls_rw enoughGas), α/- , (lt_fls_rw symStack_ok) -/]
  have fls1 : (symGasAvailable.toNat < memoryExpansionCost ss (@Operation.MSTORE .EVM)) = False :=  by
    rw [Nat.lt_sub_iff_add_lt] at enoughGas
    aesop (add safe (by linarith))

  have decode_rw : ((decode ss.executionEnv.code ss.pc).getD ⟨@Operation.STOP .EVM, none⟩).1 = Operation.MSTORE := by rfl
  have gavail_rw1 : ss.gasAvailable.toNat = symGasAvailable.toNat := by rfl
  have gavail_rw2 : ss.gasAvailable = symGasAvailable := by rfl
  simp [decode_rw, gavail_rw1, gavail_rw2, fls1]
  simp [InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount, InstructionGasGroups.Wzero, InstructionGasGroups.Wbase, InstructionGasGroups.Wverylow]
  have fls2 : ((symGasAvailable - UInt256.ofNat (memoryExpansionCost ss Operation.MSTORE)).toNat < GasConstants.Gverylow) = False := by
    apply eq_false_intro; rw [Nat.not_lt]
    rw [UInt256.toNat_sub_dist, UInt256.ofNat_toNat]
    . aesop
    . aesop
    . sorry
    --aesop (add simp [GasConstants.Gverylow]) (add safe (by omega)) (add safe (by linarith))
  have ss_lt2_f  (n : ℕ) : (n + 1 + 1 < 2) = False := by simp
  simp [fls2, ss, ss_lt2_f, Nat.not_lt_of_lt symStack_ok]
  split; contradiction
  next state n state_ok =>
  cases state_ok
  simp [Except.instMonad, Except.bind]
  have g_pos_pos : 0 < g_pos := by omega
  have step_rw (g : UInt256) := (EVM.step_mstore_summary g_pos GasConstants.Gverylow symStack (.ofNat 0) (symGasAvailable - g) symRefund offset value symActiveWords symExecLength symReturnData ⟨#[(0x52 : UInt8)]⟩ symMemory symAccessedStorageKeys symAccounts symCodeOwner symPerm g_pos_pos symState)
  simp [EVM.step_mstore, mstore_instr, mstoreEVM, ss] at step_rw
  simp [step_rw]
  rw [X_bad_pc] <;> aesop (add simp [GasConstants.Gverylow]) (add safe (by omega))

end

end MstoreSummary
