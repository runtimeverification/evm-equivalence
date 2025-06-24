import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open EvmYul.State

namespace MstoreSummary

inductive mstore_op where
 | mstore
 | mstore8

section

/- It's more handy to have the `op` variable at the top -/
variable (op : mstore_op)
variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund offset value : UInt256)
variable (symActiveWords : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner symSender : AccountAddress)
variable (symPerm : Bool)
variable (symValidJumps : Array UInt256)

@[simp]
abbrev mstoreEVM := @Operation.MSTORE .EVM

@[simp]
abbrev mstore8EVM := @Operation.MSTORE8 .EVM

@[simp]
abbrev mstore_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨mstoreEVM, none⟩

@[simp]
abbrev mstore8_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨mstore8EVM, none⟩

@[simp]
def mstore_op.get : (Option (Operation .EVM × Option (UInt256 × Nat))) :=
  match op with
  | .mstore => mstore_instr
  | .mstore8 => mstore8_instr

def mstore_op.t : Operation OperationType.EVM :=
  match op with
  | .mstore => (mstore_instr.get rfl).1
  | .mstore8 => (mstore8_instr.get rfl).1

/--
Getter for the `MachineStateOps.mstore*` function
-/
@[simp]
def mstore_op.to_mso : MachineState → UInt256 → UInt256 → MachineState :=
  match op with
  | .mstore => EvmYul.MachineState.mstore
  | .mstore8 => EvmYul.MachineState.mstore8

@[simp]
abbrev EVM.step_mstore : Transformer :=
  EVM.step gas gasCost op.get

@[simp]
abbrev EvmYul.step_mstore : Transformer :=
  EvmYul.step op.t

/--
Different cases for the `activeWords` update
-/
@[simp]
def mstore_op.to_l : ℕ :=
  match op with
  | .mstore => 32
  | .mstore8 => 1

/--
Theorem needed to bypass the `private` attribute of `EVM.dispatchBinaryMachineStateOp`
 -/
theorem mstore_bypass_private
  (symState : EVM.State):
  let ss := {symState with
  stack := symStack,
  pc := symPc
  gasAvailable := symGasAvailable,
  executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  perm := symPerm},
  accountMap := symAccounts,
  activeWords := symActiveWords,
  memory := symMemory,
  substate := {symState.substate with
               accessedStorageKeys :=  symAccessedStorageKeys
               refundBalance := symRefund}
  returnData := symReturnData,
  execLength := symExecLength}
  EvmYul.step_mstore op ss =
  EVM.binaryMachineStateOp op.to_mso ss := by cases op <;> rfl

/--
The new amount of `activeWords` based after running `MSTORE` with `offset`
and `currentAC` amount of active words
-/
def activeWords_comp (l : ℕ) :=
  UInt256.ofNat (symActiveWords.toNat ⊔ (offset.toNat + l + 31) / 32)

/--
Writing `value` to `symMemory` starting at `offset`
-/
def mstore_memory_write : ByteArray :=
value.toByteArray.write 0 symMemory offset.toNat 32

/--
Writing `value` to `symMemory` starting at `offset`
-/
def mstore8_memory_write : ByteArray :=
(⟨#[UInt8.ofNat value.toNat]⟩ :ByteArray).write 0 symMemory offset.toNat 1

/--
Different cases to write to memory depending on the `mstore*` opcode
-/
@[simp]
def mstore_op.to_write : UInt256 → UInt256 → ByteArray → ByteArray :=
  match op with
  | .mstore => mstore_memory_write
  | .mstore8 => mstore8_memory_write

theorem EvmYul.step_mstore_summary (symState : EVM.State):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EvmYul.step_mstore op ss =
  .ok {ss with
    stack := symStack,
    pc := symPc + .ofNat 1
    memory := op.to_write offset value symMemory,
    activeWords := activeWords_comp offset symActiveWords op.to_l} := by aesop

theorem EVM.step_mstore_summary
  (gas_pos : 0 < gas)
  (symState : EVM.State):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := symPc
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
                 accessedStorageKeys :=  symAccessedStorageKeys
                 refundBalance := symRefund}
    returnData := symReturnData,
    execLength := symExecLength}
  EVM.step_mstore op gas gasCost ss =
    .ok {ss with
          stack := symStack,
          pc := symPc + (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          memory := op.to_write offset value symMemory,
          activeWords := activeWords_comp offset symActiveWords op.to_l
          execLength := symExecLength + 1} := by
  cases gas; contradiction
  simp [step_mstore, EVM.step]
  have srw := EvmYul.step_mstore_summary op symStack symPc (symGasAvailable - UInt256.ofNat gasCost) symRefund offset value symActiveWords (symExecLength + 1) symReturnData symCode symMemory
  simp [EvmYul.step_mstore, Operation.MSTORE] at srw
  cases op <;> aesop

/--
Opcode map to binary
-/
def mstore_op.to_bin : ByteArray :=
  match op with
  | .mstore  => ⟨#[0x52]⟩
  | .mstore8 => ⟨#[0x53]⟩

@[simp]
theorem decode_singleton_mstore :
  decode op.to_bin (.ofNat 0) = some ⟨op.t, none⟩ := by aesop (add simp [mstore_op.t])

@[simp]
def value_and_activeWords_gas :=
  UInt256.ofNat (MachineState.M symActiveWords.toNat value.toNat op.to_l)

@[simp]
theorem memoryExpansionCost_mstore (symState : EVM.State)
  (stack_ok : symState.stack = offset :: value :: symStack)
  (symWords_ok : symState.activeWords = symActiveWords):
  memoryExpansionCost symState op.t =
  Cₘ (value_and_activeWords_gas op offset symActiveWords) -
  Cₘ symActiveWords := by
  cases op <;>
  aesop (add simp [memoryExpansionCost, memoryExpansionCost.μᵢ'])

theorem X_mstore_summary (symState : EVM.State)
                         (symStack_ok : symStack.length <
                         match op with
                         | .mstore => 1024
                         | .mstore8 => 1025):
  let ss := {symState with
    stack := offset :: value :: symStack,
    pc := .ofNat 0
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := op.to_bin,
                  codeOwner := symCodeOwner,
                  sender := symSender,
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
  GasConstants.Gverylow < symGasAvailable.toNat - (memoryExpansionCost ss op.t) →
  memoryExpansionCost ss op.t < UInt256.size →
  X symGasAvailable.toNat symValidJumps ss =
  .ok (.success {ss with
          stack := symStack,
          pc := .ofNat 1,
          gasAvailable := symGasAvailable - .ofNat (memoryExpansionCost ss op.t) - .ofNat GasConstants.Gverylow
          memory := op.to_write offset value symMemory,
          activeWords := activeWords_comp offset symActiveWords op.to_l
          returnData := .empty,
          execLength := symExecLength + 2} .empty) := by
  intro ss enoughGas mec_small
  have gavail_pos : 2 < symGasAvailable.toNat := by
    rw [GasConstants.Gverylow] at enoughGas; omega
  cases g_case : symGasAvailable.toNat; omega
  case succ g_pos =>
  simp [X]
  have lt_fls_rw {n m : ℕ} (_ : n < m) : (m < n) = False := by
    simp; apply Nat.ge_of_not_lt; simp; omega
  simp [(lt_fls_rw enoughGas), α]
  have fls1 : (symGasAvailable.toNat < memoryExpansionCost ss op.t) = False :=  by
    rw [Nat.lt_sub_iff_add_lt] at enoughGas
    aesop (add safe (by linarith))
  have decode_rw : ((decode ss.executionEnv.code ss.pc).getD ⟨@Operation.STOP .EVM, none⟩).1 = op.t := by aesop
  have gavail_rw1 : ss.gasAvailable.toNat = symGasAvailable.toNat := rfl
  have gavail_rw2 : ss.gasAvailable = symGasAvailable := rfl
  simp [decode_rw, gavail_rw1, gavail_rw2, fls1]
  let Cgas := C'
            { toState := ss.toState, gasAvailable := symGasAvailable - UInt256.ofNat (memoryExpansionCost ss op.t),
              activeWords := ss.activeWords, memory := ss.memory, returnData := ss.returnData, H_return := ss.H_return,
              pc := ss.pc, stack := ss.stack, execLength := ss.execLength }
  have Cgas_rw : Cgas op.t = GasConstants.Gverylow := by
    cases op <;> simp [Cgas, C'] <;> aesop
  unfold Cgas at Cgas_rw
  rw [Cgas_rw]
  have fls2 : ((symGasAvailable - UInt256.ofNat (memoryExpansionCost ss op.t)).toNat < GasConstants.Gverylow) = False := by
    apply eq_false_intro; rw [Nat.not_lt]
    rw [UInt256.toNat_sub_dist, UInt256.ofNat_toNat] <;>
    aesop (add simp [UInt256.ofNat_le, UInt256.ofNat_toNat])
  have ss_lt2_f  (n : ℕ) : (n + 1 + 1 < 2) = False := by simp
  simp [fls2, ss]
  have g_pos0 : 0 < g_pos := by omega
  have g_pos1 : 1 < g_pos := by omega
  have step_rw (g : UInt256) := (EVM.step_mstore_summary op g_pos GasConstants.Gverylow symStack (.ofNat 0) (symGasAvailable - g) symRefund offset value symActiveWords symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symPerm g_pos0 symState)
  let op_stack := match op with | .mstore => 1024 | .mstore8 => 1025
  have : (op_stack < List.length symStack) = False := by aesop
  cases cop : op <;> simp [δ] <;>
  (
    simp_all [op_stack, mstore_op.t, ss_lt2_f, this]; split
    next _ _ h =>
      split at h; contradiction
      split at h; linarith
      contradiction
    next state n state_ok =>
    repeat (split at state_ok; linarith)
    cases state_ok; simp [step_rw, Except.instMonad, Except.bind]
    rw [X_bad_pc] <;> first | linarith | congr
  )

end

end MstoreSummary
