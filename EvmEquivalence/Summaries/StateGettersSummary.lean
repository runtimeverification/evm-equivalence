import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open StopSummary

namespace StackOpsSummary

inductive stackGetter_op where
| address
deriving BEq, DecidableEq

section

variable (op : stackGetter_op)
variable (word₁ word₂ word₃: UInt256)
variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund symActiveWords : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

abbrev addressEVM := @Operation.ADDRESS .EVM

abbrev address_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addressEVM, none⟩


@[simp]
def stackGetter_op.get : (Option (Operation .EVM × Option (UInt256 × Nat))) :=
  match op with
  | .address  => address_instr

--@[simp]
def stackGetter_op.t : Operation .EVM :=
  match op with
  | .address  => (address_instr.get rfl).1

def EVM.step_arith : Transformer := EVM.step gas gasCost op.get

def EvmYul.step_arith : Transformer := @EvmYul.step .EVM op.t

@[simp]
def stackGetter_op.do (symState : EVM.State) :=
  match op with
  | .address  => UInt256.ofNat ↑symState.executionEnv.codeOwner

/- theorem EvmYul.step_op_summary (symState : EVM.State):
  EvmYul.step_arith op {symState with
    stack := symStack
    pc := symPc} =
  .ok {symState with
        stack := /- (op.do word₁ word₂ word₃) ::  -/symStack
        pc := symPc + .ofNat 1} := by cases op <;> try rfl -/

theorem EVM.step_add_to_step_add (gpos : 0 < gas) (symState : EVM.State):
  let ss :=
      {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  perm := symPerm},
      accountMap := symAccounts,
      activeWords := symActiveWords,
      memory := symMemory,
      substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
      returnData := symReturnData
      execLength := symExecLength}
  EVM.step_arith op gas gasCost ss =
  EvmYul.step_arith op
    {ss with
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    execLength := symExecLength + 1} := by
      cases gas; contradiction
      simp [EVM.step_arith, EVM.step]; cases op <;> rfl

open private dispatchExecutionEnvOp from EvmYul.Semantics

--attribute [local simp] dispatchExecutionEnvOp executionEnvOp

theorem EVM.step_add_summary (gpos : 0 < gas) (symState : EVM.State):
  let ss :=
      {symState with
      stack := symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  perm := symPerm},
      accountMap := symAccounts,
      activeWords := symActiveWords,
      memory := symMemory,
      substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
      returnData := symReturnData
      execLength := symExecLength}
  EVM.step_arith op gas gasCost ss =
  .ok {ss with
      stack := op.do ss :: symStack
      pc := UInt256.add symPc (.ofNat 1),
      gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
      execLength := symExecLength + 1} := by
  intro ss
  rw [EVM.step_add_to_step_add]
  . cases op <;> rfl
  . assumption

@[simp]
def stackGetter_op.to_bin : ByteArray :=
  match op with
  | .address  => ⟨#[0x30]⟩

@[simp]
theorem decode_singleton_add :
  decode ⟨#[0x30]⟩ (.ofNat 0) = some ⟨addressEVM, none⟩ := rfl

@[simp]
theorem decode_singleton_arith :
  decode op.to_bin (.ofNat 0) = some ⟨op.t, none⟩ := by cases op <;> rfl

@[simp]
theorem memoryExpansionCost_arith (symState : EVM.State) :
  memoryExpansionCost symState op.t = 0 := by
  cases op <;> simp [stackGetter_op.t, memoryExpansionCost, memoryExpansionCost.μᵢ']

def stackGetter_op.C'_comp :=
  match op with
  | .address => GasConstants.Gbase

@[simp]
theorem C'_arith (symState : EVM.State) :
  C' symState op.t = op.C'_comp := by rfl

attribute [local simp] GasConstants.Gbase

--GasConstants.Gverylow GasConstants.Glow GasConstants.Gmid GasConstants.Gexp GasConstants.Gexpbyte

theorem X_arith_summary
                      (enoughGas : op.C'_comp < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < 1024)
                      (symState : EVM.State):
  let ss :=
  {symState with
    stack := symStack,
    pc := .ofNat 0,
    execLength := symExecLength,
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := op.to_bin,
                  codeOwner := symCodeOwner,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
    returnData := symReturnData}
  -- `enoughGas` hypothesis
  --op.C'_comp ss < symGasAvailable.toNat →
  X symGasAvailable.toNat symValidJumps ss =
  Except.ok (.success {ss with
        stack := op.do ss :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat op.C'_comp,
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  intro ss
  cases g_case : symGasAvailable.toNat; rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  simp [X, δ]
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gbase) = False :=
    by aesop (add simp [stackGetter_op.C'_comp])
    (add safe (by omega))
  simp [α/- , stack_ok_rw -/, enough_gas_rw]
  have : ((decode ss.executionEnv.code ss.pc).getD (Operation.STOP, none)).1 = op.t := by
    cases op <;> simp [ss, stackGetter_op.t]
  simp [this]
  have : (ss.gasAvailable.toNat < op.C'_comp) = False := by
    aesop (add simp [stackGetter_op.C'_comp]) (add safe (by linarith))
  simp [this]
  have gPos : (0 < g_pos) := by
    revert enoughGas; simp [stackGetter_op.C'_comp]
    cases op <;> aesop (add safe (by omega))
  have step_rw (cost : ℕ) := (EVM.step_add_summary op g_pos cost symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symPerm gPos)
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    cases op <;> aesop (add safe (by omega))
  cases cop: op <;>
  split <;> rename_i evm cost exec <;> try contradiction
  all_goals (
    simp [EVM.step_arith, cop, address_instr] at step_rw
    --simp only [cop] at stack_ok_rw
    simp [stackGetter_op.t, ss, cop, stack_ok_rw] at exec
    cases exec
  )
  all_goals (
    simp [Except.instMonad, Except.bind, ss, cop, step_rw, stackGetter_op.t]
    rw [X_bad_pc] <;> aesop (add simp [stackGetter_op.C'_comp]) (add safe (by omega))
  )

end

end StackOpsSummary
