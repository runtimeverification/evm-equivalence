import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Summaries.StopSummary

open EvmYul
open EVM

namespace DupSummary

inductive dup_op where
  | dup1
  | dup2
  | dup3
  | dup4
  | dup5
  | dup6
  | dup7
  | dup8
  | dup9
  | dup10
  | dup11
  | dup12
  | dup13
  | dup14
  | dup15
  | dup16

section

variable (op : dup_op)
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

-- Specific to `DUPn`
variable (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16: UInt256)

/- @[simp]
abbrev dupEVM := @Operation.DUP1 -/


--@[simp]
def dup_op.to_op : Operation OperationType.EVM :=
  match op with
  | .dup1  => .DUP1
  | .dup2  => .DUP2
  | .dup3  => .DUP3
  | .dup4  => .DUP4
  | .dup5  => .DUP5
  | .dup6  => .DUP6
  | .dup7  => .DUP7
  | .dup8  => .DUP8
  | .dup9  => .DUP9
  | .dup10 => .DUP10
  | .dup11 => .DUP11
  | .dup12 => .DUP12
  | .dup13 => .DUP13
  | .dup14 => .DUP14
  | .dup15 => .DUP15
  | .dup16 => .DUP16

@[simp]
abbrev dup_instr : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  some ⟨op.to_op, none⟩

@[simp]
def EVM.step_dup : Transformer :=
  EVM.step gas gasCost (dup_instr op)

@[simp]
def EvmYul.step_dup : Transformer :=
  @EvmYul.step OperationType.EVM op.to_op

theorem EvmYul.step_dup_summary (symState : EVM.State):
  EvmYul.step_dup op {symState with
    stack := symStack,
    pc := symPc} = default := by cases op <;> rfl

--@[simp]
def dup_op.to_stack : Stack UInt256 :=
  match op with
  | .dup1  => w1::symStack
  | .dup2  => w1::w2::symStack
  | .dup3  => w1::w2::w3::symStack
  | .dup4  => w1::w2::w3::w4::symStack
  | .dup5  => w1::w2::w3::w4::w5::symStack
  | .dup6  => w1::w2::w3::w4::w5::w6::symStack
  | .dup7  => w1::w2::w3::w4::w5::w6::w7::symStack
  | .dup8  => w1::w2::w3::w4::w5::w6::w7::w8::symStack
  | .dup9  => w1::w2::w3::w4::w5::w6::w7::w8::w9::symStack
  | .dup10 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::symStack
  | .dup11 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::symStack
  | .dup12 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::symStack
  | .dup13 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::symStack
  | .dup14 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::symStack
  | .dup15 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::symStack
  | .dup16 => w1::w2::w3::w4::w5::w6::w7::w8::w9::w10::w11::w12::w13::w14::w15::w16::symStack

@[simp]
def dup_op.to_stack_elem : UInt256 :=
  match op with
  | .dup1  => w1
  | .dup2  => w2
  | .dup3  => w3
  | .dup4  => w4
  | .dup5  => w5
  | .dup6  => w6
  | .dup7  => w7
  | .dup8  => w8
  | .dup9  => w9
  | .dup10 => w10
  | .dup11 => w11
  | .dup12 => w12
  | .dup13 => w13
  | .dup14 => w14
  | .dup15 => w15
  | .dup16 => w16

--@[simp]
def dup_op.to_bin : ByteArray :=
  match op with
  | .dup1  => ⟨#[0x80]⟩
  | .dup2  => ⟨#[0x81]⟩
  | .dup3  => ⟨#[0x82]⟩
  | .dup4  => ⟨#[0x83]⟩
  | .dup5  => ⟨#[0x84]⟩
  | .dup6  => ⟨#[0x85]⟩
  | .dup7  => ⟨#[0x86]⟩
  | .dup8  => ⟨#[0x87]⟩
  | .dup9  => ⟨#[0x88]⟩
  | .dup10 => ⟨#[0x89]⟩
  | .dup11 => ⟨#[0x8A]⟩
  | .dup12 => ⟨#[0x8B]⟩
  | .dup13 => ⟨#[0x8C]⟩
  | .dup14 => ⟨#[0x8D]⟩
  | .dup15 => ⟨#[0x8E]⟩
  | .dup16 => ⟨#[0x8F]⟩

@[simp]
def dup_op.to_max_stack_length : ℕ :=
  match op with
  | .dup1  => 1023
  | .dup2  => 1022
  | .dup3  => 1021
  | .dup4  => 1020
  | .dup5  => 1019
  | .dup6  => 1018
  | .dup7  => 1017
  | .dup8  => 1016
  | .dup9  => 1015
  | .dup10 => 1014
  | .dup11 => 1013
  | .dup12 => 1012
  | .dup13 => 1011
  | .dup14 => 1009
  | .dup15 => 1008
  | .dup16 => 1007

theorem EVM.step_dup_summary_simple (gpos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack :=
      @op.to_stack symStack w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16}
  @EVM.step_dup op gas gasCost ss =
    .ok {ss with
    stack :=
      @op.to_stack_elem w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      :: ss.stack
    gasAvailable := ss.gasAvailable - UInt256.ofNat gasCost
    pc := ss.pc + .ofNat 1,
    execLength := ss.execLength + 1} := by
  cases op
  all_goals cases gas; contradiction; rfl


theorem EVM.step_dup_summary (gpos : 0 < gas) (symState : EVM.State):
  let ss :=
  {symState with
      stack :=
      @op.to_stack symStack w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16,
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
  @EVM.step_dup op gas gasCost ss =
    .ok {ss with
    stack :=
      @op.to_stack_elem w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
      :: ss.stack
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc + .ofNat 1,
    execLength := symExecLength + 1} := by
  cases op
  all_goals cases gas; contradiction; rfl

@[simp]
theorem decode_singleton_dup :
  decode op.to_bin (.ofNat 0) = some ⟨op.to_op, none⟩ := by cases op <;> rfl

@[simp]
theorem memoryExpansionCost_dup (symState : EVM.State) :
  memoryExpansionCost symState op.to_op = 0 := by
  cases op <;> simp [dup_op.to_op, memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp]
theorem C'_dup (symState : EVM.State) :
  C' symState op.to_op = GasConstants.Gverylow := by cases op <;> rfl

theorem X_dup_summary (enoughGas : GasConstants.Gverylow < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < op.to_max_stack_length)
                      (symState : EVM.State):
  let ss :=
  {symState with
    stack :=
      @op.to_stack symStack w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16,
    pc := .ofNat 0,
    gasAvailable := symGasAvailable,
    executionEnv := {symState.executionEnv with
                  code := op.to_bin,
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
        stack :=
        @op.to_stack_elem w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        :: ss.stack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat GasConstants.Gverylow,
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  intro ss
  cases g_case: symGasAvailable.toNat; rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gverylow) = False :=
    by aesop (add safe (by omega))
  have stack_ok_rw :
    (List.length ss.stack < (δ op.to_op).getD 0) = False := by
    cases op <;> simp [ss, δ, dup_op.to_stack, dup_op.to_op]
  have gPos : (0 < g_pos) := by aesop (add simp [GasConstants.Gverylow]) (add safe (by omega))
  have delta_none : (δ op.to_op = none) = False := by cases op <;> simp [δ, dup_op.to_op]
  have decode_ss : decode ss.executionEnv.code ss.pc = some ⟨op.to_op, none⟩ := by
    cases op <;> simp [ss]
  have : ss.gasAvailable.toNat = symGasAvailable.toNat := by simp [ss]
  simp [X, decode_ss, this, enough_gas_rw, delta_none, stack_ok_rw]
  have step_rw := (@EVM.step_dup_summary op g_pos GasConstants.Gverylow symGasPrice symTimestamp symNumber symGaslimit symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symPrevrandao symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm)
  have stack_ok_2 : (1024 < List.length ss.stack - (δ op.to_op).getD 0 + (α op.to_op).getD 0) = False := by
    cases op <;>
    simp_all [ss, δ, α, dup_op.to_stack, dup_op.to_op] <;> linarith
  cases op
  all_goals (
    simp only [dup_op.to_op] at stack_ok_2
    simp [dup_op.to_op, delta_none, stack_ok_2]
    split; contradiction
    rename_i evm _ stateOk; revert stateOk
    simp [pure, Except.pure]; intro evm_eq cost; subst cost evm_eq
    dsimp [Except.instMonad, Except.bind]
    dsimp [EVM.step_dup, dup_instr, dup_op.to_op] at step_rw
    simp [ss]; rw [step_rw] <;> try omega
    clear step_rw; simp
    rw [X_bad_pc] <;>
    aesop (add simp [GasConstants.Gverylow, dup_op.to_stack])
    (add safe (by omega))
  )

end

end DupSummary
