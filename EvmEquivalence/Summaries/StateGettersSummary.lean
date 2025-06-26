import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open StopSummary

namespace StateGettersSummary

inductive stateGetter_op where
| address
| origin
| caller
| gasprice
| coinbase
| timestamp
| prevrandao
deriving BEq, DecidableEq

section

variable (op : stateGetter_op)
variable (word₁ word₂ word₃: UInt256)
variable (gas gasCost symGasPrice symTimestamp : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund symActiveWords : UInt256)
variable (symPrevrandao : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode symMemory : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner symSender symSource symCoinbase : AccountAddress)
variable (symPerm : Bool)

variable (symValidJumps : Array UInt256)

abbrev addressEVM := @Operation.ADDRESS .EVM
abbrev originEVM := @Operation.ORIGIN .EVM
abbrev callerEVM := @Operation.CALLER .EVM
abbrev gaspriceEVM := @Operation.GASPRICE .EVM
abbrev coinbaseEVM := @Operation.COINBASE .EVM
abbrev timestampEVM := @Operation.TIMESTAMP .EVM
abbrev prevrandaoEVM := @Operation.PREVRANDAO .EVM

abbrev address_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addressEVM, none⟩
abbrev origin_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨originEVM, none⟩
abbrev caller_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨callerEVM, none⟩
abbrev gasprice_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨gaspriceEVM, none⟩
abbrev coinbase_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨coinbaseEVM, none⟩
abbrev timestamp_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨timestampEVM, none⟩
abbrev prevrandao_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨prevrandaoEVM, none⟩

@[simp]
def stateGetter_op.get : (Option (Operation .EVM × Option (UInt256 × Nat))) :=
  match op with
  | .address  => address_instr
  | .origin => origin_instr
  | .caller => caller_instr
  | .gasprice => gasprice_instr
  | .coinbase => coinbase_instr
  | .timestamp => timestamp_instr
  | .prevrandao => prevrandao_instr

--@[simp]
def stateGetter_op.t : Operation .EVM :=
  match op with
  | .address  => (address_instr.get rfl).1
  | .origin  => (origin_instr.get rfl).1
  | .caller  => (caller_instr.get rfl).1
  | .gasprice  => (gasprice_instr.get rfl).1
  | .coinbase  => (coinbase_instr.get rfl).1
  | .timestamp  => (timestamp_instr.get rfl).1
  | .prevrandao  => (prevrandao_instr.get rfl).1

def EVM.step_arith : Transformer := EVM.step gas gasCost op.get

def EvmYul.step_arith : Transformer := @EvmYul.step .EVM op.t

@[simp]
def stateGetter_op.do (symState : EVM.State) :=
  match op with
  | .address  => UInt256.ofNat ↑symState.executionEnv.codeOwner
  | .origin  => UInt256.ofNat ↑symState.executionEnv.sender
  | .caller  => UInt256.ofNat ↑symState.executionEnv.source
  | .gasprice  => UInt256.ofNat symState.executionEnv.gasPrice
  | .coinbase  => UInt256.ofNat ↑symState.coinBase
  | .timestamp  => symState.timeStamp
  | .prevrandao  => symState.executionEnv.header.prevRandao

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

theorem EVM.step_getter_summary (gpos : 0 < gas) (symState : EVM.State):
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
                    prevRandao := symPrevrandao
                  }
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
  intro ss; rw [EVM.step_add_to_step_add]
  . cases op <;> rfl
  . assumption

@[simp]
def stateGetter_op.to_bin : ByteArray :=
  match op with
  | .address  => ⟨#[0x30]⟩
  | .origin  => ⟨#[0x32]⟩
  | .caller  => ⟨#[0x33]⟩
  | .gasprice => ⟨#[0x3A]⟩
  | .coinbase => ⟨#[0x41]⟩
  | .timestamp => ⟨#[0x42]⟩
  | .prevrandao => ⟨#[0x44]⟩

@[simp]
theorem decode_singleton_address :
  decode ⟨#[0x30]⟩ (.ofNat 0) = some ⟨addressEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_origin :
  decode ⟨#[0x32]⟩ (.ofNat 0) = some ⟨originEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_caller :
  decode ⟨#[0x33]⟩ (.ofNat 0) = some ⟨callerEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_gasprice :
  decode ⟨#[0x3A]⟩ (.ofNat 0) = some ⟨gaspriceEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_coinbase :
  decode ⟨#[0x41]⟩ (.ofNat 0) = some ⟨coinbaseEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_timestamp :
  decode ⟨#[0x42]⟩ (.ofNat 0) = some ⟨timestampEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_prevrandao :
  decode ⟨#[0x44]⟩ (.ofNat 0) = some ⟨prevrandaoEVM, none⟩ := rfl

@[simp]
theorem decode_singleton :
  decode op.to_bin (.ofNat 0) = some ⟨op.t, none⟩ := by cases op <;> rfl

@[simp]
theorem memoryExpansionCost_arith (symState : EVM.State) :
  memoryExpansionCost symState op.t = 0 := by
  cases op <;> simp [stateGetter_op.t, memoryExpansionCost, memoryExpansionCost.μᵢ']

def stateGetter_op.C'_comp :=
  match op with
  | _ => GasConstants.Gbase

@[simp]
theorem C'_arith (symState : EVM.State) :
  C' symState op.t = op.C'_comp := by cases op <;> reduce <;> rfl

attribute [local simp] GasConstants.Gbase

--GasConstants.Gverylow GasConstants.Glow GasConstants.Gmid GasConstants.Gexp GasConstants.Gexpbyte

theorem X_getter_summary
                      (enoughGas : op.C'_comp < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < 1024)
                      (code_h : symCode = op.to_bin)
                      (symState : EVM.State):
  let ss :=
  {symState with
    stack := symStack,
    pc := .ofNat 0,
    execLength := symExecLength,
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
    by aesop (add simp [stateGetter_op.C'_comp])
    (add safe (by omega))
  simp [α/- , stack_ok_rw -/, enough_gas_rw]
  have : ((decode ss.executionEnv.code ss.pc).getD (Operation.STOP, none)).1 = op.t := by
    cases op <;> simp [ss, code_h, stateGetter_op.t]
  simp [this]
  have : (ss.gasAvailable.toNat < op.C'_comp) = False := by
    aesop (add simp [stateGetter_op.C'_comp]) (add safe (by linarith))
  simp [this]
  have gPos : (0 < g_pos) := by
    revert enoughGas; simp [stateGetter_op.C'_comp]
    cases op <;> aesop (add safe (by omega))
  have step_rw (cost : ℕ) := (EVM.step_getter_summary op g_pos cost symGasPrice symTimestamp symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symPrevrandao symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symCoinbase symPerm gPos)
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    cases op <;> aesop (add safe (by omega))
  cases cop: op <;>
  split <;> rename_i evm cost exec <;> try contradiction
  all_goals (
    simp [EVM.step_arith, cop, address_instr] at step_rw
    --simp only [cop] at stack_ok_rw
    simp [stateGetter_op.t, ss, cop, stack_ok_rw] at exec
    cases exec
  )
  all_goals (
    simp [Except.instMonad, Except.bind, ss, code_h, cop, step_rw, stateGetter_op.t]
    rw [X_bad_pc] <;> aesop (add simp [stateGetter_op.C'_comp]) (add safe (by omega))
  )

end

end StateGettersSummary
