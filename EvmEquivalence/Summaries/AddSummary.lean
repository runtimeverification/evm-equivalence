import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open StopSummary

namespace AddSummary

inductive arith_op where
| add
| sub
| div
| sdiv
| mod
| smod
| addmod
| mulmod
| signextend
deriving BEq, DecidableEq

section

variable (op : arith_op)
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

abbrev addEVM := @Operation.ADD .EVM
abbrev subEVM := @Operation.SUB .EVM
abbrev divEVM := @Operation.DIV .EVM
abbrev sdivEVM := @Operation.SDIV .EVM
abbrev modEVM := @Operation.MOD .EVM
abbrev smodEVM := @Operation.SMOD .EVM
abbrev addmodEVM := @Operation.ADDMOD .EVM
abbrev mulmodEVM := @Operation.MULMOD .EVM
abbrev signextendEVM := @Operation.SIGNEXTEND .EVM

abbrev add_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addEVM, none⟩
abbrev sub_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨subEVM, none⟩
abbrev div_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨divEVM, none⟩
abbrev sdiv_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨sdivEVM, none⟩
abbrev mod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨modEVM, none⟩
abbrev smod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨smodEVM, none⟩
abbrev addmod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addmodEVM, none⟩
abbrev mulmod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨mulmodEVM, none⟩
abbrev signextend_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨signextendEVM, none⟩

@[simp]
def arith_op.get : (Option (Operation .EVM × Option (UInt256 × Nat))) :=
  match op with
  | .add  => add_instr
  | .sub  => sub_instr
  | .div  => div_instr
  | .sdiv => sdiv_instr
  | .mod  => mod_instr
  | .smod => smod_instr
  | .addmod => addmod_instr
  | .mulmod => mulmod_instr
  | .signextend => signextend_instr

--@[simp]
def arith_op.t : Operation .EVM :=
  match op with
  | .add  => (add_instr.get rfl).1
  | .sub  => (sub_instr.get rfl).1
  | .div  => (div_instr.get rfl).1
  | .sdiv => (sdiv_instr.get rfl).1
  | .mod => (mod_instr.get rfl).1
  | .smod => (smod_instr.get rfl).1
  | .addmod => (addmod_instr.get rfl).1
  | .mulmod => (mulmod_instr.get rfl).1
  | .signextend => (signextend_instr.get rfl).1

def EVM.step_arith : Transformer := EVM.step gas gasCost op.get

def EvmYul.step_arith : Transformer := @EvmYul.step .EVM op.t

@[simp]
def arith_op.do :=
  match op with
  | .add  => word₁ + word₂
  | .sub  => word₁ - word₂
  | .div  => word₁ / word₂
  | .sdiv => word₁.sdiv word₂
  | .mod  => word₁.mod word₂
  | .smod  => word₁.smod word₂
  | .addmod => word₁.addMod word₂ word₃
  | .mulmod => word₁.mulMod word₂ word₃
  | .signextend => word₁.signextend word₂

@[simp]
def arith_op.stack :=
  match op with
  | .addmod | .mulmod => word₁ :: word₂ :: word₃ :: symStack
  | _ => word₁ :: word₂ :: symStack

theorem EvmYul.step_sub_summary (symState : EVM.State):
  EvmYul.step_arith op {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
    pc := symPc} =
  .ok {symState with
        stack := (op.do word₁ word₂ word₃) :: symStack
        pc := symPc + .ofNat 1} := by cases op <;> rfl

theorem EVM.step_add_to_step_add (gpos : 0 < gas) (symState : EVM.State):
  EVM.step_arith op gas gasCost
    {symState with
      stack := op.stack word₁ word₂ word₃ symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      execLength := symExecLength,
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
      returnData := symReturnData} =
  EvmYul.step_arith op
    {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    returnData := symReturnData,
    substate := {symState.substate with
            accessedStorageKeys :=  symAccessedStorageKeys
            refundBalance := symRefund
           }
    execLength := symExecLength + 1} := by
      cases gas; contradiction
      simp [EVM.step_arith, EVM.step]; cases op <;> rfl

theorem EVM.step_add_summary (gpos : 0 < gas) (symState : EVM.State):
  EVM.step_arith op gas gasCost
    {symState with
      stack := op.stack word₁ word₂ word₃ symStack,
      pc := symPc,
      gasAvailable := symGasAvailable,
      returnData := symReturnData,
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
      execLength := symExecLength} =
    .ok {symState with
          stack := op.do word₁ word₂ word₃ :: symStack,
          pc := UInt256.add symPc (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost,
          returnData := symReturnData,
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
          execLength := symExecLength + 1} := by
  rw [EVM.step_add_to_step_add]; cases op <;> rfl; assumption

----
-- For having symbolic programs instead of singleton ones
/- abbrev addBytecode (preCode postCode : Array UInt8) : ByteArray :=
  ⟨preCode ++ #[(0x01 : UInt8)] ++ postCode⟩

abbrev addInstr (preCode postCode : Array UInt8) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
decode (addBytecode preCode postCode) (.ofNat preCode.size)

theorem array_append_size_comm {α : Type} (a1 a2 : Array α) :
  (a1 ++ a2).size <= (a2 ++ a1).size := by sorry

theorem array_append_size_le {α : Type} (a1 a2 : Array α) :
  a1.size <= (a1 ++ a2).size := by sorry -/

--set_option maxHeartbeats 3000000
/- theorem addInst_eq (preCode postCode : Array UInt8)
                   (preCode_size_ok : preCode.size < UInt256.size) : addInstr preCode postCode = add_instr := by
  simp [add_instr, addEVM, addInstr, addBytecode, decode] -/
  /- split
  case isTrue => sorry
    --simp [parseInstr]
    --rw [ofNat_toNat_eq]
  case isFalse fls =>
    have h_true : (UInt256.ofNat preCode.size).toNat < preCode.size + (1 + postCode.size) := sorry
    contradiction -/
----

@[simp]
def arith_op.to_bin : ByteArray :=
  match op with
  | .add  => ⟨#[0x1]⟩
  | .sub  => ⟨#[0x3]⟩
  | .div  => ⟨#[0x4]⟩
  | .sdiv => ⟨#[0x5]⟩
  | .mod  => ⟨#[0x6]⟩
  | .smod => ⟨#[0x7]⟩
  | .addmod => ⟨#[0x8]⟩
  | .mulmod => ⟨#[0x9]⟩
  | .signextend => ⟨#[0xB]⟩

@[simp]
theorem decode_singleton_add :
  decode ⟨#[0x1]⟩ (.ofNat 0) = some ⟨addEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_sub :
  decode ⟨#[0x3]⟩ (.ofNat 0) = some ⟨subEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_div :
  decode ⟨#[0x4]⟩ (.ofNat 0) = some ⟨divEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_sdiv :
  decode ⟨#[0x5]⟩ (.ofNat 0) = some ⟨sdivEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_mod :
  decode ⟨#[0x6]⟩ (.ofNat 0) = some ⟨modEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_smod :
  decode ⟨#[0x7]⟩ (.ofNat 0) = some ⟨smodEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_addmod :
  decode ⟨#[0x8]⟩ (.ofNat 0) = some ⟨addmodEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_mulmod :
  decode ⟨#[0x9]⟩ (.ofNat 0) = some ⟨mulmodEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_signextend :
  decode ⟨#[0xB]⟩ (.ofNat 0) = some ⟨signextendEVM, none⟩ := rfl

@[simp]
theorem decode_singleton_arith :
  decode op.to_bin (.ofNat 0) = some ⟨op.t, none⟩ := by cases op <;> rfl

@[simp]
theorem memoryExpansionCost_arith (symState : EVM.State) :
  memoryExpansionCost symState op.t = 0 := by
  cases op <;> simp [arith_op.t, memoryExpansionCost, memoryExpansionCost.μᵢ']

def arith_op.C'_comp :=
  match op with
  | .add | .sub => GasConstants.Gverylow
  | .addmod | .mulmod => GasConstants.Gmid
  | _ => GasConstants.Glow

@[simp]
theorem C'_arith (symState : EVM.State) :
  C' symState op.t =  op.C'_comp := by cases op <;> rfl

@[simp]
def arith_op.to_stack_length :=
  match op with
  | .addmod | .mulmod => 1023
  | _ => 1024

attribute [local simp] GasConstants.Gverylow GasConstants.Glow GasConstants.Gmid

theorem X_arith_summary
                      (enoughGas : op.C'_comp < symGasAvailable.toNat)
                      (symStack_ok : symStack.length < op.to_stack_length)
                      (symState : EVM.State):
  let ss :=
  {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
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
  /- C'_comp op < symGasAvailable.toNat → -/
  X symGasAvailable.toNat symValidJumps ss =
  Except.ok (.success {ss with
        stack := op.do word₁ word₂ word₃ :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat op.C'_comp,
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  intro ss
  cases g_case : symGasAvailable.toNat; rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  have ss_lt2_f  (n : ℕ) : (n + 1 + 1 < 2) = False := by simp
  simp [X, δ, ss_lt2_f]
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    aesop (add safe (by omega))
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gverylow) = False :=
    by aesop (add simp [arith_op.C'_comp])
    (add safe (by omega))
  simp [α, stack_ok_rw, enough_gas_rw]
  have : ((decode ss.executionEnv.code ss.pc).getD (Operation.STOP, none)).1 = op.t := by
    cases op <;> simp [ss, arith_op.t]
  simp [this]
  have : (ss.gasAvailable.toNat < op.C'_comp) = False := by
    aesop (add simp [arith_op.C'_comp, ss]) (add safe (by linarith))
  simp [this]
  have gPos : (0 < g_pos) := by
    revert enoughGas; simp [arith_op.C'_comp]
    cases op <;> simp <;> omega
  have step_rw (cost : ℕ) := (EVM.step_add_summary op word₁ word₂ word₃ g_pos cost symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symPerm gPos)
  cases cop: op <;> simp [cop] at symStack_ok <;>
  split <;> rename_i evm cost exec <;> try contradiction
  all_goals (
    simp [EVM.step_arith, cop, add_instr, sub_instr, div_instr] at step_rw
    simp [arith_op.t, ss, cop, ss_lt2_f, stack_ok_rw] at exec
    cases exec
  )
  all_goals (
    simp [Except.instMonad, Except.bind, ss, cop, step_rw, arith_op.t]
    rw [X_bad_pc] <;> aesop (add safe (by omega))
  )

end

end AddSummary
