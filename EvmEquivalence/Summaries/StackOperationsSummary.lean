import EvmYul.EVM.Semantics
import EvmYul.EVM.GasConstants
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open EVM
open StopSummary

namespace StackOpsSummary

inductive arith_op where
| add
| sub
| div
| sdiv
| mod
| smod
| addmod
| mulmod
| exp
| signextend
| lt
| gt
| slt
| sgt
| eq
| iszero
| and
| or
| xor
| not
| byte
| shl
| shr
| sar
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
variable (symCodeOwner symSender symSource : AccountAddress)
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
abbrev expEVM := @Operation.EXP .EVM
abbrev signextendEVM := @Operation.SIGNEXTEND .EVM
abbrev ltEVM := @Operation.LT .EVM
abbrev gtEVM := @Operation.GT .EVM
abbrev sltEVM := @Operation.SLT .EVM
abbrev sgtEVM := @Operation.SGT .EVM
abbrev eqEVM := @Operation.EQ .EVM
abbrev iszeroEVM := @Operation.ISZERO .EVM
abbrev andEVM := @Operation.AND .EVM
abbrev orEVM := @Operation.OR .EVM
abbrev xorEVM := @Operation.XOR .EVM
abbrev notEVM := @Operation.NOT .EVM
abbrev byteEVM := @Operation.BYTE .EVM
abbrev shlEVM := @Operation.SHL .EVM
abbrev shrEVM := @Operation.SHR .EVM
abbrev sarEVM := @Operation.SAR .EVM

abbrev add_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addEVM, none⟩
abbrev sub_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨subEVM, none⟩
abbrev div_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨divEVM, none⟩
abbrev sdiv_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨sdivEVM, none⟩
abbrev mod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨modEVM, none⟩
abbrev smod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨smodEVM, none⟩
abbrev addmod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨addmodEVM, none⟩
abbrev mulmod_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨mulmodEVM, none⟩
abbrev exp_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨expEVM, none⟩
abbrev signextend_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨signextendEVM, none⟩
abbrev lt_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨ltEVM, none⟩
abbrev gt_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨gtEVM, none⟩
abbrev slt_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨sltEVM, none⟩
abbrev sgt_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨sgtEVM, none⟩
abbrev eq_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨eqEVM, none⟩
abbrev iszero_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨iszeroEVM, none⟩
abbrev and_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨andEVM, none⟩
abbrev or_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨orEVM, none⟩
abbrev xor_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨xorEVM, none⟩
abbrev not_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨notEVM, none⟩
abbrev byte_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨byteEVM, none⟩
abbrev shl_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨shlEVM, none⟩
abbrev shr_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨shrEVM, none⟩
abbrev sar_instr : Option (Operation .EVM × Option (UInt256 × Nat)) := some ⟨sarEVM, none⟩


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
  | .exp => exp_instr
  | .signextend => signextend_instr
  | .lt => lt_instr
  | .gt => gt_instr
  | .slt => slt_instr
  | .sgt => sgt_instr
  | .eq => eq_instr
  | .iszero => iszero_instr
  | .and => and_instr
  | .or => or_instr
  | .xor => xor_instr
  | .not => not_instr
  | .byte => byte_instr
  | .shl => shl_instr
  | .shr => shr_instr
  | .sar => sar_instr

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
  | .exp => (exp_instr.get rfl).1
  | .signextend => (signextend_instr.get rfl).1
  | .lt => (lt_instr.get rfl).1
  | .gt => (gt_instr.get rfl).1
  | .slt => (slt_instr.get rfl).1
  | .sgt => (sgt_instr.get rfl).1
  | .eq => (eq_instr.get rfl).1
  | .iszero => (iszero_instr.get rfl).1
  | .and => (and_instr.get rfl).1
  | .or => (or_instr.get rfl).1
  | .xor => (xor_instr.get rfl).1
  | .not => (not_instr.get rfl).1
  | .byte => (byte_instr.get rfl).1
  | .shl => (shl_instr.get rfl).1
  | .shr => (shr_instr.get rfl).1
  | .sar => (sar_instr.get rfl).1

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
  | .exp => word₁.exp word₂
  | .signextend => word₁.signextend word₂
  | .lt => word₁.lt word₂
  | .gt => word₁.gt word₂
  | .slt => word₁.slt word₂
  | .sgt => word₁.sgt word₂
  | .eq => word₁.eq word₂
  | .iszero => word₁.isZero
  | .and => word₁.land word₂
  | .or => word₁.lor word₂
  | .xor => word₁.xor word₂
  | .not => word₁.lnot
  | .byte => word₁.byteAt word₂
  | .shl => (flip UInt256.shiftLeft) word₁ word₂
  | .shr => (flip UInt256.shiftRight) word₁ word₂
  | .sar => word₁.sar word₂

@[simp]
def arith_op.stack :=
  match op with
  | .iszero | .not => word₁ :: symStack
  | .addmod | .mulmod => word₁ :: word₂ :: word₃ :: symStack
  | _ => word₁ :: word₂ :: symStack

theorem EvmYul.step_op_summary (symState : EVM.State):
  EvmYul.step_arith op {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
    pc := symPc} =
  .ok {symState with
        stack := (op.do word₁ word₂ word₃) :: symStack
        pc := symPc + .ofNat 1} := by cases op <;> rfl



theorem EVM.step_add_to_step_add (gpos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
    pc := symPc,
    gasAvailable := symGasAvailable,
    returnData := symReturnData,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
          accessedStorageKeys :=  symAccessedStorageKeys
          refundBalance := symRefund
         }
    execLength := symExecLength}
  EVM.step_arith op gas gasCost ss =
  EvmYul.step_arith op
    {ss with
    stack := op.stack word₁ word₂ word₃ symStack,
    gasAvailable := symGasAvailable - UInt256.ofNat gasCost
    pc := symPc,
    execLength := symExecLength + 1} := by
      cases gas; contradiction
      simp [EVM.step_arith, EVM.step]; cases op <;> rfl

theorem EVM.step_add_summary (gpos : 0 < gas) (symState : EVM.State):
  let ss := {symState with
    stack := op.stack word₁ word₂ word₃ symStack,
    pc := symPc,
    gasAvailable := symGasAvailable,
    returnData := symReturnData,
    executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner,
                  sender := symSender,
                  source := symSource,
                  perm := symPerm},
    accountMap := symAccounts,
    activeWords := symActiveWords,
    memory := symMemory,
    substate := {symState.substate with
          accessedStorageKeys :=  symAccessedStorageKeys
          refundBalance := symRefund
         }
    execLength := symExecLength}
  EVM.step_arith op gas gasCost ss =
  .ok {ss with
          stack := op.do word₁ word₂ word₃ :: symStack,
          pc := UInt256.add symPc (.ofNat 1),
          gasAvailable := symGasAvailable - UInt256.ofNat gasCost
          execLength := symExecLength + 1
          } := by
  intro ss; rw [EVM.step_add_to_step_add]; cases op <;> rfl; assumption

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
  | .exp => ⟨#[0xA]⟩
  | .signextend => ⟨#[0xB]⟩
  | .lt => ⟨#[0x10]⟩
  | .gt => ⟨#[0x11]⟩
  | .slt => ⟨#[0x12]⟩
  | .sgt => ⟨#[0x13]⟩
  | .eq => ⟨#[0x14]⟩
  | .iszero => ⟨#[0x15]⟩
  | .and => ⟨#[0x16]⟩
  | .or => ⟨#[0x17]⟩
  | .xor => ⟨#[0x18]⟩
  | .not => ⟨#[0x19]⟩
  | .byte => ⟨#[0x1A]⟩
  | .shl => ⟨#[0x1B]⟩
  | .shr => ⟨#[0x1C]⟩
  | .sar => ⟨#[0x1D]⟩

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
theorem decode_singleton_exp :
  decode ⟨#[0xA]⟩ (.ofNat 0) = some ⟨expEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_signextend :
  decode ⟨#[0xB]⟩ (.ofNat 0) = some ⟨signextendEVM, none⟩ := rfl
@[simp]
theorem decode_singleton_lt :
  decode ⟨#[0x10]⟩ (.ofNat 0) = some (ltEVM, none) := rfl
@[simp]
theorem decode_singleton_gt :
  decode ⟨#[0x11]⟩ (.ofNat 0) = some (gtEVM, none) := rfl
@[simp]
theorem decode_singleton_slt :
  decode ⟨#[0x12]⟩ (.ofNat 0) = some (sltEVM, none) := rfl
@[simp]
theorem decode_singleton_sgt :
  decode ⟨#[0x13]⟩ (.ofNat 0) = some (sgtEVM, none) := rfl
@[simp]
theorem decode_singleton_eq :
  decode ⟨#[0x14]⟩ (.ofNat 0) = some (eqEVM, none) := rfl
@[simp]
theorem decode_singleton_iszero :
  decode ⟨#[0x15]⟩ (.ofNat 0) = some (iszeroEVM, none) := rfl
@[simp]
theorem decode_singleton_and :
  decode ⟨#[0x16]⟩ (.ofNat 0) = some (andEVM, none) := rfl
@[simp]
theorem decode_singleton_or :
  decode ⟨#[0x17]⟩ (.ofNat 0) = some (orEVM, none) := rfl
@[simp]
theorem decode_singleton_xor :
  decode ⟨#[0x18]⟩ (.ofNat 0) = some (xorEVM, none) := rfl
@[simp]
theorem decode_singleton_not :
  decode ⟨#[0x19]⟩ (.ofNat 0) = some (notEVM, none) := rfl
@[simp]
theorem decode_singleton_byte :
  decode ⟨#[0x1A]⟩ (.ofNat 0) = some (byteEVM, none) := rfl
@[simp]
theorem decode_singleton_shl :
  decode ⟨#[0x1B]⟩ (.ofNat 0) = some (shlEVM, none) := rfl
@[simp]
theorem decode_singleton_shr :
  decode ⟨#[0x1C]⟩ (.ofNat 0) = some (shrEVM, none) := rfl
@[simp]
theorem decode_singleton_sar :
  decode ⟨#[0x1D]⟩ (.ofNat 0) = some (sarEVM, none) := rfl

@[simp]
theorem decode_singleton_arith :
  decode op.to_bin (.ofNat 0) = some ⟨op.t, none⟩ := by cases op <;> rfl

@[simp]
theorem memoryExpansionCost_arith (symState : EVM.State) :
  memoryExpansionCost symState op.t = 0 := by
  cases op <;> simp [arith_op.t, memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp]
def C'_exp (symState : EVM.State) :=
  if (symState.stack[1]?.getD default == { val := 0 }) = true then GasConstants.Gexp
  else GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 (symState.stack[1]?.getD default).toNat)

def arith_op.C'_noexp :=
  match op with
  | .div | .sdiv | .mod | .smod | .signextend => GasConstants.Glow
  | .addmod | .mulmod => GasConstants.Gmid
  | _ => GasConstants.Gverylow

def arith_op.C'_comp (symState : EVM.State) :=
  match op with
  | .exp => C'_exp symState
  | _ => op.C'_noexp

@[simp]
theorem C'_arith (symState : EVM.State) :
  C' symState op.t = op.C'_comp symState := by
  cases op <;> aesop (add simp [C', arith_op.t, arith_op.C'_comp, C'_exp])

@[simp]
def arith_op.to_stack_length :=
  match op with
  | .iszero | .not => 1024
  | .addmod | .mulmod => 1022
  | _ => 1023

attribute [local simp] GasConstants.Gverylow GasConstants.Glow GasConstants.Gmid GasConstants.Gexp GasConstants.Gexpbyte

theorem X_arith_summary
                      /- (enoughGas : op.C'_comp < symGasAvailable.toNat) -/
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
                  sender := symSender,
                  source := symSource,
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
  op.C'_comp ss < symGasAvailable.toNat →
  X symGasAvailable.toNat symValidJumps ss =
  Except.ok (.success {ss with
        stack := op.do word₁ word₂ word₃ :: symStack,
        pc := .ofNat 1,
        gasAvailable := symGasAvailable - .ofNat (op.C'_comp ss),
        returnData := ByteArray.empty,
        execLength := symExecLength + 2} ByteArray.empty):= by
  intro ss enoughGas
  cases g_case : symGasAvailable.toNat; rw [g_case] at enoughGas; contradiction
  case succ g_pos =>
  simp [X, δ]
  have enough_gas_rw : (symGasAvailable.toNat < GasConstants.Gverylow) = False :=
    by aesop (add simp [arith_op.C'_comp, arith_op.C'_noexp])
    (add safe (by omega))
  simp [α/- , stack_ok_rw -/, enough_gas_rw]
  have : ((decode ss.executionEnv.code ss.pc).getD (Operation.STOP, none)).1 = op.t := by
    cases op <;> simp [ss, arith_op.t]
  simp [this]
  have : (ss.gasAvailable.toNat < op.C'_comp ss) = False := by
    aesop (add simp [arith_op.C'_comp, ss]) (add safe (by linarith))
  simp [this]
  have gPos : (0 < g_pos) := by
    revert enoughGas; simp [arith_op.C'_comp]
    cases op <;> simp [ss] <;> aesop (add safe (by omega))
  have step_rw (cost : ℕ) := (EVM.step_add_summary op word₁ word₂ word₃ g_pos cost symStack (.ofNat 0) symGasAvailable symRefund symActiveWords symExecLength symReturnData op.to_bin symMemory symAccessedStorageKeys symAccounts symCodeOwner symSender symSource symPerm gPos)
  have stack_ok_rw : (1024 < List.length symStack + 1) = False := by
    cases op <;> aesop (add safe (by omega))
  cases cop: op <;> simp [cop] at symStack_ok <;>
  split <;> rename_i evm cost exec <;> try contradiction
  all_goals (
    simp [EVM.step_arith, cop, add_instr, sub_instr, div_instr] at step_rw
    simp only [cop, arith_op.to_stack_length] at stack_ok_rw
    simp [arith_op.t, ss, cop, stack_ok_rw] at exec
    cases exec
  )
  all_goals (
    simp [Except.instMonad, Except.bind, ss, cop, step_rw, arith_op.t]
    rw [X_bad_pc] <;> aesop (add safe (by omega))
  )

end

end StackOpsSummary
