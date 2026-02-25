import EvmEquivalence.Summaries.MstoreSummary
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.StateMap
import EvmEquivalence.Utils.ListByteArrayUtils

open EvmYul
open StateMap
open KEVMInterface
open MstoreSummary

namespace MstoreOpcodeEquivalence

inductive mstore_op where
  | mstore
  | mstore8

variable (op : mstore_op)

@[simp]
def mstore_op.to_binop : mstore_op → SortBinStackOp
  | .mstore  => .MSTORE_EVM_BinStackOp
  | .mstore8 => .MSTORE8_EVM_BinStackOp

def mstore_op.from_k : mstore_op → MstoreSummary.mstore_op
  | .mstore  => .mstore
  | .mstore8 => .mstore8

@[simp]
def mstore_op.to_width: mstore_op → ℕ
  | .mstore  => 32
  | .mstore8 => 1

/--
Assigns `defn_Val14` to the following propositions depending on the opcode:
`«#asByteStack» W1 = some _Val14` for `MSTORE`
`_modInt_ W1 256 = some _Val14` for `MSTORE8`
 -/
def mstore_op.to_defn_Val14
  (v14Bytes : SortBytes)
  (v14Int W1 : SortInt) : Prop :=
  match op with
  | .mstore => «#asByteStack» W1 = some v14Bytes
  | .mstore8 => _modInt_ W1 256 = some v14Int

/--
Assigns `defn_Val15` to the following propositions depending on the opcode:
`«#asByteStack» W1 = some _Val14` for `MSTORE`
`_modInt_ W1 256 = some _Val14` for `MSTORE8`
 -/
def mstore_op.to_defn_Val15
  (v14Bytes _Val15 : SortBytes)
  (v14Int : SortInt) : Prop :=
  match op with
  | .mstore => «#padToWidth» 32 v14Bytes = some _Val15
  | .mstore8 => buf 1 v14Int = some _Val15

def mstoreLHS
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 : SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) op.to_binop))) _K_CELL },
      exitCode := _Gen20,
      mode := _Gen21,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := USEGAS_CELL },
      ethereum := {
        evm := {
          output := _Gen9,
          statusCode := _Gen10,
          callStack := _Gen11,
          interimStates := _Gen12,
          touchedAccounts := _Gen13,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := _Gen2,
            caller := _Gen3,
            callData := _Gen4,
            callValue := _Gen5,
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
            localMem := { val := LOCALMEM_CELL },
            pc := { val := PC_CELL },
            gas := { val := (@inj SortInt SortGas) GAS_CELL },
            memoryUsed := { val := MEMORYUSED_CELL },
            callGas := _Gen6,
            static := _Gen7,
            callDepth := _Gen8 },
          versionedHashes := _Gen14,
          substate := _Gen15,
          gasPrice := _Gen16,
          origin := _Gen17,
          blockhashes := _Gen18,
          block := _Gen19 },
        network := _DotVar2 } },
    generatedCounter := _DotVar0 }

def mstoreRHS
  {_Val17 _Val24 _Val25 : SortInt}
  {_Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := _K_CELL },
      exitCode := _Gen20,
      mode := _Gen21,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := true },
      ethereum := {
        evm := {
          output := _Gen9,
          statusCode := _Gen10,
          callStack := _Gen11,
          interimStates := _Gen12,
          touchedAccounts := _Gen13,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := _Gen2,
            caller := _Gen3,
            callData := _Gen4,
            callValue := _Gen5,
            wordStack := { val := WS },
            localMem := { val := _Val16 },
            pc := { val := _Val17 },
            gas := { val := (@inj SortInt SortGas) _Val24 },
            memoryUsed := { val := _Val25 },
            callGas := _Gen6,
            static := _Gen7,
            callDepth := _Gen8 },
          versionedHashes := _Gen14,
          substate := _Gen15,
          gasPrice := _Gen16,
          origin := _Gen17,
          blockhashes := _Gen18,
          block := _Gen19 },
        network := _DotVar2 } },
    generatedCounter := _DotVar0 }

theorem rw_mstoreLHS_mstoreRHS
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val14mstore8 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14mstore _Val15 _Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : op.to_defn_Val14 _Val14mstore _Val14mstore8 W1)
  (defn_Val15 : op.to_defn_Val15 _Val14mstore _Val15 _Val14mstore8)
  (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
  (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
  (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
  (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
  (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
  (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
  (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val25)
  (req : _Val13 = true) :
  Rewrites
  (@mstoreLHS op GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 LOCALMEM_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  (@mstoreRHS _Val17 _Val24 _Val25 _Val16 SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  := by
  cases op
  . apply (@Rewrites.MSTORE_SUMMARY_MSTORE_SUMMARY_USEGAS GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8)
    <;> assumption
  . apply (@Rewrites.MSTORE8_SUMMARY_MSTORE8_SUMMARY_USEGAS GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val14mstore8 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8)
    <;> assumption

theorem mstore_prestate_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 : SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK}
  (symState : EVM.State) :
  let lhs := (@mstoreLHS op GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 LOCALMEM_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: (intMap W1) :: wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := executionEnv_map lhs symState,
    substate := substate_map _Gen15 symState.substate
    returnData := _Gen9.val
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    } := by aesop

theorem mstore_poststate_equiv
  {PC_CELL _Val17 _Val24 _Val25 : SortInt}
  {_Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {_Val4 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK}
  (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
  (symState : EVM.State) :
  let rhs := (@mstoreRHS _Val17 _Val24 _Val25 _Val16 SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  stateMap symState rhs =
  {symState with
    stack := wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val24
    executionEnv := executionEnv_map rhs symState,
    substate := substate_map _Gen15 symState.substate
    returnData := _Gen9.val
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    } := by cases _Gen15; aesop (add simp [«_+Int_»])

theorem activeWords_eq
  {MEMORYUSED_CELL W0 _Val25: SortInt}
  (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val25)
  (W0ge0 : 0 ≤ W0)
  (W0small : W0 < UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL)
  (mucsmall : MEMORYUSED_CELL < UInt256.size) :
  activeWords_comp (intMap W0) (intMap MEMORYUSED_CELL) op.to_width = intMap _Val25 := by
  unfold activeWords_comp
  rw [memoryUsageUpdate_rw, Option.some.injEq] at defn_Val25
  case width_pos => aesop
  simp [←defn_Val25, intMap]; rw [UInt256.ofNat_toSigned]
  simp [UInt256.toSigned]; cases mucc: MEMORYUSED_CELL
  <;> try (rw [mucc] at mucge0; contradiction)
  cases wc: W0 <;> try (rw [wc] at W0ge0; contradiction)
  cases op <;>
  aesop (add simp [UInt256.ofNat_toNat]) (add safe (by omega)) (add safe (by congr))

theorem mstore_memory_write_eq
  {W0 W1: SortInt}
  {LOCALMEM_CELL _Val14 _Val15 _Val16 : SortBytes}
  (defn_Val14 : «#asByteStack» W1 = some _Val14)
  (defn_Val15 : «#padToWidth» 32 _Val14 = some _Val15)
  (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  (W0small : W0 < UInt256.size)
  (W1small : W1 < UInt256.size)
  -- As per the YP:
  -- "Due to [the fee shceme] it is highly unlikely [memory] addresses will ever go above 32-bit bounds"
  -- It seems we need this hypothesis to achieve equivalence of behavior from the EVMYul side
  -- We keep the original `W0small` for convenience
  (W0small_realpolitik : W0 < UInt32.size)
  :
  mstore_memory_write (intMap W0) (intMap W1) LOCALMEM_CELL = _Val16 := by
  -- TODO: This proof can probably be amply optimized
  simp [mstore_memory_write]
  simp [ByteArray.write, ByteArray.copySlice, Axioms.ffi_zeroes]
  simp [UInt256.toByteArray_size, UInt256.toArray_size]
  simp [ByteArray.size]; rw [intMap_toNat] <;> try linarith
  simp [@Array.extract_of_size_le _ _ (Int.toNat W0 + 32)]
  rw [@Nat.sub_eq_zero_of_le (USize.toNat _)]
  case h => apply Nat.le_trans (USize.toNat_ofNat_le _); omega
  -- Getting `mapWriteRange` to manipulate EvmYul values
  cases w1c : W1 <;> rw [w1c] at W1small W1ge0 defn_Val14
  case negSucc => simp_all
  rename_i w1
  rw [Int.ofNat_eq_coe, Int.ofNat_lt] at W1small
  have bs_eq : «#asByteStack» ↑w1 = some _Val14 := by aesop
  rw [padToWidth32_asByteStack_rw W1small, Option.some.injEq] at defn_Val15
  <;> try exact bs_eq
  -- Treating with `mapWriteRange`
  revert defn_Val16
  rw [←defn_Val15]
  simp [mapWriteRange_rw, Axioms.ffi_zeroes]
  rw [replicate_size_32] <;> try assumption
  split; linarith
  split; linarith
  simp [«replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes»]
  intro h1 h2 h3; subst h3
  simp [«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  have : (intMap ↑w1).toNat = w1 := by rw [intMap_toNat, Int.toNat_ofNat] <;> try linarith
  simp_all [ByteArray.size]
  rw [Int.toNat_add] <;> try linarith
  rw [sub_add_BE_32 W1small]
  simp [@Array.extract_of_size_le _ _ (Int.toNat W0 + 32)]
  rw [Array.append_cancel_left_eq]
  rw [Array.append_cancel_left]
  case ofNat.isFalse.isFalse.a =>
    rw [←Int.toNat_lt_toNat] at W0small_realpolitik <;> try simp
    rw [USize.toNat_ofNat_eq] <;>
    aesop (add simp [UInt32.size]) (add safe (by omega))
  conv => rhs; rw [←Array.append_assoc]
  rw [Array.append_cancel_right_eq]
  have extract_32_eq : (intMap ↑w1).toByteArray.data.extract 0 32 = (intMap ↑w1).toByteArray.data := by
    have := UInt256.toByteArray_size
    simp [ByteArray.size] at this
    aesop
  rw [extract_32_eq, UInt256.toByteArray]
  rw [←ByteArray.append_array_data, Axioms.ffi_zeroes]; simp only
  congr

theorem step_mstore_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val14mstore8 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14mstore _Val15 _Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : op.to_defn_Val14 _Val14mstore _Val14mstore8 W1)
  (defn_Val15 : op.to_defn_Val15 _Val14mstore _Val15 _Val14mstore8)
  (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
  (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
  (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
  (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
  (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
  (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
  (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val25)
  (req : _Val13 = true)
  (symState : EVM.State)
  -- Necessary for EVM.step
  (gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : 0 < GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  (W0small : W0 < UInt256.size)
  (W1small : W1 < UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL)
  (mucsmall : MEMORYUSED_CELL < UInt256.size)
  -- As per the YP:
  -- "Due to [the fee shceme] it is highly unlikely [memory] addresses will ever go above 32-bit bounds"
  -- It seems we need this hypothesis to achieve equivalence of behavior from the EVMYul side
  -- We keep the original `W0small` for convenience
  (W0small_realpolitik : W0 < UInt32.size) :
  EVM.step_mstore op.from_k (Int.toNat GAS_CELL) gasCost (stateMap symState (@mstoreLHS op GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 LOCALMEM_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@mstoreRHS _Val17 _Val24 _Val25 _Val16 SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL))
  := by
  cases cg: (Int.toNat GAS_CELL)
  next =>
    rw [Int.toNat_eq_zero] at cg
    have _ := Int.lt_of_lt_of_le gavailEnough cg; contradiction
  rename_i g
  cases _Gen15 with
  | mk selfDestruct log refund accessedAccounts accessedStorage createdAccounts =>
  rw [mstore_prestate_equiv]; simp [mstoreLHS]
  have ms_rw := EVM.step_mstore_summary op.from_k
  unfold EVM.step_mstore mstore_op.get at ms_rw
  rw [ms_rw] <;> first | assumption | try simp
  rw [mstore_poststate_equiv, mstoreRHS] <;> first | assumption | try simp
  simp [activeWords_comp]
  constructor; constructor <;> try constructor
  . sorry -- Gas goals are for now unproven
  . have aw_rw := activeWords_eq op defn_Val25
    cases op <;> simp [mstore_op.from_k] <;> aesop
  . cases op <;> simp [mstore_op.from_k]
    . rw [mstore_memory_write_eq defn_Val14 defn_Val15 defn_Val16] <;> assumption
    . -- `mstore8_memory_write (intMap W0) (intMap W1) LOCALMEM_CELL = _Val16`
      sorry
      -- We need to provde a `mstore8_memory_write_eq` theorem
      -- similar to `mstore_memory_write_eq`.
      -- Then, something like the following should solve it:
      -- `rw [mstore8_memory_write_eq defn_Val14 defn_Val15 defn_Val16] <;> assumption`
  . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop

private theorem mec_ceil_bound (f l : ℕ) (hf : f < UInt32.size) (hl : l ≤ 32) :
    (f + l + 31) / 32 ≤ 134217730 := by
  have : UInt32.size = 4294967296 := rfl
  have : f + l + 31 ≤ 4294967358 := by omega
  exact Nat.le_trans (Nat.div_le_div_right this) (by norm_num)

private theorem mec_M_bound (s f l : ℕ) (hf : f < UInt32.size) (hl : l ≤ 32) :
    MachineState.M s f l ≤ Nat.max s 134217730 := by
  unfold MachineState.M
  cases l with
  | zero => simp
  | succ n =>
    have hceil : (f + (n + 1) + 31) / 32 ≤ 134217730 :=
      mec_ceil_bound f (n + 1) hf (by omega)
    exact max_le_max_left s hceil

private theorem mec_Cm_bound_const : EVM.Cₘ (UInt256.ofNat 134217730) < UInt256.size := by
  native_decide

private theorem mec_Cm_mono (a b : UInt256) (h : a.toNat ≤ b.toNat) :
    EVM.Cₘ a ≤ EVM.Cₘ b := by
  simp [EVM.Cₘ, EVM.Cₘ.QuadraticCeofficient]
  have h1 : GasConstants.Gmemory * a.toNat ≤ GasConstants.Gmemory * b.toNat :=
    Nat.mul_le_mul_left _ h
  have h2 : a.toNat * a.toNat / 512 ≤ b.toNat * b.toNat / 512 :=
    Nat.div_le_div_right (Nat.mul_le_mul h h)
  omega

/-- Connects the KEVM `Cmem` function on the CANCUN schedule to the EVM `Cₘ` function. -/
private theorem Cmem_cancun_eq_Cm (N : SortInt) (hN : 0 ≤ N) (hNs : N < ↑UInt256.size) :
    Cmem .CANCUN_EVM N = some ↑(EVM.Cₘ (intMap N)) := by
  simp [Cmem, GAS_FEES_Cmem, «_*Int_», «_/Int_», «_+Int_», GasInterface.cancun_def]
  simp [EVM.Cₘ, EVM.Cₘ.QuadraticCeofficient, GasConstants.Gmemory]
  rw [intMap_toNat hN hNs]
  cases N with
  | ofNat n =>
    simp [Int.toNat]
    conv_lhs => rw [show (↑n * ↑n : Int) = ↑(n * n) from by push_cast; ring]
    rw [show Int.tdiv ↑(n * n) (512 : Int) = ↑(n * n / 512) from Int.ofNat_tdiv _ _]
    push_cast; ring
  | negSucc n =>
    exfalso; exact absurd hN (by simp)

private theorem vawg_eq_intMap
  {MEMORYUSED_CELL W0 _Val18 : SortInt}
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (W0ge0 : 0 ≤ W0) (W0small : W0 < ↑UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) (mucsmall : MEMORYUSED_CELL < ↑UInt256.size) :
  value_and_activeWords_gas op.from_k (intMap W0) (intMap MEMORYUSED_CELL) = intMap _Val18 := by
  have aw := activeWords_eq op defn_Val18 W0ge0 W0small mucge0 mucsmall
  simp [value_and_activeWords_gas, activeWords_comp, MachineState.M] at aw ⊢
  cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.from_k, mstore_op.to_l,
    MstoreOpcodeEquivalence.mstore_op.to_width] at aw ⊢ <;> exact aw

private theorem memUsageUpdate_nonneg
  {MEMORYUSED_CELL W0 _Val18 : SortInt}
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) :
  0 ≤ _Val18 := by
  have hw : (0 : SortInt) < op.to_width := by cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.to_width] <;> omega
  rw [memoryUsageUpdate_rw _ _ _ hw, Option.some.injEq] at defn_Val18
  subst defn_Val18
  exact le_sup_of_le_left mucge0

private theorem memUsageUpdate_small
  {MEMORYUSED_CELL W0 _Val18 : SortInt}
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (W0ge0 : 0 ≤ W0)
  (mucsmall : MEMORYUSED_CELL < ↑UInt256.size)
  (W0small_realpolitik : W0 < ↑UInt32.size) :
  _Val18 < ↑UInt256.size := by
  have hw_pos : (0 : SortInt) < op.to_width := by
    cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.to_width]
  have hw_le : (op.to_width : SortInt) ≤ 32 := by
    cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.to_width]
  rw [memoryUsageUpdate_rw _ _ _ hw_pos, Option.some.injEq] at defn_Val18
  subst defn_Val18
  have hsum_nonneg : 0 ≤ W0 + ↑op.to_width + 31 := by linarith
  have hceil_le : Int.tdiv (W0 + ↑op.to_width + 31) 32 ≤ W0 + ↑op.to_width + 31 :=
    Int.tdiv_le_self 32 hsum_nonneg
  have hsum_bound : W0 + ↑op.to_width + 31 < ↑UInt256.size := by
    have : (UInt256.size : ℤ) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      simp [UInt256.size]
    have : (UInt32.size : ℤ) = 4294967296 := by simp [UInt32.size]
    linarith
  exact max_lt mucsmall (lt_of_le_of_lt hceil_le hsum_bound)

/-- Proves the gas correctness goal in `X_mstore_equiv`: the KEVM gas chain
    (Cmem subtractions via `_-Int_`) equals the EVM `memoryExpansionCost` (via `Cₘ`). -/
private theorem gas_cost_X_equiv
  {GAS_CELL MEMORYUSED_CELL W0 _Val18 _Val19 _Val20 _Val21 _Val22 _Val23 _Val24 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
  (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
  (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
  (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
  (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0) (W0small : W0 < ↑UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) (mucsmall : MEMORYUSED_CELL < ↑UInt256.size)
  (W0small_realpolitik : W0 < ↑UInt32.size)
  (hmec_le_gas : _Val21 ≤ GAS_CELL)
  (hgvl_le : _Val23 ≤ GAS_CELL - _Val21) :
  intMap GAS_CELL -
    UInt256.ofNat (EVM.Cₘ (value_and_activeWords_gas op.from_k (intMap W0) (intMap MEMORYUSED_CELL)) -
                   EVM.Cₘ (intMap MEMORYUSED_CELL)) -
    UInt256.ofNat GasConstants.Gverylow = intMap _Val24 := by
  -- Extract concrete values from the KEVM chain
  have eq21 : _Val19 - _Val20 = _Val21 := by simp [«_-Int_»] at defn_Val21; exact defn_Val21
  have eq22 : GAS_CELL - _Val21 = _Val22 := by simp [«_-Int_»] at defn_Val22; exact defn_Val22
  have eq24 : _Val22 - _Val23 = _Val24 := by simp [«_-Int_»] at defn_Val24; exact defn_Val24
  have eq23 : _Val23 = 3 := by
    rw [cancun] at defn_Val23; simp [GasInterface.cancun_def] at defn_Val23; exact defn_Val23.symm
  -- Compute _Val19, _Val20 via Cmem_cancun_eq_Cm
  have h18_nn := memUsageUpdate_nonneg op defn_Val18 mucge0
  have h18_sm := memUsageUpdate_small op defn_Val18 W0ge0 mucsmall W0small_realpolitik
  have eq19 : _Val19 = ↑(EVM.Cₘ (intMap _Val18)) := by
    have := Cmem_cancun_eq_Cm _Val18 h18_nn h18_sm
    rw [cancun] at defn_Val19; rw [this] at defn_Val19
    exact (Option.some.inj defn_Val19).symm
  have eq20 : _Val20 = ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) := by
    have := Cmem_cancun_eq_Cm MEMORYUSED_CELL mucge0 mucsmall
    rw [cancun] at defn_Val20; rw [this] at defn_Val20
    exact (Option.some.inj defn_Val20).symm
  -- Rewrite value_and_activeWords_gas to intMap _Val18
  rw [vawg_eq_intMap op defn_Val18 W0ge0 W0small mucge0 mucsmall]
  -- Cₘ monotonicity: cmmu ≤ cm18
  have hCm_le : EVM.Cₘ (intMap MEMORYUSED_CELL) ≤ EVM.Cₘ (intMap _Val18) := by
    apply mec_Cm_mono
    rw [intMap_toNat mucge0 mucsmall, intMap_toNat h18_nn h18_sm]
    have hw : (0 : SortInt) < op.to_width := by
      cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.to_width]
    have defn18' := defn_Val18
    rw [memoryUsageUpdate_rw _ _ _ hw] at defn18'
    have eq18 : _Val18 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + ↑op.to_width + 31) 32 :=
      (Option.some.inj defn18').symm
    rw [eq18]
    exact Int.toNat_le_toNat (le_max_left _ _)
  -- Derive _Val24 = GAS_CELL - (↑cm18 - ↑cmmu) - 3
  have hv24 : _Val24 = GAS_CELL - (↑(EVM.Cₘ (intMap _Val18)) - ↑(EVM.Cₘ (intMap MEMORYUSED_CELL))) - 3 := by
    rw [← eq24, ← eq22, ← eq21, eq19, eq20, eq23]
  rw [hv24]
  -- Introduce names for Cₘ values to help with opaque terms
  set cm18 := EVM.Cₘ (intMap _Val18) with hcm18_def
  set cmmu := EVM.Cₘ (intMap MEMORYUSED_CELL) with hcmmu_def
  -- Simplify ↑cm18 - ↑cmmu = ↑(cm18 - cmmu) using Nat.cast_sub
  have hcast : (↑cm18 : SortInt) - ↑cmmu = ↑(cm18 - cmmu) := (Nat.cast_sub hCm_le).symm
  rw [hcast]
  simp only [GasConstants.Gverylow]
  -- Bounds for intMap_sub_dist (derived from hmec_le_gas and hgvl_le)
  have hmec_le : (↑(cm18 - cmmu) : SortInt) ≤ GAS_CELL := by
    rw [← hcast, ← eq19, ← eq20, eq21]; exact hmec_le_gas
  have h3_le : (3 : SortInt) ≤ GAS_CELL - ↑(cm18 - cmmu) := by
    rw [← hcast, ← eq19, ← eq20, eq21, ← eq23]; exact hgvl_le
  rw [intMap_sub_dist h3_le (by norm_num) (by linarith)]
  rw [intMap_sub_dist hmec_le (Int.natCast_nonneg _) gavailSmall]
  simp [intMap, UInt256.toSigned]

theorem X_mstore_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val14mstore8 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14mstore _Val15 _Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortStatusCodeCell}
  {_Gen11 : SortCallStackCell}
  {_Gen12 : SortInterimStatesCell}
  {_Gen13 : SortTouchedAccountsCell}
  {_Gen14 : SortVersionedHashesCell}
  {_Gen15 : SortSubstateCell}
  {_Gen16 : SortGasPriceCell}
  {_Gen17 : SortOriginCell}
  {_Gen18 : SortBlockhashesCell}
  {_Gen19 : SortBlockCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortExitCodeCell}
  {_Gen21 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortCallGasCell}
  {_Gen7 : SortStaticCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortOutputCell}
  {_K_CELL : SortK}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : op.to_defn_Val14 _Val14mstore _Val14mstore8 W1)
  (defn_Val15 : op.to_defn_Val15 _Val14mstore _Val15 _Val14mstore8)
  (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
  (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
  (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
  (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
  (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
  (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
  (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
  (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 op.to_width = some _Val25)
  (req : _Val13 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : 0 < GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  (W0small : W0 < UInt256.size)
  (W1small : W1 < UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL)
  (mucsmall : MEMORYUSED_CELL < UInt256.size)
  (codeMstore : _Gen0 = ⟨op.from_k.to_bin⟩)
  (pcZero : PC_CELL = 0)
  -- TODO: Replace with a native measure for `SortWordStack` and
  -- prove this assumption via an equality theorem stating that
  -- `List.length (wordStackMap WS) = wordStackLength WS`
  (stackOk: List.length (wordStackMap WS) < 1024)
  -- As per the YP:
  -- "Due to [the fee shceme] it is highly unlikely [memory] addresses will ever go above 32-bit bounds"
  -- It seems we need this hypothesis to achieve equivalence of behavior from the EVMYul side
  -- We keep the original `W0small` for convenience
  (W0small_realpolitik : W0 < UInt32.size) :
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState (@mstoreLHS op GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 LOCALMEM_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@mstoreRHS _Val17 _Val24 _Val25 _Val16 SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 ⟨.empty⟩ _K_CELL)) .empty)
  := by
  cases cg: (Int.toNat GAS_CELL)
  next =>
    rw [Int.toNat_eq_zero] at cg
    have _ := Int.lt_of_lt_of_le gavailEnough cg; contradiction
  rw [pcZero, codeMstore, mstore_prestate_equiv, mstore_poststate_equiv]
  <;> try assumption
  cases _Gen15 with
  | mk selfDestruct log refund accessedAccounts accessedStorage createdAccounts =>
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  simp [mstoreLHS, mstoreRHS]; rw [pc_equiv, X_mstore_summary] <;> try assumption
  . simp; constructor <;> try constructor <;> try constructor
    . -- Gas correctness goal
      rw [memoryExpansionCost_mstore op.from_k (wordStackMap WS) (intMap W0) (intMap W1) (intMap MEMORYUSED_CELL) _ rfl rfl]
      -- Derive variable equalities across duplicated KEVM computation chains
      have eq_0_18 : _Val0 = _Val18 := Option.some.inj (defn_Val0.symm.trans defn_Val18)
      have eq_1_19 : _Val1 = _Val19 := by
        have h := defn_Val1; rw [eq_0_18] at h; exact Option.some.inj (h.symm.trans defn_Val19)
      have eq_2_20 : _Val2 = _Val20 := Option.some.inj (defn_Val2.symm.trans defn_Val20)
      have eq_3_21 : _Val3 = _Val21 := by
        have h3 := defn_Val3; have h21 := defn_Val21
        simp [«_-Int_»] at h3 h21; rw [← h3, ← h21, eq_1_19, eq_2_20]
      have eq_5_23 : _Val5 = _Val23 := Option.some.inj (defn_Val5.symm.trans defn_Val23)
      have eq_6_18 : _Val6 = _Val18 := Option.some.inj (defn_Val6.symm.trans defn_Val18)
      have eq_7_19 : _Val7 = _Val19 := by
        have h := defn_Val7; rw [eq_6_18] at h; exact Option.some.inj (h.symm.trans defn_Val19)
      have eq_8_20 : _Val8 = _Val20 := Option.some.inj (defn_Val8.symm.trans defn_Val20)
      have eq_9_21 : _Val9 = _Val21 := by
        have h9 := defn_Val9; have h21 := defn_Val21
        simp [«_-Int_»] at h9 h21; rw [← h9, ← h21, eq_7_19, eq_8_20]
      have eq_10_22 : _Val10 = _Val22 := by
        have h10 := defn_Val10; have h22 := defn_Val22
        simp [«_-Int_»] at h10 h22; rw [← h10, ← h22, eq_9_21]
      -- Extract gas bounds from `req`
      have hbool13 : USEGAS_CELL = true ∧ _Val12 = true := by
        have h := defn_Val13; simp [andBool_def] at h; rw [← h] at req; exact Bool.and_eq_true_iff.mp req
      have hbool12 : _Val4 = true ∧ _Val11 = true := by
        have h := defn_Val12; simp [andBool_def] at h; rw [← h] at hbool13; exact Bool.and_eq_true_iff.mp hbool13.2
      have hmec_le_gas : _Val21 ≤ GAS_CELL := by
        have h := defn_Val4; simp [«_<=Int_»] at h; rw [← h] at hbool12
        rw [← eq_3_21]; exact of_decide_eq_true hbool12.1
      have hgvl_le : _Val23 ≤ GAS_CELL - _Val21 := by
        have h := defn_Val11; simp [«_<=Int_»] at h; rw [← h] at hbool12
        have hle : _Val5 ≤ _Val10 := of_decide_eq_true hbool12.2
        rw [eq_5_23] at hle; rw [eq_10_22] at hle
        have h22 := defn_Val22; simp [«_-Int_»] at h22
        linarith
      exact gas_cost_X_equiv op defn_Val18 defn_Val19 defn_Val20 defn_Val21 defn_Val22 defn_Val23 defn_Val24
            cancun gavailSmall W0ge0 W0small mucge0 mucsmall W0small_realpolitik hmec_le_gas hgvl_le
    . have aw_rw := activeWords_eq op defn_Val25
      cases op <;> simp [mstore_op.from_k] <;> aesop
    . cases op <;> simp [mstore_op.from_k]
      . rw [mstore_memory_write_eq defn_Val14 defn_Val15 defn_Val16] <;> assumption
      . -- `mstore8_memory_write (intMap W0) (intMap W1) LOCALMEM_CELL = _Val16`
        sorry
      -- We need to provde a `mstore8_memory_write_eq` theorem
      -- similar to `mstore_memory_write_eq`.
      -- Then, something like the following should solve it:
      -- `rw [mstore8_memory_write_eq defn_Val14 defn_Val15 defn_Val16] <;> assumption`
    . aesop
  . -- Enough Gas
    cases op <;> simp [mstore_op.from_k] <;> omega
  . -- Gas is not greater than `UInt256.size`
    rw [memoryExpansionCost_mstore op.from_k (wordStackMap WS) (intMap W0) (intMap W1) (intMap MEMORYUSED_CELL) _ rfl rfl,
        vawg_eq_intMap op defn_Val18 W0ge0 W0small mucge0 mucsmall]
    -- Re-derive variable equalities across duplicated KEVM computation chains
    have eq_0_18 : _Val0 = _Val18 := Option.some.inj (defn_Val0.symm.trans defn_Val18)
    have eq_1_19 : _Val1 = _Val19 := by
      have h := defn_Val1; rw [eq_0_18] at h; exact Option.some.inj (h.symm.trans defn_Val19)
    have eq_2_20 : _Val2 = _Val20 := Option.some.inj (defn_Val2.symm.trans defn_Val20)
    have eq_3_21 : _Val3 = _Val21 := by
      have h3 := defn_Val3; have h21 := defn_Val21
      simp [«_-Int_»] at h3 h21; rw [← h3, ← h21, eq_1_19, eq_2_20]
    have eq_5_23 : _Val5 = _Val23 := Option.some.inj (defn_Val5.symm.trans defn_Val23)
    have eq_6_18 : _Val6 = _Val18 := Option.some.inj (defn_Val6.symm.trans defn_Val18)
    have eq_7_19 : _Val7 = _Val19 := by
      have h := defn_Val7; rw [eq_6_18] at h; exact Option.some.inj (h.symm.trans defn_Val19)
    have eq_8_20 : _Val8 = _Val20 := Option.some.inj (defn_Val8.symm.trans defn_Val20)
    have eq_9_21 : _Val9 = _Val21 := by
      have h9 := defn_Val9; have h21 := defn_Val21
      simp [«_-Int_»] at h9 h21; rw [← h9, ← h21, eq_7_19, eq_8_20]
    have eq_10_22 : _Val10 = _Val22 := by
      have h10 := defn_Val10; have h22 := defn_Val22
      simp [«_-Int_»] at h10 h22; rw [← h10, ← h22, eq_9_21]
    -- Extract gas bounds from req
    have hbool13 : USEGAS_CELL = true ∧ _Val12 = true := by
      have h := defn_Val13; simp [andBool_def] at h; rw [← h] at req; exact Bool.and_eq_true_iff.mp req
    have hbool12 : _Val4 = true ∧ _Val11 = true := by
      have h := defn_Val12; simp [andBool_def] at h; rw [← h] at hbool13; exact Bool.and_eq_true_iff.mp hbool13.2
    have hmec_le_gas : _Val21 ≤ GAS_CELL := by
      have h := defn_Val4; simp [«_<=Int_»] at h; rw [← h] at hbool12
      rw [← eq_3_21]; exact of_decide_eq_true hbool12.1
    have hgvl_le : _Val23 ≤ GAS_CELL - _Val21 := by
      have h := defn_Val11; simp [«_<=Int_»] at h; rw [← h] at hbool12
      have hle : _Val5 ≤ _Val10 := of_decide_eq_true hbool12.2
      rw [eq_5_23] at hle; rw [eq_10_22] at hle
      have h22 := defn_Val22; simp [«_-Int_»] at h22
      linarith
    -- Get _Val23 = 3 (Gverylow for Cancun)
    have eq23 : _Val23 = 3 := by
      rw [cancun] at defn_Val23; simp [GasInterface.cancun_def] at defn_Val23; exact defn_Val23.symm
    -- Connect Cmem to Cₘ
    have h18_nn := memUsageUpdate_nonneg op defn_Val18 mucge0
    have h18_sm := memUsageUpdate_small op defn_Val18 W0ge0 mucsmall W0small_realpolitik
    have eq19 : _Val19 = ↑(EVM.Cₘ (intMap _Val18)) := by
      have := Cmem_cancun_eq_Cm _Val18 h18_nn h18_sm
      rw [cancun] at defn_Val19; rw [this] at defn_Val19
      exact (Option.some.inj defn_Val19).symm
    have eq20 : _Val20 = ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) := by
      have := Cmem_cancun_eq_Cm MEMORYUSED_CELL mucge0 mucsmall
      rw [cancun] at defn_Val20; rw [this] at defn_Val20
      exact (Option.some.inj defn_Val20).symm
    -- Cₘ monotonicity: Cₘ(intMap MEMORYUSED_CELL) ≤ Cₘ(intMap _Val18)
    have hCm_le : EVM.Cₘ (intMap MEMORYUSED_CELL) ≤ EVM.Cₘ (intMap _Val18) := by
      apply mec_Cm_mono
      rw [intMap_toNat mucge0 mucsmall, intMap_toNat h18_nn h18_sm]
      have hw : (0 : SortInt) < op.to_width := by
        cases op <;> simp [MstoreOpcodeEquivalence.mstore_op.to_width]
      have defn18' := defn_Val18
      rw [memoryUsageUpdate_rw _ _ _ hw] at defn18'
      have eq18 : _Val18 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + ↑op.to_width + 31) 32 :=
        (Option.some.inj defn18').symm
      rw [eq18]
      exact Int.toNat_le_toNat (le_max_left _ _)
    -- _Val21 = ↑(Cₘ(intMap _Val18) - Cₘ(intMap MEMORYUSED_CELL))
    have eq21_z : _Val21 = ↑(EVM.Cₘ (intMap _Val18)) - ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) := by
      have h := defn_Val21; simp [«_-Int_»] at h; rw [← h, eq19, eq20]
    have h21_nn : 0 ≤ _Val21 := by
      rw [eq21_z]; exact sub_nonneg.mpr (Nat.cast_le.mpr hCm_le)
    have hCm_diff : _Val21.toNat = EVM.Cₘ (intMap _Val18) - EVM.Cₘ (intMap MEMORYUSED_CELL) := by
      rw [eq21_z, show (↑(EVM.Cₘ (intMap _Val18)) - ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) : ℤ) =
        ↑(EVM.Cₘ (intMap _Val18) - EVM.Cₘ (intMap MEMORYUSED_CELL)) from (Nat.cast_sub hCm_le).symm]
      exact Int.toNat_natCast _
    -- Final: GasConstants.Gverylow ≤ (intMap GAS_CELL).toNat - (Cₘ ... - Cₘ ...)
    simp only [GasConstants.Gverylow]
    rw [intMap_toNat (le_of_lt gavailEnough) gavailSmall, ← hCm_diff]
    -- Goal: 3 ≤ GAS_CELL.toNat - _Val21.toNat
    have h3_le : 3 ≤ GAS_CELL - _Val21 := by rw [← eq23]; exact hgvl_le
    have hGAS_nn : 0 ≤ GAS_CELL := le_of_lt gavailEnough
    have h_sub_nn : 0 ≤ GAS_CELL - _Val21 := by linarith
    have h_sub_eq : ↑(GAS_CELL - _Val21).toNat = GAS_CELL - _Val21 :=
      Int.toNat_of_nonneg h_sub_nn
    have h_gas_eq : ↑GAS_CELL.toNat = GAS_CELL := Int.toNat_of_nonneg hGAS_nn
    have h_val_eq : ↑_Val21.toNat = _Val21 := Int.toNat_of_nonneg h21_nn
    have h_sub_nat : (GAS_CELL - _Val21).toNat = GAS_CELL.toNat - _Val21.toNat := by
      zify [Int.toNat_le_toNat hmec_le_gas]
      rw [h_sub_eq, h_gas_eq, h_val_eq]
    have h1 : (3 : ℤ).toNat ≤ (GAS_CELL - _Val21).toNat := Int.toNat_le_toNat h3_le
    simp at h1
    linarith
  . -- `memoryExpansionCost < UInt256.size`
    rw [memoryExpansionCost_mstore op.from_k (wordStackMap WS) (intMap W0) (intMap W1) (intMap MEMORYUSED_CELL) _ rfl rfl]
    have hoff : (intMap W0).toNat < UInt32.size := by
      rw [intMap_toNat W0ge0 W0small]
      exact (Int.toNat_lt_toNat (by linarith : (0 : ℤ) < (↑UInt32.size : ℤ))).mpr W0small_realpolitik
    have hl : op.from_k.to_l ≤ 32 := by cases op <;> simp [mstore_op.from_k, MstoreSummary.mstore_op.to_l]
    simp only [value_and_activeWords_gas]
    have hb := mec_M_bound (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat op.from_k.to_l hoff hl
    by_cases haw : (intMap MEMORYUSED_CELL).toNat ≤ 134217730
    · -- aw ≤ bound: M ≤ bound
      have hM_le : MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat op.from_k.to_l ≤ 134217730 :=
        le_trans hb (Nat.max_le_of_le_of_le haw (le_refl _))
      have hM_small : MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat op.from_k.to_l < UInt256.size := by
        have : UInt256.size = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := rfl; omega
      have hCm := mec_Cm_mono
        (UInt256.ofNat (MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat op.from_k.to_l))
        (UInt256.ofNat 134217730)
        (by rw [UInt256.ofNat_toNat hM_small, UInt256.ofNat_toNat (by native_decide)]; exact hM_le)
      have := mec_Cm_bound_const
      omega
    · -- aw > bound: M = aw, cost = 0
      push_neg at haw
      have hM_eq : MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat op.from_k.to_l = (intMap MEMORYUSED_CELL).toNat := by
        unfold MachineState.M
        have hceil := mec_ceil_bound (intMap W0).toNat op.from_k.to_l hoff hl
        cases op <;> simp [mstore_op.from_k, MstoreSummary.mstore_op.to_l] at hceil ⊢ <;> omega
      rw [hM_eq]
      have hrt : (UInt256.ofNat (intMap MEMORYUSED_CELL).toNat) = (intMap MEMORYUSED_CELL) := by
        simp [UInt256.ofNat, UInt256.toNat]; rfl
      rw [hrt]; simp [UInt256.size]

end MstoreOpcodeEquivalence
