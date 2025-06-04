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
  --rw [ByteArray.append_empty]
  simp [UInt256.toByteArray_size, UInt256.toArray_size]
  have : USize.toNat (OfNat.ofNat ((intMap W0).toNat - LOCALMEM_CELL.data.size)) ≤
    ((intMap W0).toNat - LOCALMEM_CELL.data.size) := by
    cases System.Platform.numBits_eq <;> simp_all [USize.toNat] <;>
    aesop (add safe (by omega))
  simp [ByteArray.size, this]; rw [intMap_toNat] <;> try linarith
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
  rw [←defn_Val15]; simp [mapWriteRange_rw, Axioms.ffi_zeroes]
  rw [zeroes_size_eq_sub] <;> try assumption
  split; linarith
  rw [ByteArray.size_append, ByteArray.size]; simp [Array.toList]
  split; omega; rw [UInt256.toByteArray]
  simp [«replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes»]
  intro h1 h2 h3; subst h3
  simp [«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int», Axioms.ffi_zeroes]
  have _ : (intMap W0).toNat = Int.toNat W0 := by apply intMap_toNat <;> assumption
  have _ := BE_size_le_32 _ W1small
  have : (intMap ↑w1).toNat = w1 := by rw [intMap_toNat, Int.toNat_ofNat] <;> try linarith
  simp_all [ByteArray.size]
  have : (Int.toNat W0 - LOCALMEM_CELL.data.size) ⊓
    (Int.toNat W0 + Int.toNat 32 - LOCALMEM_CELL.data.size) =
    (Int.toNat W0 - LOCALMEM_CELL.data.size) := by omega
  rw [Int.toNat_add, this] <;> try linarith
  have : (BE w1).data.size = (BE w1).size := rfl
  rw [this, zeroes_size_eq_sub] <;> try exact W1small
  rw [Nat.min_eq_right] <;> try omega
  simp [@Array.extract_of_size_le _ _ (Int.toNat W0 + 32)]
  have _ : (BE w1).data.extract 0 (32 - (32 - (BE w1).size)) = (BE w1).data := by
    simp [Array.extract_eq_self_of_le]; right; rw [Nat.sub_sub_self]; rfl; assumption
  congr; rw [USize.toNat_ofNat_eq]
  -- This is when we require the hipothesis `W0small_realpolitik`
  rw [←Int.toNat_lt_toNat] at W0small_realpolitik <;> try simp
  aesop (add simp [UInt32.size]) (add safe (by omega))

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
  (W0small_realpolitik : W0 < UInt32.size):
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
  simp [activeWords_comp, mstore_memory_write]
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
      /- rw [memoryExpansionCost_mstore op (wordStackMap WS) (intMap W0) (intMap MEMORYUSED_CELL)]
      simp [EVM.Cₘ] -/
      sorry
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
    sorry
  . -- Gas is not greater than `UInt256.size`
    simp [EVM.memoryExpansionCost, EVM.Cₘ, EVM.memoryExpansionCost.μᵢ', MachineState.M]
    sorry
  . -- `memoryExpansionCost < UInt256.size`
    sorry

end MstoreOpcodeEquivalence
