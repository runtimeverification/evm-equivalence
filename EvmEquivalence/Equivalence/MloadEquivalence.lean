import EvmEquivalence.Summaries.MloadSummary
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.StateMap
import EvmEquivalence.Utils.ListByteArrayUtils
import EvmEquivalence.Equivalence.MstoreEquivalence

open EvmYul
open StateMap
open KEVMInterface
open MstoreSummary
open MloadSummary

namespace MloadOpcodeEquivalence

def mloadLHS
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0: SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
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
  {_WS : SortWordStack} : SortGeneratedTopCell :=
  {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.MLOAD_EVM_UnStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 _WS },
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

def mloadRHS
  {_Val15 _Val16 _Val23 _Val24 : SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
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
  {_WS : SortWordStack} : SortGeneratedTopCell :=
  {
      kevm := {
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val15 _WS },
              localMem := { val := LOCALMEM_CELL },
              pc := { val := _Val16 },
              gas := { val := (@inj SortInt SortGas) _Val23 },
              memoryUsed := { val := _Val24 },
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

theorem rw_mloadLHS_mloadRHS
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 _Val0 _Val1 _Val10 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
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
  {_WS : SortWordStack}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : «#range» LOCALMEM_CELL W0 32 = some _Val14)
  (defn_Val15 : asWord _Val14 = some _Val15)
  (defn_Val16 : «_+Int_» PC_CELL 1 = some _Val16)
  (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
  (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
  (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
  (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
  (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
  (defn_Val23 : «_-Int_» _Val21 _Val22 = some _Val23)
  (defn_Val24 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val24)
  (req : _Val13 = true) :
  Rewrites
  (@mloadLHS GAS_CELL MEMORYUSED_CELL PC_CELL W0 LOCALMEM_CELL SCHEDULE_CELL
    USEGAS_CELL _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13
    _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4
    _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL _WS)
  (@mloadRHS _Val15 _Val16 _Val23 _Val24 LOCALMEM_CELL SCHEDULE_CELL _DotVar0
    _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16
    _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7
    _Gen8 _Gen9 _K_CELL _WS)
  := by
  apply (@Rewrites.MLOAD_SUMMARY_MLOAD_SUMMARY_USEGAS GAS_CELL MEMORYUSED_CELL
    PC_CELL W0 _Val0 _Val1 _Val10 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2
    _Val20 _Val21 _Val22 _Val23 _Val24 _Val3 _Val5 _Val6 _Val7 _Val8)
  <;> assumption

theorem mload_prestate_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0: SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
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
  {_WS : SortWordStack}
  (symState : EVM.State):
  let lhs :=
  (@mloadLHS GAS_CELL MEMORYUSED_CELL PC_CELL W0 LOCALMEM_CELL SCHEDULE_CELL
    USEGAS_CELL _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13
    _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4
    _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL _WS)
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: wordStackMap _WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := executionEnv_map lhs symState,
    substate := substate_map _Gen15 symState.substate
    returnData := _Gen9.val
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    } := by aesop

theorem mload_poststate_equiv
  {PC_CELL _Val15 _Val16 _Val23 _Val24 : SortInt}
  {LOCALMEM_CELL : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
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
  {_WS : SortWordStack}
  (defn_Val16 : «_+Int_» PC_CELL 1 = some _Val16)
  (symState : EVM.State):
  let rhs :=
  (@mloadRHS _Val15 _Val16 _Val23 _Val24 LOCALMEM_CELL SCHEDULE_CELL _DotVar0
    _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16
    _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7
    _Gen8 _Gen9 _K_CELL _WS)
  stateMap symState rhs =
  {symState with
    stack := intMap _Val15 :: wordStackMap _WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val23
    executionEnv := executionEnv_map rhs symState,
    substate := substate_map _Gen15 symState.substate
    returnData := _Gen9.val
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    } := by cases _Gen15;  aesop (add simp [«_+Int_»])

/--
Theorem stating that `asWord (#range LM W0 32) = LM.lookupMemory W0`

`MachineState.lookupMemory` is `simp`ed to abstract the rest of the `MachineState`
-/
theorem range_lookupMemory_eq
  {LOCALMEM_CELL _Val14 : SortBytes}
  {W0 MEMORYUSED_CELL _Val15: SortInt}
  (defn_Val14 : «#range» LOCALMEM_CELL W0 32 = some _Val14)
  (defn_Val15 : asWord _Val14 = some _Val15)
  (W0ge0 : 0 ≤ W0)
  (W0small : W0 < UInt256.size)
  :
  (if ByteArray.size LOCALMEM_CELL ≤ (intMap W0).toNat ∨ intMap MEMORYUSED_CELL * { val := 32 } ≤ intMap W0 then
    { val := 0 }
  else UInt256.ofNat (fromByteArrayBigEndian (ByteArray.readWithPadding LOCALMEM_CELL (intMap W0).toNat 32))) =
  intMap _Val15 := by
  have dupl := defn_Val14; revert dupl
  simp [range_rw, «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  simp [«padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int»]
  split; linarith; split
  case isFalse.isFalse =>
    rename_i lth fls; rw [not_and] at fls
    have : ByteArray.size LOCALMEM_CELL ≤ (intMap W0).toNat := by
      rw [not_lt] at lth; apply fls at lth; rw [not_lt] at lth
      rw [intMap_toNat] <;> aesop
    simp; intro defn_Val14; simp [←defn_Val14, asWord_empty] at defn_Val15
    aesop
  split; aesop; simp; intro _
  have : ByteArray.size LOCALMEM_CELL - LOCALMEM_CELL.data.size = 0 := by
    simp [ByteArray.size]
  simp [this]
  split
  case isFalse.isTrue.isFalse.isTrue =>
    rename_i a b; rcases b with b|b
    . have : (ByteArray.size LOCALMEM_CELL - Int.toNat W0) = 0 := by
        rw [intMap_toNat] at b <;> aesop
      simp [ByteArray.extract, this, ByteArray.copySlice]
      have : (Int.toNat W0) ⊓ LOCALMEM_CELL.data.size ≤ (Int.toNat W0) := by omega
      rw [←Array.extract_eq_empty_iff] at this
      rw [this, ←ByteArray.mkEmpty, ←ByteArray.empty]
      intro defn_Val14; simp [←defn_Val14, asWord_empty] at defn_Val15
      aesop
    . /- This is the case where the following hipothesys
        `b : intMap MEMORYUSED_CELL * { val := 32 } ≤ intMap W0`
        has to imply that the following `#range(LM, INDEX, 32)` is empty.
        This is intuitively correct, but it doesn't appear to be reflected
        in the KEVM semantics.
        Further investigation is required in order to remove the `sorry`
       -/
      sorry
  revert defn_Val15
  simp [asWord, _ef5332a, Bytes2Int_fromByteArrayBigEndian_eq]
  have := @chop_self_eq
    LOCALMEM_CELL _Val14 W0 (fromByteArrayBigEndian _Val14) defn_Val14
    (Bytes2Int_fromByteArrayBigEndian_eq _Val14)
  rw [this]; simp; intro a b; rw [←b] at a; rw [←a]
  rw [←Int.ofNat_eq_coe]; conv => rhs; simp only [intMap, UInt256.toSigned]
  congr
  simp [ByteArray.readWithPadding, Axioms.ffi_zeroes]
  rename_i c; simp [not_and, not_le] at c; rcases c with ⟨c1, c2⟩
  simp [ByteArray.readWithoutPadding]
  split; omega
  simp [ByteArray.extract, ByteArray.copySlice]
  rw [intMap_toNat] at c1 <;> try assumption
  rw [Nat.add_sub_of_le]
  /- How to proceed:
  Hypotheses `b` and `defn_Val14` tell us that `LM.size - W0 = 32`
  Hence,`w0 + 32 ⊓ LM.size = LM.size`
  Ithshould then be shown that the `mkArray` equals the empty array
   -/
  sorry
  . aesop

theorem EVM.step_mload_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 _Val0 _Val1 _Val10 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
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
  {_WS : SortWordStack}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : «#range» LOCALMEM_CELL W0 32 = some _Val14)
  (defn_Val15 : asWord _Val14 = some _Val15)
  (defn_Val16 : «_+Int_» PC_CELL 1 = some _Val16)
  (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
  (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
  (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
  (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
  (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
  (defn_Val23 : «_-Int_» _Val21 _Val22 = some _Val23)
  (defn_Val24 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val24)
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
  (W0small : W0 < UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL)
  (mucsmall : MEMORYUSED_CELL < UInt256.size)
  -- As per the YP:
  -- "Due to [the fee shceme] it is highly unlikely [memory] addresses will ever go above 32-bit bounds"
  -- It seems we need this hypothesis to achieve equivalence of behavior from the EVMYul side
  -- We keep the original `W0small` for convenience
  (W0small_realpolitik : W0 < UInt32.size) :
  let lhs :=
  (@mloadLHS GAS_CELL MEMORYUSED_CELL PC_CELL W0 LOCALMEM_CELL SCHEDULE_CELL
    USEGAS_CELL _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13
    _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4
    _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL _WS)
  let rhs :=
  (@mloadRHS _Val15 _Val16 _Val23 _Val24 LOCALMEM_CELL SCHEDULE_CELL _DotVar0
    _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16
    _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7
    _Gen8 _Gen9 _K_CELL _WS)
EVM.step_mload (Int.toNat GAS_CELL) gasCost (stateMap symState lhs) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} rhs)
  := by
  intro lhs rhs; unfold lhs rhs
  cases cg: (Int.toNat GAS_CELL)
  next =>
    rw [Int.toNat_eq_zero] at cg
    have _ := Int.lt_of_lt_of_le gavailEnough cg; contradiction
  cases _Gen15; rw [mload_prestate_equiv]; simp [mloadLHS]
  rw [←EVM.step_mload, EVM.step_mload_summary] <;> first | assumption | try simp
  rw [mload_poststate_equiv, mloadRHS] <;> first | assumption | try simp
  simp [MachineState.lookupMemory, /- activeWords_comp -//- , mstore_memory_write -/]
  constructor <;> constructor <;> try constructor
  . sorry -- Gas goals are for now unproven
  . have := MstoreOpcodeEquivalence.activeWords_eq .mstore defn_Val24
    rw [MloadSummary.activeWords_comp]; aesop
  . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
  . apply range_lookupMemory_eq defn_Val14 defn_Val15 <;> aesop


theorem X_mload_equiv
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 _Val0 _Val1 _Val10 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {LOCALMEM_CELL _Val14 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
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
  {_WS : SortWordStack}
  (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val0)
  (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
  (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
  (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val6)
  (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
  (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
  (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
  (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
  (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
  (defn_Val14 : «#range» LOCALMEM_CELL W0 32 = some _Val14)
  (defn_Val15 : asWord _Val14 = some _Val15)
  (defn_Val16 : «_+Int_» PC_CELL 1 = some _Val16)
  (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
  (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
  (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
  (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
  (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
  (defn_Val23 : «_-Int_» _Val21 _Val22 = some _Val23)
  (defn_Val24 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val24)
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
  (W0small : W0 < UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL)
  (mucsmall : MEMORYUSED_CELL < UInt256.size)
  (codeMstore : _Gen0 = ⟨⟨#[(0x51 : UInt8)]⟩⟩)
  (pcZero : PC_CELL = 0)
  -- TODO: Replace with a native measure for `SortWordStack` and
  -- prove this assumption via an equality theorem stating that
  -- `List.length (wordStackMap WS) = wordStackLength WS`
  (stackOk: List.length (wordStackMap _WS) < 1024)
  -- As per the YP:
  -- "Due to [the fee shceme] it is highly unlikely [memory] addresses will ever go above 32-bit bounds"
  -- It seems we need this hypothesis to achieve equivalence of behavior from the EVMYul side
  -- We keep the original `W0small` for convenience
  (W0small_realpolitik : W0 < UInt32.size) :
  let lhs :=
  (@mloadLHS GAS_CELL MEMORYUSED_CELL PC_CELL W0 LOCALMEM_CELL SCHEDULE_CELL
    USEGAS_CELL _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13
    _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4
    _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL _WS)
  let rhs :=
  (@mloadRHS _Val15 _Val16 _Val23 _Val24 LOCALMEM_CELL SCHEDULE_CELL _DotVar0
    _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16
    _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7
    _Gen8 ⟨.empty⟩ _K_CELL _WS)
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState lhs) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} rhs) .empty)
  := by
  intro lhs rhs; unfold lhs rhs
  cases cg: (Int.toNat GAS_CELL)
  next =>
    rw [Int.toNat_eq_zero] at cg
    have _ := Int.lt_of_lt_of_le gavailEnough cg; contradiction
  rw [pcZero, codeMstore, mload_prestate_equiv, mload_poststate_equiv]
  <;> try assumption
  cases _Gen15 with
  | mk selfDestruct log refund accessedAccounts accessedStorage createdAccounts =>
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  simp [mloadLHS, mloadRHS]; rw [pc_equiv, X_mload_summary] <;> try assumption
  . simp; constructor <;> try constructor <;> try constructor
    . -- The deducted amount of gas coincides
      sorry
    . have := MstoreOpcodeEquivalence.activeWords_eq .mstore defn_Val24
      rw [MloadSummary.activeWords_comp]; aesop
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . simp [MachineState.lookupMemory]
      apply range_lookupMemory_eq defn_Val14 defn_Val15 <;> aesop
  . -- There is enough gas
    sorry
  . -- Gas doesn't overflow
    sorry



end MloadOpcodeEquivalence
