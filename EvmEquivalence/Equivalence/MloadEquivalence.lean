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
      rw [this]
      have : { data := #[] } = ByteArray.empty := rfl
      rw [this]
      intro defn_Val14; simp [←defn_Val14, asWord_empty] at defn_Val15
      aesop (add simp [asWord])
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
  rename_i c; simp [not_le] at c; rcases c with ⟨c1, c2⟩
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

/-! ## Private helpers for KEVM `Cmem` ↔ EVM `Cₘ` gas correspondence (MLOAD, width = 32) -/

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

private theorem memUsageUpdate_nonneg
  {MEMORYUSED_CELL W0 _Val : SortInt}
  (defn_Val : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) :
  0 ≤ _Val := by
  rw [memoryUsageUpdate_rw _ _ _ (by omega : (0 : Int) < 32), Option.some.injEq] at defn_Val
  subst defn_Val
  exact le_sup_of_le_left mucge0

private theorem memUsageUpdate_small
  {MEMORYUSED_CELL W0 _Val : SortInt}
  (defn_Val : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val)
  (W0ge0 : 0 ≤ W0)
  (mucsmall : MEMORYUSED_CELL < ↑UInt256.size)
  (W0small_realpolitik : W0 < ↑UInt32.size) :
  _Val < ↑UInt256.size := by
  rw [memoryUsageUpdate_rw _ _ _ (by omega : (0 : Int) < 32), Option.some.injEq] at defn_Val
  subst defn_Val
  have hsum_nonneg : 0 ≤ W0 + 32 + 31 := by linarith
  have hceil_le : Int.tdiv (W0 + 32 + 31) 32 ≤ W0 + 32 + 31 :=
    Int.tdiv_le_self 32 hsum_nonneg
  have hsum_bound : W0 + 32 + 31 < ↑UInt256.size := by
    have : (UInt256.size : ℤ) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
      simp [UInt256.size]
    have : (UInt32.size : ℤ) = 4294967296 := by simp [UInt32.size]
    linarith
  exact max_lt mucsmall (lt_of_le_of_lt hceil_le hsum_bound)

private theorem Cm_mono (a b : UInt256) (h : a.toNat ≤ b.toNat) :
    EVM.Cₘ a ≤ EVM.Cₘ b := by
  simp [EVM.Cₘ, EVM.Cₘ.QuadraticCeofficient]
  have h1 : GasConstants.Gmemory * a.toNat ≤ GasConstants.Gmemory * b.toNat :=
    Nat.mul_le_mul_left _ h
  have h2 : a.toNat * a.toNat / 512 ≤ b.toNat * b.toNat / 512 :=
    Nat.div_le_div_right (Nat.mul_le_mul h h)
  omega

/-- For MLOAD, `MachineState.M` (computing active words) equals `intMap _Val` where
    `_Val` comes from `#memoryUsageUpdate`. -/
private theorem vawg_eq_intMap_mload
  {MEMORYUSED_CELL W0 _Val : SortInt}
  (defn_Val : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val)
  (W0ge0 : 0 ≤ W0) (W0small : W0 < ↑UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) (mucsmall : MEMORYUSED_CELL < ↑UInt256.size) :
  UInt256.ofNat (MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat 32) = intMap _Val := by
  have aw := MstoreOpcodeEquivalence.activeWords_eq .mstore defn_Val W0ge0 W0small mucge0 mucsmall
  simp only [MstoreSummary.activeWords_comp] at aw
  exact aw

/-- Proves the gas correctness goal in `X_mload_equiv`: the KEVM gas chain
    (Cmem subtractions via `_-Int_`) equals the EVM `memoryExpansionCost` (via `Cₘ`). -/
private theorem gas_cost_X_mload_equiv
  {GAS_CELL MEMORYUSED_CELL W0 _Val17 _Val18 _Val19 _Val20 _Val21 _Val22 _Val23 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
  (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
  (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
  (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
  (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
  (defn_Val23 : «_-Int_» _Val21 _Val22 = some _Val23)
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0) (W0small : W0 < ↑UInt256.size)
  (mucge0 : 0 ≤ MEMORYUSED_CELL) (mucsmall : MEMORYUSED_CELL < ↑UInt256.size)
  (W0small_realpolitik : W0 < ↑UInt32.size)
  (hmec_le_gas : _Val20 ≤ GAS_CELL)
  (hgvl_le : _Val22 ≤ GAS_CELL - _Val20) :
  intMap GAS_CELL -
    UInt256.ofNat (EVM.Cₘ (UInt256.ofNat (MachineState.M (intMap MEMORYUSED_CELL).toNat (intMap W0).toNat 32)) -
                   EVM.Cₘ (intMap MEMORYUSED_CELL)) -
    UInt256.ofNat GasConstants.Gverylow = intMap _Val23 := by
  have eq20 : _Val18 - _Val19 = _Val20 := by simp [«_-Int_»] at defn_Val20; exact defn_Val20
  have eq21 : GAS_CELL - _Val20 = _Val21 := by simp [«_-Int_»] at defn_Val21; exact defn_Val21
  have eq23 : _Val21 - _Val22 = _Val23 := by simp [«_-Int_»] at defn_Val23; exact defn_Val23
  have eq22 : _Val22 = 3 := by
    rw [cancun] at defn_Val22; simp [GasInterface.cancun_def] at defn_Val22; exact defn_Val22.symm
  have h17_nn := memUsageUpdate_nonneg defn_Val17 mucge0
  have h17_sm := memUsageUpdate_small defn_Val17 W0ge0 mucsmall W0small_realpolitik
  have eq18 : _Val18 = ↑(EVM.Cₘ (intMap _Val17)) := by
    have := Cmem_cancun_eq_Cm _Val17 h17_nn h17_sm
    rw [cancun] at defn_Val18; rw [this] at defn_Val18
    exact (Option.some.inj defn_Val18).symm
  have eq19 : _Val19 = ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) := by
    have := Cmem_cancun_eq_Cm MEMORYUSED_CELL mucge0 mucsmall
    rw [cancun] at defn_Val19; rw [this] at defn_Val19
    exact (Option.some.inj defn_Val19).symm
  rw [vawg_eq_intMap_mload defn_Val17 W0ge0 W0small mucge0 mucsmall]
  have hCm_le : EVM.Cₘ (intMap MEMORYUSED_CELL) ≤ EVM.Cₘ (intMap _Val17) := by
    apply Cm_mono
    rw [intMap_toNat mucge0 mucsmall, intMap_toNat h17_nn h17_sm]
    have defn17' := defn_Val17
    rw [memoryUsageUpdate_rw _ _ _ (by omega : (0 : Int) < 32)] at defn17'
    have eq17 : _Val17 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + 32 + 31) 32 :=
      (Option.some.inj defn17').symm
    rw [eq17]
    exact Int.toNat_le_toNat (le_max_left _ _)
  have hv23 : _Val23 = GAS_CELL - (↑(EVM.Cₘ (intMap _Val17)) - ↑(EVM.Cₘ (intMap MEMORYUSED_CELL))) - 3 := by
    rw [← eq23, ← eq21, ← eq20, eq18, eq19, eq22]
  rw [hv23]
  set cm17 := EVM.Cₘ (intMap _Val17) with hcm17_def
  set cmmu := EVM.Cₘ (intMap MEMORYUSED_CELL) with hcmmu_def
  have hcast : (↑cm17 : SortInt) - ↑cmmu = ↑(cm17 - cmmu) := (Nat.cast_sub hCm_le).symm
  rw [hcast]
  simp only [GasConstants.Gverylow]
  have hmec_le : (↑(cm17 - cmmu) : SortInt) ≤ GAS_CELL := by
    rw [← hcast, ← eq18, ← eq19, eq20]; exact hmec_le_gas
  have h3_le : (3 : SortInt) ≤ GAS_CELL - ↑(cm17 - cmmu) := by
    rw [← hcast, ← eq18, ← eq19, eq20, ← eq22]; exact hgvl_le
  rw [intMap_sub_dist h3_le (by norm_num) (by linarith)]
  rw [intMap_sub_dist hmec_le (Int.natCast_nonneg _) gavailSmall]
  simp [intMap, UInt256.toSigned]

/-- Derives the memory expansion cost inequality `_Val20 ≤ GAS_CELL` and
    the Gverylow inequality `_Val22 ≤ GAS_CELL - _Val20` from the KEVM `req` flag. -/
private theorem gas_bounds_from_req
  {GAS_CELL MEMORYUSED_CELL W0 _Val0 _Val1 _Val10 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
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
  (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
  (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
  (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
  (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
  (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
  (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
  (req : _Val13 = true)
  (_cancun : SCHEDULE_CELL = .CANCUN_EVM) :
  _Val20 ≤ GAS_CELL ∧ _Val22 ≤ GAS_CELL - _Val20 := by
  have hbool13 : USEGAS_CELL = true ∧ _Val12 = true := by
    have h := defn_Val13; simp [andBool_def] at h; rw [← h] at req; exact Bool.and_eq_true_iff.mp req
  have hbool12 : _Val4 = true ∧ _Val11 = true := by
    have h := defn_Val12; simp [andBool_def] at h; rw [← h] at hbool13; exact Bool.and_eq_true_iff.mp hbool13.2
  have eq_0_17 : _Val0 = _Val17 := Option.some.inj (defn_Val0.symm.trans defn_Val17)
  have eq_1_18 : _Val1 = _Val18 := by
    have h := defn_Val1; rw [eq_0_17] at h; exact Option.some.inj (h.symm.trans defn_Val18)
  have eq_2_19 : _Val2 = _Val19 := Option.some.inj (defn_Val2.symm.trans defn_Val19)
  have eq_3_20 : _Val3 = _Val20 := by
    have h3 := defn_Val3; have h20 := defn_Val20
    simp [«_-Int_»] at h3 h20; rw [← h3, ← h20, eq_1_18, eq_2_19]
  have eq_6_17 : _Val6 = _Val17 := Option.some.inj (defn_Val6.symm.trans defn_Val17)
  have eq_7_18 : _Val7 = _Val18 := by
    have h := defn_Val7; rw [eq_6_17] at h; exact Option.some.inj (h.symm.trans defn_Val18)
  have eq_8_19 : _Val8 = _Val19 := Option.some.inj (defn_Val8.symm.trans defn_Val19)
  have eq_9_20 : _Val9 = _Val20 := by
    have h9 := defn_Val9; have h20 := defn_Val20
    simp [«_-Int_»] at h9 h20; rw [← h9, ← h20, eq_7_18, eq_8_19]
  have eq_5_22 : _Val5 = _Val22 := Option.some.inj (defn_Val5.symm.trans defn_Val22)
  have eq_10_21 : _Val10 = _Val21 := by
    have h10 := defn_Val10; have h21 := defn_Val21
    simp [«_-Int_»] at h10 h21; rw [← h10, ← h21, eq_9_20]
  have hmec_le_gas : _Val3 ≤ GAS_CELL := by
    simp [«_<=Int_»] at defn_Val4; rw [← defn_Val4] at hbool12
    exact of_decide_eq_true hbool12.1
  have hgvl_le : _Val5 ≤ _Val10 := by
    simp [«_<=Int_»] at defn_Val11; rw [← defn_Val11] at hbool12
    exact of_decide_eq_true hbool12.2
  constructor
  · rw [eq_3_20] at hmec_le_gas; exact hmec_le_gas
  · rw [← eq_5_22]
    rw [eq_10_21] at hgvl_le
    have h21 : _Val21 = GAS_CELL - _Val20 := by
      simp [«_-Int_»] at defn_Val21; exact defn_Val21.symm
    linarith

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
  -- Following the pattern in step_sstore_equiv: constrain gasCost to its KEVM value
  (gasCostValue : gasCost = Int.toNat (_Val20 + _Val22))
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
  . -- Gas goal: intMap GAS_CELL - UInt256.ofNat gasCost = intMap _Val23
    -- Use gasCostValue and the KEVM chain to discharge
    rw [gasCostValue]
    -- Extract concrete values from the KEVM chain
    have eq20 : _Val18 - _Val19 = _Val20 := by simp [«_-Int_»] at defn_Val20; exact defn_Val20
    have eq21 : GAS_CELL - _Val20 = _Val21 := by simp [«_-Int_»] at defn_Val21; exact defn_Val21
    have eq23 : _Val21 - _Val22 = _Val23 := by simp [«_-Int_»] at defn_Val23; exact defn_Val23
    have eq22_val : _Val22 = 3 := by
      rw [cancun] at defn_Val22; simp [GasInterface.cancun_def] at defn_Val22; exact defn_Val22.symm
    -- Connect Cmem to Cₘ via Cmem_cancun_eq_Cm (reusing mstore infrastructure)
    have h17_nn := MstoreOpcodeEquivalence.memUsageUpdate_nonneg_pub .mstore defn_Val17 mucge0
    have h17_sm := MstoreOpcodeEquivalence.memUsageUpdate_small_pub .mstore defn_Val17 W0ge0 mucsmall W0small_realpolitik
    have eq18 : _Val18 = ↑(EVM.Cₘ (intMap _Val17)) := by
      have := MstoreOpcodeEquivalence.Cmem_cancun_eq_Cm_pub _Val17 h17_nn h17_sm
      rw [cancun] at defn_Val18; rw [this] at defn_Val18
      exact (Option.some.inj defn_Val18).symm
    have eq19 : _Val19 = ↑(EVM.Cₘ (intMap MEMORYUSED_CELL)) := by
      have := MstoreOpcodeEquivalence.Cmem_cancun_eq_Cm_pub MEMORYUSED_CELL mucge0 mucsmall
      rw [cancun] at defn_Val19; rw [this] at defn_Val19
      exact (Option.some.inj defn_Val19).symm
    -- Cₘ monotonicity
    have hCm_le : EVM.Cₘ (intMap MEMORYUSED_CELL) ≤ EVM.Cₘ (intMap _Val17) := by
      apply MstoreOpcodeEquivalence.mec_Cm_mono_pub
      rw [intMap_toNat mucge0 mucsmall, intMap_toNat h17_nn h17_sm]
      have defn17' := defn_Val17
      rw [memoryUsageUpdate_rw _ _ _ (by norm_num : (0 : SortInt) < 32)] at defn17'
      have eq17 : _Val17 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + 32 + 31) 32 :=
        (Option.some.inj defn17').symm
      rw [eq17]
      exact Int.toNat_le_toNat (le_max_left _ _)
    -- 0 ≤ _Val20 (Cmem is monotone)
    have h20_nn : 0 ≤ _Val20 := by
      rw [← eq20, eq18, eq19]; exact sub_nonneg.mpr (Nat.cast_le.mpr hCm_le)
    have h22_nn : 0 ≤ _Val22 := by linarith
    -- _Val23 = GAS_CELL - (_Val20 + _Val22)
    have hv23 : _Val23 = GAS_CELL - (_Val20 + _Val22) := by linarith
    rw [hv23]
    -- Derive bounds from req
    have hbool13 : USEGAS_CELL = true ∧ _Val12 = true := by
      have h := defn_Val13; simp [andBool_def] at h; rw [← h] at req; exact Bool.and_eq_true_iff.mp req
    have hbool12 : _Val4 = true ∧ _Val11 = true := by
      have h := defn_Val12; simp [andBool_def] at h; rw [← h] at hbool13; exact Bool.and_eq_true_iff.mp hbool13.2
    have h_val3_le : _Val3 ≤ GAS_CELL := by
      have h := defn_Val4; simp [«_<=Int_»] at h; rw [← h] at hbool12; exact of_decide_eq_true hbool12.1
    have eq_0_17 : _Val0 = _Val17 := Option.some.inj (defn_Val0.symm.trans defn_Val17)
    have eq_1_18 : _Val1 = _Val18 := by
      have h := defn_Val1; rw [eq_0_17] at h; exact Option.some.inj (h.symm.trans defn_Val18)
    have eq_2_19 : _Val2 = _Val19 := Option.some.inj (defn_Val2.symm.trans defn_Val19)
    have eq_3_20 : _Val3 = _Val20 := by
      have h3 := defn_Val3; have h20 := defn_Val20
      simp [«_-Int_»] at h3 h20; linarith
    have hmec_le_gas : _Val20 ≤ GAS_CELL := by linarith
    have h_val5_le_val10 : _Val5 ≤ _Val10 := by
      have h := defn_Val11; simp [«_<=Int_»] at h; rw [← h] at hbool12; exact of_decide_eq_true hbool12.2
    have eq_5_22 : _Val5 = _Val22 := Option.some.inj (defn_Val5.symm.trans defn_Val22)
    have eq_6_17 : _Val6 = _Val17 := Option.some.inj (defn_Val6.symm.trans defn_Val17)
    have eq_7_18 : _Val7 = _Val18 := by
      have h := defn_Val7; rw [eq_6_17] at h; exact Option.some.inj (h.symm.trans defn_Val18)
    have eq_8_19 : _Val8 = _Val19 := Option.some.inj (defn_Val8.symm.trans defn_Val19)
    have eq_9_20 : _Val9 = _Val20 := by
      have h9 := defn_Val9; have h20 := defn_Val20
      simp [«_-Int_»] at h9 h20; linarith
    have eq_10_21 : _Val10 = _Val21 := by
      have h10 := defn_Val10; have h21 := defn_Val21
      simp [«_-Int_»] at h10 h21; linarith
    have hgvl_le : _Val22 ≤ GAS_CELL - _Val20 := by
      rw [eq_5_22] at h_val5_le_val10; rw [eq_10_21] at h_val5_le_val10; linarith
    have hsum_nn : 0 ≤ _Val20 + _Val22 := by linarith
    have hsum_le : _Val20 + _Val22 ≤ GAS_CELL := by linarith
    have ofNat_eq : UInt256.ofNat (Int.toNat (_Val20 + _Val22)) = intMap (_Val20 + _Val22) := by
      simp [intMap, UInt256.toSigned]
      cases h : (_Val20 + _Val22) with
      | ofNat n => rfl
      | negSucc n => rw [h] at hsum_nn; simp at hsum_nn
    rw [ofNat_eq, intMap_sub_dist hsum_le hsum_nn gavailSmall]
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
      -- Use the gas_cost_X_mload_equiv helper with bounds extracted from `req`.
      have ⟨hmec, hgvl⟩ := gas_bounds_from_req defn_Val0 defn_Val1 defn_Val2 defn_Val3 defn_Val4
        defn_Val5 defn_Val6 defn_Val7 defn_Val8 defn_Val9 defn_Val10 defn_Val11 defn_Val12 defn_Val13
        defn_Val17 defn_Val18 defn_Val19 defn_Val20 defn_Val21 defn_Val22 req cancun
      exact gas_cost_X_mload_equiv defn_Val17 defn_Val18 defn_Val19 defn_Val20 defn_Val21 defn_Val22
        defn_Val23 cancun gavailSmall W0ge0 W0small mucge0 mucsmall W0small_realpolitik hmec hgvl
    . have := MstoreOpcodeEquivalence.activeWords_eq .mstore defn_Val24
      rw [MloadSummary.activeWords_comp]; aesop
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . simp [MachineState.lookupMemory]
      apply range_lookupMemory_eq defn_Val14 defn_Val15 <;> aesop
  . -- There is enough gas
    -- X_mload_summary now requires `3 ≤` (non-strict), matching the KEVM hypothesis.
    -- Extract the KEVM gas sufficiency inequality from `req`
    have h13 : _Val13 = (USEGAS_CELL && _Val12) := by
      simp [andBool_def] at defn_Val13; exact defn_Val13.symm
    rw [h13] at req
    have huse : USEGAS_CELL = true := by cases USEGAS_CELL <;> simp_all
    have h12t : _Val12 = true := by cases USEGAS_CELL <;> cases _Val12 <;> simp_all
    have h12 : _Val12 = (_Val4 && _Val11) := by
      simp [andBool_def] at defn_Val12; exact defn_Val12.symm
    rw [h12] at h12t
    have h4t : _Val4 = true := by cases _Val4 <;> simp_all
    have h11t : _Val11 = true := by cases _Val4 <;> cases _Val11 <;> simp_all
    have hv5 : _Val5 = 3 := by
      rw [cancun] at defn_Val5; simp [GasInterface.cancun_def] at defn_Val5; exact defn_Val5.symm
    have hv10 : _Val10 = GAS_CELL - _Val9 := by
      simp [«_-Int_»] at defn_Val10; exact defn_Val10.symm
    have hleq : _Val5 ≤ _Val10 := by
      simp [«_<=Int_»] at defn_Val11
      rw [← defn_Val11] at h11t
      exact decide_eq_true_eq.mp h11t
    rw [hv5, hv10] at hleq
    have hv9 : _Val9 = _Val7 - _Val8 := by
      simp [«_-Int_»] at defn_Val9; exact defn_Val9.symm
    rw [hv9] at hleq
    have hv3_le_gas : _Val3 ≤ GAS_CELL := by
      simp [«_<=Int_»] at defn_Val4
      rw [← defn_Val4] at h4t
      exact decide_eq_true_eq.mp h4t
    have hv3_eq : _Val3 = _Val1 - _Val2 := by
      simp [«_-Int_»] at defn_Val3; exact defn_Val3.symm
    -- _Val1 = _Val7, _Val2 = _Val8 because they compute the same Cmem on the same args
    have hv0 : _Val0 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + 32 + 31) 32 := by
      have := memoryUsageUpdate_rw MEMORYUSED_CELL W0 32 (by omega : (0 : Int) < 32)
      rw [this] at defn_Val0; simp at defn_Val0; exact defn_Val0.symm
    have hv6 : _Val6 = MEMORYUSED_CELL ⊔ Int.tdiv (W0 + 32 + 31) 32 := by
      have := memoryUsageUpdate_rw MEMORYUSED_CELL W0 32 (by omega : (0 : Int) < 32)
      rw [this] at defn_Val6; simp at defn_Val6; exact defn_Val6.symm
    have hv0_eq_v6 : _Val0 = _Val6 := by rw [hv0, hv6]
    have hv1_eq_v7 : _Val1 = _Val7 := by
      have h1 : Cmem SCHEDULE_CELL _Val0 = some _Val1 := defn_Val1
      have h7 : Cmem SCHEDULE_CELL _Val6 = some _Val7 := defn_Val7
      rw [hv0_eq_v6] at h1; rw [h1] at h7; simp at h7; exact h7
    have hv2_eq_v8 : _Val2 = _Val8 := by
      have h2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2 := defn_Val2
      have h8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8 := defn_Val8
      rw [h2] at h8; simp at h8; exact h8
    have hv3_eq_v9 : _Val3 = _Val7 - _Val8 := by
      rw [hv3_eq, hv1_eq_v7, hv2_eq_v8]
    rw [hv3_eq_v9] at hv3_le_gas
    rw [GasConstants.Gverylow]
    have hgas_nat : (intMap GAS_CELL).toNat = Int.toNat GAS_CELL :=
      intMap_toNat (le_of_lt gavailEnough) gavailSmall
    rw [hgas_nat]
    simp only [EVM.memoryExpansionCost, EVM.memoryExpansionCost.μᵢ', EVM.Cₘ,
               EVM.Cₘ.QuadraticCeofficient, GasConstants.Gmemory, MachineState.M]
    have hstack0 : (intMap W0 :: wordStackMap _WS)[0]!.toNat = (intMap W0).toNat := rfl
    simp only [hstack0]
    set aw := (intMap MEMORYUSED_CELL).toNat with haw_def
    set w0 := (intMap W0).toNat with hw0_def
    set m := max aw ((w0 + 32 + 31) / 32) with hm_def
    have hm_bound : m < UInt256.size := by
      simp only [hm_def, Nat.max_def]; split
      · have hw0_small : w0 < UInt32.size := by
          rw [hw0_def, intMap_toNat W0ge0 W0small]
          exact (Int.toNat_lt W0ge0).mpr W0small_realpolitik
        simp [UInt32.size, UInt256.size] at hw0_small ⊢; omega
      · exact (intMap MEMORYUSED_CELL).val.isLt
    rw [UInt256.ofNat_toNat hm_bound]
    have cmem_cancun : ∀ n : SortInt, Cmem .CANCUN_EVM n = some (n * 3 + Int.tdiv (n * n) 512) := by
      intro n; simp only [Cmem, GAS_FEES_Cmem]
      simp only [GasInterface.cancun_def, «_*Int_», «_/Int_», «_+Int_»]; simp
    rw [cancun] at defn_Val7 defn_Val8
    rw [cmem_cancun] at defn_Val7 defn_Val8
    simp only [Option.some.injEq] at defn_Val7 defn_Val8
    have haw_int : aw = Int.toNat MEMORYUSED_CELL := by
      rw [haw_def, intMap_toNat mucge0 mucsmall]
    have hw0_int : w0 = Int.toNat W0 := by
      rw [hw0_def, intMap_toNat W0ge0 W0small]
    have hv6_ge_muc : MEMORYUSED_CELL ≤ _Val6 := by rw [hv6]; exact le_max_left _ _
    have hv6_nonneg : 0 ≤ _Val6 := le_trans mucge0 hv6_ge_muc
    have hm_ge_aw : aw ≤ m := le_max_left _ _
    have evm_cost_sub_ok : 3 * aw + aw * aw / 512 ≤ 3 * m + m * m / 512 := by
      have : aw * aw / 512 ≤ m * m / 512 := Nat.div_le_div_right (Nat.mul_le_mul hm_ge_aw hm_ge_aw)
      omega
    have hm_eq_v6 : (m : ℤ) = _Val6 := by
      rw [hm_def, hv6, haw_int, hw0_int]
      simp only [Nat.cast_max, Int.natCast_div, Int.toNat_of_nonneg mucge0]
      congr 1
      rw [show ((Int.toNat W0 + 32 + 31 : ℕ) : ℤ) = W0 + 32 + 31 from by push_cast; rw [Int.toNat_of_nonneg W0ge0]]
      rw [Int.tdiv_eq_ediv_of_nonneg (by linarith : 0 ≤ W0 + 32 + 31)]; norm_cast
    have haw_eq : (aw : ℤ) = MEMORYUSED_CELL := by
      rw [haw_int]; exact Int.toNat_of_nonneg mucge0
    have hcm_m : (↑(3 * m + m * m / 512) : ℤ) = _Val7 := by
      push_cast [Int.natCast_div]
      rw [hm_eq_v6, ← defn_Val7]
      rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg _Val6)]
      ring
    have hcm_aw : (↑(3 * aw + aw * aw / 512) : ℤ) = _Val8 := by
      push_cast [Int.natCast_div]
      rw [haw_eq, ← defn_Val8]
      rw [Int.tdiv_eq_ediv_of_nonneg (mul_self_nonneg MEMORYUSED_CELL)]
      ring
    have evm_cost_int : ↑(3 * m + m * m / 512 - (3 * aw + aw * aw / 512)) = _Val7 - _Val8 := by
      rw [Nat.cast_sub evm_cost_sub_ok, hcm_m, hcm_aw]
    have : (3 : ℤ) ≤ GAS_CELL - ↑(3 * m + m * m / 512 - (3 * aw + aw * aw / 512)) := by
      linarith [evm_cost_int]
    omega
  . -- Gas doesn't overflow
    simp only [EVM.memoryExpansionCost, EVM.Cₘ, EVM.memoryExpansionCost.μᵢ', MachineState.M]
    simp only [GasConstants.Gmemory, EVM.Cₘ.QuadraticCeofficient, UInt256.size]
    have hw0 : (intMap W0).toNat < UInt32.size := by
      rw [intMap_toNat W0ge0 W0small]; exact (Int.toNat_lt W0ge0).mpr W0small_realpolitik
    have haw : (intMap MEMORYUSED_CELL).toNat < UInt256.size := (intMap MEMORYUSED_CELL).val.isLt
    set aw := (intMap MEMORYUSED_CELL).toNat
    set w0 := (intMap W0).toNat
    set m := max aw ((w0 + 32 + 31) / 32)
    have hm_bound : m < UInt256.size := by
      simp only [m, Nat.max_def]; split
      · simp [UInt32.size, UInt256.size] at hw0 ⊢; omega
      · exact haw
    have hstack : (intMap W0 :: wordStackMap _WS)[0]!.toNat = w0 := by rfl
    rw [hstack]
    have : m = max aw ((w0 + 32 + 31) / 32) := rfl
    have hmu : (UInt256.ofNat m).toNat = m := UInt256.ofNat_toNat hm_bound
    rw [hmu]
    simp only [m, Nat.max_def] at hmu ⊢
    split
    · -- aw ≤ (w0+63)/32, so m = (w0+63)/32 which is small
      have hb : (w0 + 32 + 31) / 32 < 134217730 := by simp [UInt32.size] at hw0; omega
      apply Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      nlinarith [Nat.div_le_self ((w0 + 32 + 31) / 32 * ((w0 + 32 + 31) / 32)) 512]
    · -- aw > (w0+63)/32, so m = aw and Cm(m) - Cm(aw) = 0
      omega



end MloadOpcodeEquivalence
