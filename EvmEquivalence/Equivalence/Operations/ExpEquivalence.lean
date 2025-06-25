import EvmEquivalence.Summaries.StackOperationsSummary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace ExpOpcodeEquivalence

/--
We have two cases for the summaries: one where the exponent is 0,
and where the exponent is greater than 0
 -/
inductive exp_case where
  | gt0 -- exponent is greater than 0
  | eq0 -- exponent is 0

variable (ec : exp_case)

def expLHS
  {GAS_CELL PC_CELL W0 W1 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
    { kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.EXP_EVM_BinStackOp))) _K_CELL },
        exitCode := _Gen22,
        mode := _Gen23,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen11,
            statusCode := _Gen12,
            callStack := _Gen13,
            interimStates := _Gen14,
            touchedAccounts := _Gen15,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
              localMem := _Gen6,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := _Gen19,
            blockhashes := _Gen20,
            block := _Gen21 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }

def expRHS
  {_Val11 _Val12 _Val20 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := _K_CELL },
      exitCode := _Gen22,
      mode := _Gen23,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := true },
      ethereum := {
        evm := {
          output := _Gen11,
          statusCode := _Gen12,
          callStack := _Gen13,
          interimStates := _Gen14,
          touchedAccounts := _Gen15,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := _Gen2,
            caller := _Gen3,
            callData := _Gen4,
            callValue := _Gen5,
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val11 WS },
            localMem := _Gen6,
            pc := { val := _Val12 },
            gas := { val := (@inj SortInt SortGas) _Val20 },
            memoryUsed := _Gen7,
            callGas := _Gen8,
            static := _Gen9,
            callDepth := _Gen10 },
          versionedHashes := _Gen16,
          substate := _Gen17,
          gasPrice := _Gen18,
          origin := _Gen19,
          blockhashes := _Gen20,
          block := _Gen21 },
        network := _DotVar2 } },
    generatedCounter := _DotVar0 }

/-
Given that we're dealing with two summaries that have a different structure at once,
we have to differentiate which conditions change depending on the summary
-/

@[simp]
/- Note the implicit assumption that 0 ≤ W1 -/
def exp_case.to_defn_Val0 (W1 : SortInt) (_Val0 : SortBool) : Prop :=
  match ec with
  | gt0 => «_<Int_» 0 W1 = some _Val0
  | eq0 => «_<=Int_» W1 0 = some _Val0

@[simp]
def exp_case.to_defn_Val8 (GAS_CELL _Val1 _Val7 : SortInt) (_Val8 _Val2 : SortBool) : Prop :=
  match ec with
  | gt0 => «_<=Int_» _Val7 GAS_CELL = some _Val8
  | eq0 => «_<=Int_» _Val1 GAS_CELL = some _Val2

@[simp]
def exp_case.to_defn_Val9 (_Val0 _Val2 _Val3 _Val8 _Val9 : SortBool) : Prop :=
  match ec with
  | gt0 => _andBool_ _Val0 _Val8 = some _Val9
  | eq0 => _andBool_ _Val0 _Val2 = some _Val3

@[simp]
def exp_case.to_defn_Val10 (USEGAS_CELL _Val3 _Val4 _Val9 _Val10 : SortBool) : Prop :=
  match ec with
  | gt0 => _andBool_ USEGAS_CELL _Val9 = some _Val10
  | eq0 => _andBool_ USEGAS_CELL _Val3 = some _Val4

@[simp]
def exp_case.to_defn_Val20 (GAS_CELL _Val1 _Val19 _Val20 : SortInt) : Prop :=
  match ec with
  | gt0 => «_-Int_» GAS_CELL _Val19 = some _Val20
  | eq0 => «_-Int_» GAS_CELL _Val1 = some _Val20

@[simp]
def exp_case.to_req (_Val4 _Val10 : SortBool) : Prop :=
  match ec with
  | gt0 => _Val10 = true
  | eq0 => _Val4 = true

/--
We have three different kinds of hypotheses:

1. Hypotheses that apply to both summaries (e.g., `defn_Val1`)
2. Hypotheses that change depending on the summary (e.g., `defn_Val0`)
3. Hypotheses that only apply to the case `gt0` and are irrelevant for `eq0`
  (e.g., `defn_Val2` through `defn_Val7`)
-/
theorem rw_expLHS_expRHS
  {GAS_CELL PC_CELL W0 W1 _Val1 _Val11 _Val12 _Val13 _Val14 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val10 _Val8 _Val9 _Val2_eq _Val3_eq _Val4_eq : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK}
  (defn_Val0 : ec.to_defn_Val0 W1 _Val0)
  (defn_Val1 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val3)
  (defn_Val4 : «_/Int_» _Val3 8 = some _Val4)
  (defn_Val5 : «_+Int_» _Val4 1 = some _Val5)
  (defn_Val6 : «_*Int_» _Val2 _Val5 = some _Val6)
  (defn_Val7 : «_+Int_» _Val1 _Val6 = some _Val7)
  (defn_Val8 : ec.to_defn_Val8 GAS_CELL _Val1 _Val7 _Val8 _Val2_eq)
  (defn_Val9 : ec.to_defn_Val9 _Val0 _Val2_eq _Val3_eq _Val8 _Val9)
  (defn_Val10 : ec.to_defn_Val10 USEGAS_CELL _Val3_eq _Val4_eq _Val9 _Val10)
  (defn_Val11 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val11)
  (defn_Val12 : «_+Int_» PC_CELL 1 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val15)
  (defn_Val16 : «_/Int_» _Val15 8 = some _Val16)
  (defn_Val17 : «_+Int_» _Val16 1 = some _Val17)
  (defn_Val18 : «_*Int_» _Val14 _Val17 = some _Val18)
  (defn_Val19 : «_+Int_» _Val13 _Val18 = some _Val19)
  (defn_Val20 : ec.to_defn_Val20 GAS_CELL _Val13 _Val19 _Val20)
  (req : ec.to_req _Val4_eq _Val10) :
  Rewrites
  (@expLHS GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL USEGAS_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  (@expRHS _Val11 _Val12 _Val20 SCHEDULE_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL) := by
  cases ec <;> simp [expLHS, expRHS]
  . apply (@Rewrites.EXP_SUMMARY_EXP_SUMMARY_USEGAS GAS_CELL PC_CELL
  W0 W1 _Val1  _Val11 _Val12 _Val13 _Val14 _Val15 _Val16 _Val17
  _Val18 _Val19 _Val2 _Val20 _Val3 _Val4 _Val5 _Val6)
    all_goals assumption
  . apply (@Rewrites.EXP_SUMMARY_EXP_SUMMARY_USEGAS_LE0 GAS_CELL PC_CELL W0 W1 _Val1  _Val11 _Val12 _Val13 _Val20 SCHEDULE_CELL USEGAS_CELL _Val0 _Val2_eq _Val3_eq _Val4_eq WS)
    all_goals assumption

theorem exp_prestate_equiv
  {GAS_CELL PC_CELL W0 W1 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK}
  (symState : EVM.State):
  let lhs := (@expLHS GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: (intMap W1) :: wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := executionEnv_map lhs symState
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap lhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := rfl

/--
We should specify a reasoning friendly `exp` behavior
-/
opaque TODO.exp_representation : SortInt → SortInt → SortInt

theorem exp_poststate_equiv
  {PC_CELL W0 W1 _Val6 _Val11 _Val12 _Val20 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK}
  (defn_Val11 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val11)
  (defn_Val12 : «_+Int_» PC_CELL 1 = some _Val12)
  (symState : EVM.State):
  let rhs := (@expRHS _Val11 _Val12 _Val20 SCHEDULE_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  stateMap symState rhs =
  {symState with
    stack := (intMap (TODO.exp_representation W0 W1)) :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val20
    executionEnv := executionEnv_map rhs symState
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap rhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := by
    aesop (add simp [expRHS, stateMap, «_+Int_»])
    sorry

open StackOpsSummary

/- TODO: correctly articulate the case where `0 < W1` -/
def exp_case.gas : ℕ :=
  match ec with
  | eq0 => GasConstants.Gexp
  | gt0 => GasConstants.Gexp + GasConstants.Gexpbyte -- Blatantly wrong

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_exp_equiv
  {GAS_CELL PC_CELL W0 W1 _Val1 _Val11 _Val12 _Val13 _Val14 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val10 _Val8 _Val9 _Val2_eq _Val3_eq _Val4_eq : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK}
  (defn_Val0 : ec.to_defn_Val0 W1 _Val0)
  (defn_Val1 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val3)
  (defn_Val4 : «_/Int_» _Val3 8 = some _Val4)
  (defn_Val5 : «_+Int_» _Val4 1 = some _Val5)
  (defn_Val6 : «_*Int_» _Val2 _Val5 = some _Val6)
  (defn_Val7 : «_+Int_» _Val1 _Val6 = some _Val7)
  (defn_Val8 : ec.to_defn_Val8 GAS_CELL _Val1 _Val7 _Val8 _Val2_eq)
  (defn_Val9 : ec.to_defn_Val9 _Val0 _Val2_eq _Val3_eq _Val8 _Val9)
  (defn_Val10 : ec.to_defn_Val10 USEGAS_CELL _Val3_eq _Val4_eq _Val9 _Val10)
  (defn_Val11 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val11)
  (defn_Val12 : «_+Int_» PC_CELL 1 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val15)
  (defn_Val16 : «_/Int_» _Val15 8 = some _Val16)
  (defn_Val17 : «_+Int_» _Val16 1 = some _Val17)
  (defn_Val18 : «_*Int_» _Val14 _Val17 = some _Val18)
  (defn_Val19 : «_+Int_» _Val13 _Val18 = some _Val19)
  (defn_Val20 : ec.to_defn_Val20 GAS_CELL _Val13 _Val19 _Val20)
  (req : ec.to_req _Val4_eq _Val10)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : ec.gas ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = ec.gas)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  let lhs := (@expLHS GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
  let rhs := (@expRHS _Val11 _Val12 _Val20 SCHEDULE_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  EVM.step_arith .exp gas gasCost (stateMap symState lhs) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} rhs) := by
  intro lhs rhs
  rw [exp_prestate_equiv, @exp_poststate_equiv PC_CELL W0 W1 _ _ _Val12]
  <;> try assumption
  cases gas; contradiction
  case succ gas =>
    have : intMap W0 :: intMap W1 :: wordStackMap WS =
    StackOpsSummary.arith_op.stack .exp
      (intMap W0) (intMap W1) (intMap W1) (wordStackMap WS) := by aesop
    rw [this]
    rw [executionEnv_map, EVM.step_add_summary] <;> try assumption
    simp [expLHS, expRHS]; constructor <;> try constructor
    . aesop (add simp [exp_case.gas, GasConstants.Gexp, GasInterface.cancun_def, «_-Int_»])
      (add safe (by rw [intMap_sub_dist]))
      /- All remaining goals are for the `exp_case.gt0` case -/
      all_goals sorry
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . cases ec
      . -- `gt0` case
        -- To prove this, first `TODO.exp_representation` needs to be fixed for `gt0`
        sorry
      . -- `eq0` case
        -- To prove this, first `TODO.exp_representation` needs to be fixed for `eq0`
        sorry

attribute [local simp] GasConstants.Gexp

/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode (`ADD`) program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_exp_equiv
  {GAS_CELL PC_CELL W0 W1 _Val1 _Val11 _Val12 _Val13 _Val14 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val10 _Val8 _Val9 _Val2_eq _Val3_eq _Val4_eq : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortVersionedHashesCell}
  {_Gen17 : SortSubstateCell}
  {_Gen18 : SortGasPriceCell}
  {_Gen19 : SortOriginCell}
  {_Gen2 : SortIdCell}
  {_Gen20 : SortBlockhashesCell}
  {_Gen21 : SortBlockCell}
  {_Gen22 : SortExitCodeCell}
  {_Gen23 : SortModeCell}
  {_Gen3 : SortCallerCell}
  {_Gen4 : SortCallDataCell}
  {_Gen5 : SortCallValueCell}
  {_Gen6 : SortLocalMemCell}
  {_Gen7 : SortMemoryUsedCell}
  {_Gen8 : SortCallGasCell}
  {_Gen9 : SortStaticCell}
  {_K_CELL : SortK}
  (defn_Val0 : ec.to_defn_Val0 W1 _Val0)
  (defn_Val1 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val3)
  (defn_Val4 : «_/Int_» _Val3 8 = some _Val4)
  (defn_Val5 : «_+Int_» _Val4 1 = some _Val5)
  (defn_Val6 : «_*Int_» _Val2 _Val5 = some _Val6)
  (defn_Val7 : «_+Int_» _Val1 _Val6 = some _Val7)
  (defn_Val8 : ec.to_defn_Val8 GAS_CELL _Val1 _Val7 _Val8 _Val2_eq)
  (defn_Val9 : ec.to_defn_Val9 _Val0 _Val2_eq _Val3_eq _Val8 _Val9)
  (defn_Val10 : ec.to_defn_Val10 USEGAS_CELL _Val3_eq _Val4_eq _Val9 _Val10)
  (defn_Val11 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val11)
  (defn_Val12 : «_+Int_» PC_CELL 1 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val15)
  (defn_Val16 : «_/Int_» _Val15 8 = some _Val16)
  (defn_Val17 : «_+Int_» _Val16 1 = some _Val17)
  (defn_Val18 : «_*Int_» _Val14 _Val17 = some _Val18)
  (defn_Val19 : «_+Int_» _Val13 _Val18 = some _Val19)
  (defn_Val20 : ec.to_defn_Val20 GAS_CELL _Val13 _Val19 _Val20)
  (req : ec.to_req _Val4_eq _Val10)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (codeDiv : _Gen0 = ⟨⟨#[0xA]⟩⟩)
  (pcZero : PC_CELL = 0)
  (enoughGas :ec.gas < GAS_CELL)
  (boundedGas : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  (boundedW1 : W1 < ↑UInt256.size)
  -- There's no #sizeWordStack
  (wordStackOk : sizeWordStackAux WS 0 < some 1023):
  let lhs := (@expLHS GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
  let rhs := (@expRHS _Val11 _Val12 _Val20 SCHEDULE_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 ⟨.empty⟩ _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState lhs) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} rhs) ByteArray.empty) := by
  intro lhs rhs; simp [lhs, rhs]
  -- With `simp` doesn't work
  rw [codeDiv, pcZero]
  rw [exp_prestate_equiv, @exp_poststate_equiv PC_CELL W0 W1 _ _ _Val12]
  <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  have stack_op : intMap W0 :: intMap W1 :: wordStackMap WS =
    StackOpsSummary.arith_op.stack .exp
      (intMap W0) (intMap W1) (intMap W1) (wordStackMap WS) := rfl
  have code_op : ⟨#[0xA]⟩ = StackOpsSummary.arith_op.to_bin .exp := rfl
  simp [executionEnv_map, expLHS]
  rw [stack_op, code_op, pc_equiv, X_arith_summary]
  /- This have could be subsumed, but it's useful for the `gt0` case above -/
  have W1_zero_eq : (intMap W1 == { val := 0 }) = true → W1 = 0 := by
    sorry
  have W1_zero_eq' : ec = .eq0 → W1 = 0 := by
    intro ecc; simp [ecc] at defn_Val0
    aesop (add simp [«_<=Int_»]) (add safe (by linarith))
  · cases ec <;> simp [arith_op.C'_comp]
    . -- `gt0` case
      -- To prove this, first `TODO.exp_representation` needs to be fixed for `gt0`
      aesop (add simp [GasInterface.cancun_def, plusInt_def, intMap_add_dist, expLHS, expRHS])
      (add safe (by rw [intMap_sub_dist]))
      (add safe (by apply le_of_lt))
      all_goals sorry
    . -- `eq0` case
      -- To prove this, first `TODO.exp_representation` needs to be fixed for `eq0`
      aesop (add simp [GasInterface.cancun_def, plusInt_def, intMap_add_dist, expLHS, expRHS])
      (add safe (by rw [intMap_sub_dist]))
      (add safe (by apply le_of_lt))
      (add safe (by contradiction))
      sorry
  · cases ec <;> simp <;> simp [sizeWordStack_def] at wordStackOk <;> assumption
  · cases ec <;> simp [arith_op.C'_comp] <;>
    simp [exp_case.gas] at enoughGas <;>
    simp [exp_case.to_defn_Val0] at defn_Val0
    . -- Enough Gas `gt0`
      -- To solve this one we need to describe accurately gas expenditure in `exp_case.gas`
      rw [intMap_toNat, intMap_toNat] <;> try linarith
      sorry
    . -- Enough Gas `gt0`
      have : W1 = 0 := by aesop (add simp [«_<=Int_»]) (add safe (by linarith))
      simp [this, intMap, UInt256.toSigned]
      have : (UInt256.ofNat 0 == { val := 0 }) = true := by aesop
      aesop (add simp [UInt256.ofNat_toNat]) (add safe (by contradiction))

end ExpOpcodeEquivalence
