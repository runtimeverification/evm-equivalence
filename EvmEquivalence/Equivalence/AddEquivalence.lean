import EvmEquivalence.Summaries.AddSummary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace AddOpcodeEquivalence

inductive arith_op where
  | add
  | sub

variable (op : arith_op)

@[simp]
def arith_op.to_binop : arith_op → SortBinStackOp
  | .add => .ADD_EVM_BinStackOp
  | .sub => .SUB_EVM_BinStackOp

def arith_op.from_k : arith_op → AddSummary.arith_op
 | .add => .add
 | .sub => .sub

def addLHS
  {GAS_CELL PC_CELL W0 W1 : SortInt}
  {K_CELL : SortK}
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
  {_Gen9 : SortStaticCell} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) op.to_binop))) K_CELL },
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

def addRHS
  {_Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val1 _Val2 : SortBool}
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
  {_Gen9 : SortStaticCell}: SortGeneratedTopCell :=
  { kevm := {
      k := { val := K_CELL },
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
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val4 WS },
            localMem := _Gen6,
            pc := { val := _Val5 },
            gas := { val := (@inj SortInt SortGas) _Val7 },
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


def arith_op.to_defn_Val3 (W0 W1 _Val3 : SortInt) : Prop :=
  match op with
  | .add => «_+Int_» W0 W1 = some _Val3
  | .sub => «_-Int_» W0 W1 = some _Val3

theorem rw_addLHS_addRHS
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 : SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : chop _Val3 = some _Val4)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true):
  Rewrites
  (@addLHS op GAS_CELL PC_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@addRHS _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) := by
  cases op
  . apply (@Rewrites.ADD_SUMMARY_ADD_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.SUB_SUMMARY_SUB_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 SCHEDULE_CELL USEGAS_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
    <;> try assumption

theorem add_prestate_equiv
  {GAS_CELL PC_CELL W0 W1 : SortInt}
  {K_CELL : SortK}
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
  (symState : EVM.State):
  let lhs := (@addLHS op GAS_CELL PC_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: (intMap W1) :: wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap lhs.Iₐ
                  perm := !lhs.isStatic.val}
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap lhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := rfl

@[simp]
def arith_op.do : SortInt → SortInt → SortInt :=
  match op with
  | .add => (· + ·)
  | .sub => (· - ·)

theorem add_poststate_equiv
  {PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val1 _Val2 : SortBool}
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
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : chop _Val3 = some _Val4)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (symState : EVM.State):
  let rhs := (@addRHS _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState rhs =
  {symState with
    stack := (intMap (chop' (op.do W0 W1))) :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val7
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap rhs.Iₐ,
                  perm := !rhs.isStatic.val}
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap rhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := by
    aesop (add simp [«_-Int_»,«_+Int_», chop', arith_op.to_defn_Val3, addRHS, stateMap])


open AddSummary

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_add_equiv
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 : SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : chop _Val3 = some _Val4)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : 3 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = GasConstants.Gverylow)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  EVM.step_arith op.from_k gas gasCost (stateMap symState (@addLHS op GAS_CELL PC_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@addRHS _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) := by
  rw [add_prestate_equiv, @add_poststate_equiv _ _ W0 W1 _ _Val3]
  <;> try assumption
  cases gas; contradiction
  case succ gas =>
    rw [EVM.step_add_summary] <;> try assumption
    simp [addLHS, addRHS]; constructor <;> try constructor
    . aesop (add simp [GasInterface.cancun_def, «_-Int_», intMap_sub_dist])
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . cases op <;> simp [arith_op.from_k]
      . -- `add` case
        aesop (add simp [intMap, chop_def, plusInt_def, intMap_add_dist])
      . -- `sub` case
        sorry




/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode (`ADD`) program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_add_equiv
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 : SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : chop _Val3 = some _Val4)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (codeAdd : _Gen0 = ⟨op.from_k.to_bin⟩)
  (pcZero : PC_CELL = 0)
  (enoughGas : 3 < GAS_CELL)
  (boundedGas : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  -- There's no #sizeWordStack
  (wordStackOk : sizeWordStackAux WS 0 < some 1024):
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState (@addLHS op GAS_CELL PC_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@addRHS _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 ⟨ByteArray.empty⟩ _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) ByteArray.empty) := by
  -- With `simp` doesn't work
  rw [codeAdd, pcZero]
  rw [add_prestate_equiv, @add_poststate_equiv _ _ W0 W1 _ _Val3]
  <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  rw [pc_equiv, X_arith_summary]
  · cases op <;> simp [arith_op.from_k]
    . -- `add` case
      aesop (add simp [GasInterface.cancun_def, «_-Int_», chop_def, plusInt_def, intMap_add_dist, addLHS, addRHS])
      (add safe (by rw [intMap_sub_dist])) (add safe (by apply le_of_lt))
    . -- `sub` case
      sorry
  · aesop (add simp [GasConstants.Gverylow, intMap, UInt256.toSigned])
      (add simp [intMap_toNat, UInt256.ofNat_toNat])
      (add safe (by contradiction))
  · simp_all [sizeWordStack_def]

end AddOpcodeEquivalence
