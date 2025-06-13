import EvmEquivalence.Summaries.AddSummary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace DivOpcodeEquivalence

inductive arith_op where
  | div
  | sdiv
  | mod

variable (op : arith_op)

@[simp]
def arith_op.to_binop : arith_op → SortBinStackOp
  | .div  => .DIV_EVM_BinStackOp
  | .sdiv => .SDIV_EVM_BinStackOp
  | .mod  => .MOD_EVM_BinStackOp

def arith_op.from_k : arith_op → AddSummary.arith_op
 | .div  => .div
 | .sdiv => .sdiv
 | .mod  => .mod

def divLHS
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
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) op.to_binop))) _K_CELL },
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

def divRHS
  {_Val3 _Val4 _Val5 _Val6 : SortInt}
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
  {_K_CELL : SortK}: SortGeneratedTopCell :=
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
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
            localMem := _Gen6,
            pc := { val := _Val4 },
            gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | .div  => «_/Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3
  | .sdiv => «_/sWord__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3
  | .mod  => «_%Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3

theorem rw_addLHS_addRHS
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
  {_K_CELL : SortK}
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
  (req : _Val2 = true):
  Rewrites
  (@divLHS op GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL USEGAS_CELL WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  (@divRHS _Val3 _Val4 _Val5 _Val6 SCHEDULE_CELL _Val1 _Val2 WS
  _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14
  _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22
  _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL) := by
  cases op
  . apply (@Rewrites.DIV_SUMMARY_DIV_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.SDIV_SUMMARY_SDIV_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.MOD_SUMMARY_MOD_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption

theorem div_prestate_equiv
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
  let lhs := (@divLHS op GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
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

def divWord (n m : SortInt) : SortInt:=
  if h : m == 0 then 0 else
  ((«_/Int_» n m).get (by simp [«_/Int_»]; aesop))

theorem divWord_divInt_eq (n m : SortInt):
  «_/Word__EVM-TYPES_Int_Int_Int» n m = some (divWord n m) := by
  simp [«_/Word__EVM-TYPES_Int_Int_Int», _19cae79, _72d6664]
  simp [Option.bind]
  cases m0: (m == 0) <;>
  simp [«_=/=Int_», _4de6e05, «_==Int_», notBool_, _17ebc68, _53fc758, m0] <;>
  simp [divWord] <;> aesop

@[simp]
def arith_op.do : SortInt → SortInt → SortInt :=
  match op with
  | .div  => (divWord · ·)
  | .sdiv => (divWord · ·) -- Blatantly wrong
  | .mod  => (divWord · ·) -- Blatantly wrong

theorem div_poststate_equiv
  {PC_CELL W0 W1 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
  {_K_CELL : SortK}
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
  (symState : EVM.State):
  let rhs := (@divRHS _Val3 _Val4 _Val5 _Val6 SCHEDULE_CELL _Val1
  _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12
  _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20
  _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9
  _K_CELL)
  stateMap symState rhs =
  {symState with
    stack := (intMap (op.do W0 W1)) :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val6
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
    cases op
    . -- `div`
      aesop (add simp [«_-Int_»,«_+Int_», arith_op.to_defn_Val3, divRHS, stateMap])
    (add simp [divWord_divInt_eq])
    . -- `sdiv`
      -- To prove this, first `arith_op.do` needs to be fixed for `sdiv`
      aesop (add simp [«_-Int_»,«_+Int_», arith_op.to_defn_Val3, divRHS, stateMap])
      sorry
    . -- `mod`
      -- To prove this, first `arith_op.do` needs to be fixed for `mod`
      aesop (add simp [«_-Int_»,«_+Int_», arith_op.to_defn_Val3, divRHS, stateMap])
      sorry


open AddSummary

def arith_op.gas :=
  match op with
  | .div  => GasConstants.Glow
  | .sdiv => GasConstants.Glow
  | .mod  => GasConstants.Glow

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_add_equiv
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
  {_K_CELL : SortK}
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
  (req : _Val2 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : 5 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = op.gas)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  let lhs := (@divLHS op GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
  let rhs := (@divRHS _Val3 _Val4 _Val5 _Val6 SCHEDULE_CELL _Val1
  _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12
  _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20
  _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9
  _K_CELL)
  EVM.step_arith op.from_k gas gasCost (stateMap symState lhs) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} rhs) := by
  intro lhs rhs
  rw [div_prestate_equiv, @div_poststate_equiv _ _ W0 W1 _Val3]
  <;> try assumption
  cases gas; contradiction
  case succ gas =>
    rw [EVM.step_add_summary] <;> try assumption
    simp [divLHS, divRHS]; constructor <;> try constructor
    . aesop (add simp [arith_op.gas, GasConstants.Glow, GasInterface.cancun_def, «_-Int_», intMap_sub_dist])
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . cases op <;> simp [arith_op.from_k]
      . -- `div` case
        sorry
      . -- `sdiv`
      -- To prove this, first `arith_op.do` needs to be fixed for `sdiv`
        sorry
      .  -- `mod`
      -- To prove this, first `arith_op.do` needs to be fixed for `mod`
        sorry

attribute [local simp] GasConstants.Glow

/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode (`ADD`) program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_add_equiv
  {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
  {_K_CELL : SortK}
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3)
  (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
  (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
  (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
  (req : _Val2 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (codeDiv : _Gen0 = ⟨op.from_k.to_bin⟩)
  (pcZero : PC_CELL = 0)
  (enoughGas : 5 < GAS_CELL)
  (boundedGas : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  -- There's no #sizeWordStack
  (wordStackOk : sizeWordStackAux WS 0 < some 1024):
  let lhs := (@divLHS op GAS_CELL PC_CELL W0 W1 SCHEDULE_CELL
   USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11
   _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2
   _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8
   _Gen9 _K_CELL)
  let rhs := (@divRHS _Val3 _Val4 _Val5 _Val6 SCHEDULE_CELL _Val1
  _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 ⟨.empty⟩ _Gen12
  _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20
  _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9
  _K_CELL)
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState lhs) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} rhs) ByteArray.empty) := by
  intro lhs rhs; simp [lhs, rhs]
  -- With `simp` doesn't work
  rw [codeDiv, pcZero]
  rw [div_prestate_equiv, @div_poststate_equiv _ _ W0 W1 _Val3]
  <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  rw [pc_equiv, X_arith_summary]
  · cases op <;> simp [arith_op.from_k]
    . -- `div` case
      aesop (add simp [GasInterface.cancun_def, «_-Int_», chop_def, plusInt_def, intMap_add_dist, divLHS, divRHS])
      (add safe (by rw [intMap_sub_dist])) (add safe (by apply le_of_lt))
      sorry
    . -- `sdiv`
      -- To prove this, first `arith_op.do` needs to be fixed for `sdiv`
      aesop (add simp [GasInterface.cancun_def, «_-Int_», chop_def, plusInt_def, intMap_add_dist, divLHS, divRHS])
      (add safe (by rw [intMap_sub_dist])) (add safe (by apply le_of_lt))
      sorry
    . -- `mod`
      -- To prove this, first `arith_op.do` needs to be fixed for `mod`
      aesop (add simp [GasInterface.cancun_def, «_-Int_», chop_def, plusInt_def, intMap_add_dist, divLHS, divRHS])
      (add safe (by rw [intMap_sub_dist])) (add safe (by apply le_of_lt))
      sorry
  · cases op <;> simp [C'_comp, arith_op.from_k] <;>
    rw [intMap_toNat] <;> aesop (add safe (by linarith))
  · simp_all [sizeWordStack_def]

end DivOpcodeEquivalence
