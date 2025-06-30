import EvmEquivalence.Summaries.StackOperationsSummary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace TwoOpEquivalence

/- Equivalence proofs for arithmetic opcodes that take two operations to summarize -/

inductive arith_op where
  | add
  | sub
  | addmod
  | mulmod
  | lt
  | gt
  | eq
  | iszero

variable (op : arith_op)

@[simp]
def arith_op.to_binop : arith_op → SortBinStackOp ⊕ (SortTernStackOp ⊕ SortUnStackOp)
  | .add => .inl .ADD_EVM_BinStackOp
  | .sub => .inl .SUB_EVM_BinStackOp
  | .addmod => .inr (.inl .ADDMOD_EVM_TernStackOp)
  | .mulmod => .inr (.inl .MULMOD_EVM_TernStackOp)
  | .lt => .inl .LT_EVM_BinStackOp
  | .gt => .inl .GT_EVM_BinStackOp
  | .eq => .inl .EQ_EVM_BinStackOp
  | .iszero => .inr (.inr .ISZERO_EVM_UnStackOp)

@[simp]
def arith_op.to_maybeOpcode : SortMaybeOpCode :=
  match op.to_binop with
  | .inl op => (@inj SortBinStackOp SortMaybeOpCode) op
  | .inr (.inl op) => (@inj SortTernStackOp SortMaybeOpCode) op
  | .inr (.inr op) => (@inj SortUnStackOp SortMaybeOpCode) op

def arith_op.from_k : arith_op → StackOpsSummary.arith_op
 | .add => .add
 | .sub => .sub
 | .addmod => .addmod
 | .mulmod => .mulmod
 | .lt => .lt
 | .gt => .gt
 | .eq => .eq
 | .iszero => .iszero

@[simp]
def arith_op.to_stack (W0 W1 W2 : SortInt) (WS : SortWordStack) : SortWordStack :=
  match op.to_binop with
  | .inl _ => SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS)
  | .inr (.inl _) => SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W2 WS))
  | .inr (.inr _) => SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 WS

def twoOpLHS
  {GAS_CELL PC_CELL W0 W1 W2 : SortInt}
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
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» op.to_maybeOpcode)) K_CELL },
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
            wordStack := { val := op.to_stack W0 W1 W2 WS},
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

def twoOpRHS
  {_Val0 _Val4 _Val5 _Val6 _Val7 : SortInt}
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

/--
First Op for summarization
-/
def arith_op.to_defn_Val3 (W0 W1 _Val3_int : SortInt) (_Val3_bool : SortBool) : Prop :=
  match op with
  | .add | .addmod => «_+Int_» W0 W1 = some _Val3_int
  | .sub => «_-Int_» W0 W1 = some _Val3_int
  | .mulmod => «_*Int_» W0 W1 = some _Val3_int
  | .lt => «_<Int_» W0 W1 = some _Val3_bool
  | .gt => «_<Int_» W1 W0 = some _Val3_bool
  | .eq => «_==Int_» W0 W1 = some _Val3_bool
  | .iszero => «_==Int_» W0 0 = some _Val3_bool

/--
Second Op for summarization
-/
def arith_op.to_defn_Val4 (_Val3_bool : SortBool) (_Val3_int _Val4 W2: SortInt) : Prop :=
  match op with
  | .add | .sub => chop _Val3_int = some _Val4
  | .addmod | .mulmod => «_%Word__EVM-TYPES_Int_Int_Int» _Val3_int W2 = some _Val4
  | .lt | .gt | .eq | .iszero => bool2Word _Val3_bool = some _Val4

@[simp]
def arith_op.to_gas : arith_op → SortScheduleConst
 | .addmod | .mulmod => .Gmid_SCHEDULE_ScheduleConst
 | _ => .Gverylow_SCHEDULE_ScheduleConst

theorem rw_twoOpLHS_twoOpRHS
  {GAS_CELL PC_CELL W0 W1 W2 _Val0 _Val3_int _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 _Val3_bool : SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3_int _Val3_bool)
  (defn_Val4 : op.to_defn_Val4 _Val3_bool _Val3_int _Val4 W2)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true):
  Rewrites
  (@twoOpLHS op GAS_CELL PC_CELL W0 W1 W2 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@twoOpRHS _Val0 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) := by
  cases op
  . apply (@Rewrites.ADD_SUMMARY_ADD_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.SUB_SUMMARY_SUB_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.ADDMOD_SUMMARY_ADDMOD_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 W2 _Val0)
    <;> assumption
  . apply (@Rewrites.MULMOD_SUMMARY_MULMOD_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 W2 _Val0)
    <;> assumption
  . apply (@Rewrites.LT_SUMMARY_LT_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.GT_SUMMARY_GT_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.EQ_SUMMARY_EQ_SUMMARY_USEGAS GAS_CELL PC_CELL W0 W1 _Val0)
    <;> assumption
  . apply (@Rewrites.ISZERO_SUMMARY_ISZERO_SUMMARY_USEGAS GAS_CELL PC_CELL W0 _Val0)
    <;> assumption

theorem twoOp_prestate_equiv
  {GAS_CELL PC_CELL W0 W1 W2 : SortInt}
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
  let lhs := (@twoOpLHS op GAS_CELL PC_CELL W0 W1 W2 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState lhs =
  {symState with
    stack := op.from_k.stack (intMap W0) (intMap W1) (intMap W2) (wordStackMap WS)
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
    } := by
    cases cop: op <;>
    simp [twoOpLHS, cop, stateMap, arith_op.from_k] <;> rfl

def modWord (n m : SortInt) := ite (m = 0) 0 n % m

@[simp]
theorem modWord_eq (n m : SortInt) :
  «_%Word__EVM-TYPES_Int_Int_Int» n m = some (modWord n m) := by
  aesop (add simp [«_%Word__EVM-TYPES_Int_Int_Int», _08b1484, _952a14b])
  (add simp [Option.bind, «_=/=Int_», «_==Int_», _4de6e05, notBool_])
  (add simp [_17ebc68, _modInt_, modWord])

@[simp]
def arith_op.do (W0 W1 W2 : SortInt) : SortInt :=
  match op with
  | .add => chop' (W0 + W1)
  | .sub => chop' (W0 - W1)
  | .addmod => modWord (W0 + W1) W2
  | .mulmod => modWord (W0 * W1) W2
  | .lt => ite (W0 < W1) 1 0
  | .gt => ite (W1 < W0) 1 0
  | .eq => ite (W0 = W1) 1 0
  | .iszero => ite (W0 = 0) 1 0

@[simp]
def arith_op.gas_comp : arith_op → SortInt
  | .addmod | .mulmod => 8
  | _ => 3

theorem twoOp_poststate_equiv
  {PC_CELL W0 W1 W2 _Val0 _Val3_int _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val1 _Val2 _Val3_bool : SortBool}
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
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3_int _Val3_bool)
  (defn_Val4 : op.to_defn_Val4 _Val3_bool _Val3_int _Val4 W2)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (symState : EVM.State):
  let rhs := (@twoOpRHS _Val0 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState rhs =
  {symState with
    stack := (intMap (op.do W0 W1 W2)) :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val7
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
    aesop (add simp [«_-Int_», «_+Int_», «_*Int_», chop', chopIsSome])
    (add simp [arith_op.to_defn_Val3, arith_op.to_defn_Val4, twoOpRHS, stateMap])
    (add simp [bool2Word, _4bd3e13, _cb4e96d])

open StackOpsSummary

attribute [local simp] GasConstants.Gverylow GasConstants.Gmid

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_twoOp_equiv
  {GAS_CELL PC_CELL W0 W1 W2 _Val0 _Val3_int _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 _Val3_bool : SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3_int _Val3_bool)
  (defn_Val4 : op.to_defn_Val4 _Val3_bool _Val3_int _Val4 W2)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = op.from_k.C'_noexp)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  EVM.step_arith op.from_k gas gasCost (stateMap symState (@twoOpLHS op GAS_CELL PC_CELL W0 W1 W2 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@twoOpRHS _Val0 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) := by
  have gasAvailEnough : op.gas_comp ≤ GAS_CELL := by
   cases op <;> aesop (add simp [_andBool_, _5b9db8d, _61fbef3, «_<=Int_»])
  rw [twoOp_prestate_equiv, @twoOp_poststate_equiv _ _ W0 W1 W2 _ _Val3_int]
  <;> try assumption
  cases gas; contradiction
  case succ gas =>
    rw [executionEnv_map, blockHeader_map, EVM.step_add_summary]
    <;> try assumption
    simp [twoOpLHS, twoOpRHS]; constructor <;> try constructor
    . simp [«_-Int_»] at defn_Val7; simp [←defn_Val7]
      simp [GasInterface.cancun_def] at defn_Val6 defn_Val0
      simp [defn_Val6] at defn_Val0
      cases cop : op <;> rw [intMap_sub_dist] <;> aesop
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . cases op <;> simp [arith_op.from_k]
      . -- `add` case
        aesop (add simp [intMap, chop_def, plusInt_def, intMap_add_dist])
      . -- `sub` case
        sorry
      . -- `addmod` case
        sorry
      . -- `mulmod` case
        sorry
      . -- `lt` case
        aesop (add simp [UInt256.lt, UInt256.fromBool, Bool.toUInt256]) <;>
        /- We need a lemma to the effect that `a < b` iff `intMap a < intMap b` -/
        sorry
      . -- `gt` case
        sorry
      . -- `eq` case
        sorry
      . -- `iszero` case
        sorry


attribute [local simp] StackOpsSummary.arith_op.C'_comp

/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode (`ADD`) program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_twoOp_equiv
  {GAS_CELL PC_CELL W0 W1 W2 _Val0 _Val3_int _Val4 _Val5 _Val6 _Val7 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 _Val3_bool: SortBool}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
  (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
  (defn_Val3 : op.to_defn_Val3 W0 W1 _Val3_int _Val3_bool)
  (defn_Val4 : op.to_defn_Val4 _Val3_bool _Val3_int _Val4 W2)
  (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» op.to_gas SCHEDULE_CELL = some _Val6)
  (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
  (req : _Val2 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (codeTwoOp : _Gen0 = ⟨op.from_k.to_bin⟩)
  (pcZero : PC_CELL = 0)
  -- We need the strict equality
  (enoughGas : op.gas_comp < GAS_CELL)
  (boundedGas : GAS_CELL < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  -- There's no #sizeWordStack
  (wordStackOk : sizeWordStackAux WS 0 < some op.from_k.to_stack_length):
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState (@twoOpLHS op GAS_CELL PC_CELL W0 W1 W2 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@twoOpRHS _Val0 _Val4 _Val5 _Val6 _Val7 K_CELL SCHEDULE_CELL _Val1 _Val2 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 ⟨ByteArray.empty⟩ _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) ByteArray.empty) := by
  -- With `simp` doesn't work
  rw [codeTwoOp, pcZero]
  rw [twoOp_prestate_equiv, @twoOp_poststate_equiv _ _ W0 W1 W2 _ _Val3_int]
  <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  simp only [executionEnv_map, blockHeader_map, twoOpLHS, SortGeneratedTopCell.program]
  rw [pc_equiv, X_arith_summary]
  · cases op <;> simp [arith_op.from_k]
    . -- `add` case
      simp [«_-Int_»] at defn_Val7; simp [←defn_Val7]
      simp [GasInterface.cancun_def] at defn_Val6 defn_Val0
      simp [defn_Val6] at defn_Val0
      aesop (add simp [GasInterface.cancun_def, «_-Int_», chop_def, plusInt_def, intMap_add_dist, twoOpLHS, twoOpRHS, arith_op.C'_comp])
      (add simp [arith_op.from_k])
      (add safe (by rw [intMap_sub_dist])) (add safe (by apply le_of_lt))
    . -- `sub` case
      sorry
    . -- `addmod` case
      sorry
    . -- `mulmod` case
      sorry
    . -- `lt` case
      sorry
    . -- `gt` case
      sorry
    . -- `eq` case
      sorry
    . -- `iszero` case
      sorry
  · simp_all [sizeWordStack_def]
  · simp [GasInterface.cancun_def] at defn_Val6 defn_Val0
    simp [defn_Val6] at defn_Val0
    cases op <;> simp [arith_op.from_k] <;>
    rw [intMap_toNat] <;> aesop (add safe (by linarith))

end TwoOpEquivalence
