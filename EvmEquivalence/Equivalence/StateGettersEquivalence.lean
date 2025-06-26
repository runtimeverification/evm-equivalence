import EvmEquivalence.Summaries.StateGettersSummary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace StateGettersEquivalence

/- Equivalence proofs for arithmetic opcodes that take one operation to summarize -/

inductive stateGetter_op where
  | address
  | origin
  | caller
  | gasprice
  | coinbase
  | timestamp
  | number
  | prevrandao

variable (op : stateGetter_op)

@[simp]
def stateGetter_op.to_binop : stateGetter_op → SortNullStackOp
  | .address  => .ADDRESS_EVM_NullStackOp
  | .origin => .ORIGIN_EVM_NullStackOp
  | .caller => .CALLER_EVM_NullStackOp
  | .gasprice => .GASPRICE_EVM_NullStackOp
  | .coinbase => .COINBASE_EVM_NullStackOp
  | .timestamp => .TIMESTAMP_EVM_NullStackOp
  | .number => .NUMBER_EVM_NullStackOp
  | .prevrandao => .PREVRANDAO_EVM_NullStackOp

def stateGetter_op.from_k : stateGetter_op → StateGettersSummary.stateGetter_op
 | .address  => .address
 | .origin => .origin
 | .caller => .caller
 | .gasprice => .gasprice
 | .coinbase => .coinbase
 | .timestamp => .timestamp
 | .number => .number
 | .prevrandao => .prevrandao

def oneOpLHS
  {GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL: SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortNullStackOp SortMaybeOpCode) op.to_binop))) _K_CELL },
      exitCode := _Gen21,
      mode := _Gen22,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := USEGAS_CELL },
      ethereum := {
        evm := {
          output := _Gen10,
          statusCode := _Gen11,
          callStack := _Gen12,
          interimStates := _Gen13,
          touchedAccounts := _Gen14,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := { val := (@inj SortInt SortAccount) ID_CELL },
            caller := { val := (@inj SortInt SortAccount) CALLER_CELL },
            callData := _Gen3,
            callValue := _Gen4,
            wordStack := { val := WS },
            localMem := _Gen5,
            pc := { val := PC_CELL },
            gas := { val := (@inj SortInt SortGas) GAS_CELL },
            memoryUsed := _Gen6,
            callGas := _Gen7,
            static := _Gen8,
            callDepth := _Gen9 },
          versionedHashes := _Gen15,
          substate := _Gen16,
          gasPrice := { val := GASPRICE_CELL },
          origin := { val := (@inj SortInt SortAccount) ORIGIN_CELL },
          blockhashes := _Gen19,
          block := {_Gen20 with
                    coinbase := { val := COINBASE_CELL},
                    timestamp := { val := TIMESTAMP_CELL },
                    number := { val := NUMBER_CELL },
                    mixHash := { val := MIXHASH_CELL }
                    } },
        network := _DotVar2 } },
    generatedCounter := _DotVar0 }

def oneOpRHS
  {TOP_STACK ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL _Val6 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK} : SortGeneratedTopCell :=
    { kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen10,
            statusCode := _Gen11,
            callStack := _Gen12,
            interimStates := _Gen13,
            touchedAccounts := _Gen14,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := { val := (@inj SortInt SortAccount) ID_CELL },
              caller := { val := (@inj SortInt SortAccount) CALLER_CELL },
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» TOP_STACK WS },
              localMem := _Gen5,
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen15,
            substate := _Gen16,
            gasPrice := { val := GASPRICE_CELL },
            origin := { val := (@inj SortInt SortAccount) ORIGIN_CELL },
            blockhashes := _Gen19,
            block := {_Gen20 with
                    coinbase := { val := COINBASE_CELL},
                    timestamp := { val := TIMESTAMP_CELL },
                    number := { val := NUMBER_CELL },
                    mixHash := { val := MIXHASH_CELL },
                    } },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }

@[simp]
def stateGetter_op.to_gas : stateGetter_op → SortScheduleConst
 | _ => .Gbase_SCHEDULE_ScheduleConst

/- Apparently the name `SortAccount.toInt` won't work for calls -/
@[simp]
def acc2Int : SortAccount → SortInt
  | .inj_SortInt n => n | _ => 0

@[simp]
def stateGetter_op.do (tc : SortGeneratedTopCell) : SortInt :=
  match op with
  | .address  => acc2Int tc.Iₐ.val
  | .origin => acc2Int tc.origin.val
  | .caller => acc2Int tc.caller.val
  | .gasprice => tc.gasPrice.val
  | .coinbase => tc.coinbase.val
  | .timestamp => tc.timestamp.val
  | .number => tc.number.val
  | .prevrandao => tc.mixhash.val

theorem rw_oneOpLHS_oneOpRHS
  {GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK}
  (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
  (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
  (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
  (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
  (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
  (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
  (req : _Val5 = true):
  let lhs := (@oneOpLHS op GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10
  _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19
  _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  let rhs := (@oneOpRHS (op.do lhs) ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  Rewrites lhs rhs
   := by
  --intro lhs rhs; simp [lhs, rhs, oneOpLHS, oneOpRHS]
  cases op
  . apply (@Rewrites.ADDRESS_SUMMARY_ADDRESS_SUMMARY_USEGAS GAS_CELL ID_CELL PC_CELL _Val0 _Val2)
    <;> assumption
  . apply (@Rewrites.ORIGIN_SUMMARY_ORIGIN_SUMMARY_USEGAS GAS_CELL ORIGIN_CELL PC_CELL _Val0 _Val2)
    <;> assumption
  . apply (@Rewrites.CALLER_SUMMARY_CALLER_SUMMARY_USEGAS CALLER_CELL GAS_CELL PC_CELL _Val0 _Val2)
    <;> assumption
  . apply (@Rewrites.GASPRICE_SUMMARY_GASPRICE_SUMMARY_USEGAS GASPRICE_CELL GAS_CELL PC_CELL _Val0 _Val2)
    <;> try assumption
  . apply (@Rewrites.COINBASE_SUMMARY_COINBASE_SUMMARY_USEGAS COINBASE_CELL GAS_CELL PC_CELL _Val0 _Val2)
    <;> try assumption
  . apply (@Rewrites.TIMESTAMP_SUMMARY_TIMESTAMP_SUMMARY_USEGAS GAS_CELL PC_CELL TIMESTAMP_CELL _Val0 _Val2)
    <;> try assumption
  . apply (@Rewrites.NUMBER_SUMMARY_NUMBER_SUMMARY_USEGAS GAS_CELL NUMBER_CELL PC_CELL _Val0 _Val2)
    <;> try assumption
  . apply (@Rewrites.PREVRANDAO_SUMMARY_PREVRANDAO_SUMMARY_USEGAS GAS_CELL MIXHASH_CELL PC_CELL _Val0 _Val2)
    <;> try assumption

theorem oneOp_prestate_equiv
  {GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL: SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK}
  (symState : EVM.State):
  let lhs := (@oneOpLHS op GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10
  _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19
  _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  stateMap symState lhs =
  {symState with
    stack := wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := executionEnv_map lhs symState
    /- {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap lhs.Iₐ
                  sender := accountAddressMap lhs.origin.val
                  source := accountAddressMap lhs.caller.val
                  gasPrice := GASPRICE_CELL
                  perm := !lhs.isStatic.val} -/
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap lhs.accessedStorage
            refundBalance := intMap _Gen16.refund.val
           }
    returnData := _Gen10.val
    } := by
    cases cop: op <;>
    simp [oneOpLHS, cop, stateMap, stateGetter_op.from_k] <;> rfl

theorem oneOp_poststate_equiv
  {TOP_STACK ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val5 _Val6 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK}
  (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
  (symState : EVM.State):
  let rhs := (@oneOpRHS TOP_STACK ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  stateMap symState rhs =
  {symState with
    stack := (intMap TOP_STACK) :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap _Val8
    executionEnv := executionEnv_map rhs symState
    /- {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap rhs.Iₐ,
                  sender := accountAddressMap rhs.origin.val
                  source := accountAddressMap rhs.caller.val
                  gasPrice := GASPRICE_CELL
                  perm := !rhs.isStatic.val} -/
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap rhs.accessedStorage
            refundBalance := intMap _Gen16.refund.val
           }
    returnData := _Gen10.val
    } := by aesop (add simp [oneOpRHS, stateMap])

open StateGettersSummary

def stateGetter_op.gas :=
  match op with
  | _ => GasConstants.Gbase

attribute [local simp] GasConstants.Gbase

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_oneOp_equiv
  {GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK}
  (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
  (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
  (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
  (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
  (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
  (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
  (req : _Val5 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : op.gas ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = op.gas)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (ID_CELL_small : ID_CELL < AccountAddress.size)
  (ID_CELL_nonneg : 0 ≤ ID_CELL)
  (ORIGIN_CELL_small : ORIGIN_CELL < AccountAddress.size)
  (ORIGIN_CELL_nonneg : 0 ≤ ORIGIN_CELL)
  (CALLER_CELL_small : CALLER_CELL < AccountAddress.size)
  (CALLER_CELL_nonneg : 0 ≤ CALLER_CELL)
  (COINBASE_CELL_small : COINBASE_CELL < AccountAddress.size)
  (COINBASE_CELL_nonneg : 0 ≤ COINBASE_CELL)
  (TIMESTAMP_CELL_small : TIMESTAMP_CELL < UInt256.size)
  (TIMESTAMP_CELL_nonneg : 0 ≤ TIMESTAMP_CELL)
  (NUMBER_CELL_small : NUMBER_CELL < UInt256.size)
  (NUMBER_CELL_nonneg : 0 ≤ NUMBER_CELL):
  let lhs := (@oneOpLHS op GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10
  _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19
  _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  let rhs := (@oneOpRHS (op.do lhs) ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL _Val6 _Val8 GASPRICE_CELL  SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16  _Gen19 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  EVM.step_arith op.from_k gas gasCost (stateMap symState lhs) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} rhs) := by
  intro lhs rhs
  rw [oneOp_prestate_equiv]
  rw [@oneOp_poststate_equiv _ ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL]
  <;> try assumption
  cases gas; contradiction
  case succ gas =>
    rw [executionEnv_map, blockHeader_map, EVM.step_getter_summary]
    <;> try assumption
    simp [oneOpLHS, oneOpRHS]; constructor <;> try constructor
    . cases op <;>
      simp [cancun, GasInterface.cancun_def] at defn_Val0 defn_Val5 <;>
      aesop (add simp [stateGetter_op.gas, GasInterface.cancun_def, «_-Int_», intMap_sub_dist])
    . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
    . generalize h_top_stack : op.do lhs = top_stack
      cases op <;> simp [lhs, oneOpLHS, stateGetter_op.from_k] <;>
       -- `address`
        simp [intMap, AccountAddress.ofNat, UInt256.ofNat, Id.run, UInt256.toSigned] <;>
        cases top_stack <;>
        aesop (add simp [Fin.val, Fin.ofNat, AccountAddress.size, State.coinBase, State.timeStamp])
        (add safe (by omega))
      /- . -- `origin`
        simp [intMap, AccountAddress.ofNat, UInt256.ofNat, Id.run, UInt256.toSigned]
        cases top_stack <;>
        aesop (add simp [Fin.val, Fin.ofNat, AccountAddress.size])
        (add safe (by omega)) -/


attribute [local simp] GasConstants.Glow

/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_oneOp_equiv
  {GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
  -- We assume `GASPRICE_CELL` is not negative
  {GASPRICE_CELL : ℕ}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortOutputCell}
  {_Gen11 : SortStatusCodeCell}
  {_Gen12 : SortCallStackCell}
  {_Gen13 : SortInterimStatesCell}
  {_Gen14 : SortTouchedAccountsCell}
  {_Gen15 : SortVersionedHashesCell}
  {_Gen16 : SortSubstateCell}
  {_Gen19 : SortBlockhashesCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortBlockCell}
  {_Gen21 : SortExitCodeCell}
  {_Gen22 : SortModeCell}
  {_Gen3 : SortCallDataCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_K_CELL : SortK}
  (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
  (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
  (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
  (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
  (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
  (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
  (req : _Val5 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (codeDiv : _Gen0 = ⟨op.from_k.to_bin⟩)
  (pcZero : PC_CELL = 0)
  (enoughGas : op.gas < GAS_CELL)
  (boundedGas : GAS_CELL < ↑UInt256.size)
  (ID_CELL_small : ID_CELL < AccountAddress.size)
  (ID_CELL_nonneg : 0 ≤ ID_CELL)
  (ORIGIN_CELL_small : ORIGIN_CELL < AccountAddress.size)
  (ORIGIN_CELL_nonneg : 0 ≤ ORIGIN_CELL)
  (CALLER_CELL_small : CALLER_CELL < AccountAddress.size)
  (CALLER_CELL_nonneg : 0 ≤ CALLER_CELL)
  (COINBASE_CELL_small : COINBASE_CELL < AccountAddress.size)
  (COINBASE_CELL_nonneg : 0 ≤ COINBASE_CELL)
  (TIMESTAMP_CELL_small : TIMESTAMP_CELL < UInt256.size)
  (TIMESTAMP_CELL_nonneg : 0 ≤ TIMESTAMP_CELL)
  (NUMBER_CELL_small : NUMBER_CELL < UInt256.size)
  (NUMBER_CELL_nonneg : 0 ≤ NUMBER_CELL) :
  let lhs := (@oneOpLHS op GAS_CELL ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 ⟨op.from_k.to_bin⟩ _Gen1 _Gen10
  _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19
  _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  let rhs := (@oneOpRHS (op.do lhs) ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL _Val6 _Val8 GASPRICE_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 ⟨.empty⟩ _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen19 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState lhs) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} rhs) ByteArray.empty) := by
  intro lhs rhs; simp [lhs, rhs]
  -- With `simp` doesn't work
  --rw [codeDiv, pcZero]
  rw [oneOp_prestate_equiv]
  rw [@oneOp_poststate_equiv _ ID_CELL ORIGIN_CELL CALLER_CELL COINBASE_CELL TIMESTAMP_CELL MIXHASH_CELL NUMBER_CELL PC_CELL]
  <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  rw [pcZero, pc_equiv, executionEnv_map, blockHeader_map]
  rw [X_getter_summary op.from_k]
  case enoughGas => rw [intMap_toNat] <;> aesop (add safe (by linarith))
  case symStack_ok =>
    aesop (add simp [sizeWordStack_def, «_<=Int_»]) (add safe (by linarith))
  case code_h => simp [oneOpLHS]
  congr <;> try simp
  . cases op <;>
    simp [stateGetter_op.C'_comp, stateGetter_op.from_k, oneOpLHS, oneOpRHS] <;>
    aesop
  . -- Gas deduction
    aesop (add simp [stateGetter_op.C'_comp, stateGetter_op.from_k])
    (add safe (by rw [intMap_sub_dist]))
    (add safe (by apply le_of_lt))
  . generalize h_top_stack : op.do lhs = top_stack
    cases op <;> simp [stateGetter_op.from_k]
    --. -- `address`
      <;>
      cases top_stack <;> simp [oneOpLHS, intMap, AccountAddress.ofNat] <;>
      simp [UInt256.ofNat, Id.run, UInt256.toSigned] <;>
      aesop (add simp [Fin.val, Fin.ofNat, AccountAddress.size, State.coinBase, State.number])
      (add safe (by omega))

end StateGettersEquivalence
