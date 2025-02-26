import EvmYul.EVM.Semantics
import EvmEquivalence.KEVM2Lean.Sorts
import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.KEVM2Lean.Rewrite

open EvmYul
open EVM

namespace StateMap

/- Maps from K types to EvmYul types -/
abbrev intMap (n : SortInt) : UInt256 := UInt256.toSigned n

@[simp]
def wordStackMap (ws : SortWordStack) : Stack UInt256 :=
  match ws with
  | .«.WordStack_EVM-TYPES_WordStack» => []
  | .«_:__EVM-TYPES_WordStack_Int_WordStack» w ws => intMap w :: (wordStackMap ws)

@[simp]
def wordStackCellMap (wsc : SortWordStackCell) : Stack UInt256 :=
  wordStackMap wsc.val

@[simp]
def pcCellMap (pcc : SortPcCell) : UInt256 :=
  intMap pcc.val

@[simp]
def gasMap (gs : SortGas) : UInt256 :=
  match gs with | .inj_SortInt g => intMap g

@[simp]
def gasCellMap (gc : SortGasCell) : UInt256 :=
  gasMap gc.val

/- Getters for accessing cells from the Generated Top Cell -/

@[simp]
def evmOfGTC (tc : SortGeneratedTopCell) :SortEvmCell :=
  tc.kevm.ethereum.evm

@[simp]
def callStateOfGTC (tc : SortGeneratedTopCell) : SortCallStateCell :=
  tc.kevm.ethereum.evm.callState

@[simp]
def wordStackCellOfGTC (tc : SortGeneratedTopCell) : SortWordStackCell :=
  tc.kevm.ethereum.evm.callState.wordStack

@[simp]
def pcOfGTC (tc : SortGeneratedTopCell) : SortPcCell :=
  tc.kevm.ethereum.evm.callState.pc

@[simp]
def gasOfGTC (tc : SortGeneratedTopCell) : SortGasCell :=
  tc.kevm.ethereum.evm.callState.gas
@[simp]
def programOfGTC (tc : SortGeneratedTopCell) : SortProgramCell :=
  tc.kevm.ethereum.evm.callState.program
@[simp]
def outputOfGTC (tc : SortGeneratedTopCell) : SortOutputCell :=
  tc.kevm.ethereum.evm.output

/- State Mapping: Mapping KEVM states to EvmYul states -/

-- We temporarely require the `symState` argument since we don't map the entire KEVM state yet
def stateMap (symState : EVM.State) (tc : SortGeneratedTopCell) : EVM.State :=
  {symState with
  stack := wordStackCellMap (wordStackCellOfGTC tc)
  pc := pcCellMap (pcOfGTC tc)
  gasAvailable := gasCellMap (gasOfGTC tc)
  executionEnv := {symState.executionEnv with code := (programOfGTC tc).val}
  returnData := (outputOfGTC tc).val
  }

end StateMap
