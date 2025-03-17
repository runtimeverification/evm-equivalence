import EvmYul.EVM.Semantics
import EvmEquivalence.KEVM2Lean.Sorts
import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.KEVM2Lean.Rewrite
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Utils.IntUtils

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

/- State Mapping Results -/
/- Theorems to make life easier -/

theorem intMap_sub_dist {n m : SortInt} (le_m_n : m <= n) (pos : 0 <= m) (size : n < UInt256.size) :
  intMap (n - m) = intMap n - intMap m := by
  unfold intMap UInt256.toSigned; split <;> rename_i a b h
  . cases cn : n with
    | ofNat p => cases m with
                | ofNat q =>
                simp_all [Int.ofNat]
                rw [←Int.ofNat_sub, Int.ofNat_inj] at h <;> try assumption
                simp only [←h, HSub.hSub, Sub.sub, UInt256.sub, Fin.sub]
                aesop (add simp [UInt256.ofNat_eq, UInt256.size, Fin.ofNat])
                      (add safe (by omega))
                | negSucc q => aesop
    | negSucc p =>
      have _ : 0 ≤ n := by apply (Int.le_trans pos le_m_n)
      aesop
  . rw [←sub_nonneg, h] at le_m_n; contradiction

theorem intMap_add_dist {n m : SortInt} (nh : 0 ≤ n) (mh : 0 ≤ m) :
  intMap ((n + m) % ↑UInt256.size) = intMap n + intMap m := by
  unfold intMap UInt256.toSigned
  split; rename_i h p mod_eq
  . split <;> split <;> rename_i h' q j l <;> try contradiction
    . simp_all only [Int.ofNat_eq_coe, Int.ofNat_add_ofNat]
      rw [Int.mod_cast, Int.toNat_ofNat, Int.ofNat_inj] at * <;> try simp
      . aesop (add simp [UInt256.ofNat, UInt256.size, Id.run, dbgTrace, Fin.ofNat])
              (add safe (by congr 1))
      . aesop (add safe (by omega))
  . have mod_nonneg: 0 ≤ (n + m) % ↑UInt256.size := by
      rw [Int.mod_def']; apply Int.emod_nonneg; simp [UInt256.size]
    simp_all

theorem intMap_toNat {n : SortInt} (nh : 0 ≤ n) (size : n < UInt256.size) :
  (intMap n).toNat = n.toNat := by
  aesop (add simp [intMap, Int.toNat, UInt256.toSigned, Int.toNat_ofNat, UInt256.ofNat_toNat])

end StateMap
