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

-- This proof could be optimized
theorem intMap_sub_dist (n m : SortInt) (le_m_n : m <= n) (pos : 0 <= m) (size : n < UInt256.size) :
  intMap (n - m) = intMap n - intMap m := by
  simp [intMap, UInt256.toSigned]; split <;> rename_i a b h
  . cases cn : n with
    | ofNat p => cases cm : m with
                | ofNat q =>
                simp_all [Int.ofNat]
                rw [←Int.ofNat_sub, Int.ofNat_inj] at h <;> try assumption
                simp only [←h, HSub.hSub, Sub.sub, UInt256.sub, Fin.sub]
                have size_q : q < UInt256.size := by
                  apply (Nat.lt_of_le_of_lt le_m_n size)
                have p_sub_q : p - q < UInt256.size := by
                  rw [Nat.sub_lt_iff_lt_add] <;> try assumption
                  apply Nat.lt_add_left; assumption
                rw [UInt256.ofNat_eq] <;> try assumption
                have eq : (UInt256.size - q + ↑(UInt256.ofNat p).1) % UInt256.size = ↑(UInt256.ofNat p).1 - q := by
                  rw [←Nat.sub_add_comm] <;> try apply (Nat.le_of_lt size_q)
                  rw [Nat.add_sub_assoc] <;> try rw [UInt256.val_eq] <;> try assumption
                  rw [Nat.add_comm]; simp_arith
                  rw [Nat.mod_eq_iff_lt]; assumption; simp [UInt256.size]
                simp [eq, Fin.ofNat]; rw [Nat.mod_eq]
                simp_all [UInt256.size, le_fls_of_lt, ←h, UInt256.val_eq]
                | negSucc q => simp_all [cm]
    | negSucc p =>
      have _ : 0 ≤ n := by apply (Int.le_trans pos le_m_n)
      simp_all [cn]
  . rw [←sub_nonneg, h] at le_m_n; contradiction

theorem intMap_add_dist (n m : SortInt) (nh : 0 ≤ n) (mh : 0 ≤ m) :
  intMap ((n + m) % ↑UInt256.size) = intMap n + intMap m := by
  simp [intMap, UInt256.toSigned]
  split; rename_i h p mod_eq
  . split <;> split <;> rename_i h' q j l <;> try contradiction
    . revert mod_eq
      simp only [Int.ofNat_eq_coe, Int.ofNat_add_ofNat]
      rw [Int.mod_cast, Int.toNat_ofNat, Int.ofNat_inj] <;> try simp
      . intro mod_eq; subst mod_eq
        simp [UInt256.ofNat, Id.run, dbgTrace]
        congr 1; rw [Fin.add_def]; simp [←Fin.val_add]
        simp [Fin.ofNat, Fin.add_def, UInt256.size]
      . rw [←(Int.zero_add 0)]; apply Int.add_le_add <;> simp
  . have mod_nonneg: 0 ≤ (n + m) % ↑UInt256.size := by
      rw [Int.mod_def']; apply Int.emod_nonneg; simp [UInt256.size]
    simp_all

end StateMap
