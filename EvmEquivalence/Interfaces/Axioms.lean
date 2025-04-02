import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.KEVM2Lean.Sorts

open EvmYul

/-
This module contains current axioms used in the equivalence work.
The reason of needing this axioms is to have placeholders for pending work. Such as:
1. Missing implementation of the Lean 4 K-generated code
2. Missing reasoning-suitable interfaces for the EvmYul model
 -/
namespace Axioms

axiom SortAccountsCellMap : SortAccountsCell → AccountMap

axiom SortAccessedStorageCellMap : SortAccessedStorageCell → Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp

axiom SortStorageCellMap : SortStorageCell → Storage

axiom SortTransientStorageCellMap : SortTransientStorageCell → Storage

end Axioms
