-- This module serves as the root of the `EvmEquivalence` library.
-- Import modules here that should be built as part of the library.

-- K generated code
import EvmEquivalence.KEVM2Lean.Prelude
import EvmEquivalence.KEVM2Lean.Sorts
import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.ScheduleOrdering
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.KEVM2Lean.Rewrite

-- Interfaces
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.Tactics
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.Axioms

-- State Map
import EvmEquivalence.StateMap

-- Utils
import EvmEquivalence.Utils.IntUtils

-- Summaries
import EvmEquivalence.Summaries.StopSummary
import EvmEquivalence.Summaries.AddSummary
import EvmEquivalence.Summaries.Push0Summary
import EvmEquivalence.Summaries.SstoreSummary
import EvmEquivalence.Summaries.SloadSummary
import EvmEquivalence.Summaries.MstoreSummary

-- Equivalence
import EvmEquivalence.Equivalence.AddEquivalence
import EvmEquivalence.Equivalence.Push0Equivalence
import EvmEquivalence.Equivalence.SstoreEquivalence
import EvmEquivalence.Equivalence.SloadEquivalence
import EvmEquivalence.Equivalence.MstoreEquivalence
