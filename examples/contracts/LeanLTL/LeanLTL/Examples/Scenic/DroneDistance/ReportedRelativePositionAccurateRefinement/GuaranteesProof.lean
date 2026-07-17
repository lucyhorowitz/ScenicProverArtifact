import LeanLTL.Examples.Scenic.DroneDistance.ReportedRelativePositionAccurateRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace ReportedRelativePositionAccurateRefinement


theorem imp_guarantees : LLTL[(assumptions ∧ i_guarantees)] ⇒ LLTL[guarantees] := by
  intro t ⟨_, hIG0, hIG1, hIG2, hIG3, hIG4⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [push_ltl] at * <;> intro n hn <;>
    specialize hIG0 n hn <;> specialize hIG1 n hn <;> aesop
