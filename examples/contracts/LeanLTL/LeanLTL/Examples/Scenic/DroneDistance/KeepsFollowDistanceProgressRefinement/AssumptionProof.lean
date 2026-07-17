import LeanLTL.Examples.Scenic.DroneDistance.KeepsFollowDistanceProgressRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace KeepsFollowDistanceProgressRefinement

/- Every internal assumption is a closed rational fact (IA0/IA1 are copies of
   A0/A1; IA2/IA3 are constant inequalities), so no trace reasoning is needed. -/
theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t _
  simp only [i_assumptions, IA0, IA1, IA2, IA3, TraceSet.sat_and_iff]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [push_ltl] <;> norm_num
