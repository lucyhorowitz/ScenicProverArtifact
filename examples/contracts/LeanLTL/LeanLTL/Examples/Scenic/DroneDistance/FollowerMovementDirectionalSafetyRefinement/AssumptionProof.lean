import LeanLTL.Examples.Scenic.DroneDistance.FollowerMovementDirectionalSafetyRefinement.Lib

open LeanLTL
open scoped LeanLTL.Notation

namespace FollowerMovementDirectionalSafetyRefinement

/- Every internal assumption is a closed rational fact (IA1/IA2 are copies of
   A0/A1; IA0 is a constant inequality), so no trace reasoning is needed. -/
theorem imp_assumptions : LLTL[(assumptions)] ⇒ LLTL[i_assumptions] := by
  intro t _
  simp only [i_assumptions, IA0, IA1, IA2, TraceSet.sat_and_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simp [push_ltl] <;> norm_num
